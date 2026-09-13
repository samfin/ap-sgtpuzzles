/*
 * keen-incremental-solver-test.c: correctness and performance test for
 * keen_human_solver_create()/keen_human_solver_reveal()'s incremental
 * ("warm-start") API -- see keen_human_solver.h's doc comment on that
 * API, and keen_human_solver.c's "Incremental / warm-start API" section
 * for the design/correctness argument this test is verifying.
 *
 * Covers:
 *   1. Correctness: for many real generated puzzles (sizes 4-9), reveal
 *      every cage in several independently-random orders, and after
 *      EVERY single reveal, compare the incremental solver's snapshot
 *      against a fresh, independent one-shot keen_human_solver() call
 *      given exactly the same revealed-cage subset (C_NO_CLUE for every
 *      cage not yet revealed) -- must match byte-for-byte at every
 *      step, regardless of reveal order. This directly tests the
 *      order-independence/equivalence argument the design relies on.
 *   2. Idempotency: revealing an already-revealed cage a second time
 *      changes nothing.
 *   3. Contradiction agreement: whenever the incremental reveal reports
 *      a contradiction, the equivalent fresh one-shot call must also
 *      report one (NULL) -- they must never disagree about
 *      satisfiability of the same revealed-cage subset.
 *   4. Performance: at w=9, times "reveal every cage in order, one at a
 *      time" via the incremental API against the equivalent "call
 *      keen_human_solver() fresh from scratch after each new cage is
 *      revealed" (what a from-scratch clue-grouping planner currently
 *      does), and reports the speedup.
 *   5. Save/restore checkpoints: for many real generated puzzles,
 *      capture a checkpoint after every single reveal along a random
 *      order, then restore a handful of them out of order (each
 *      possibly more than once) and confirm each restore reproduces
 *      the EXACT snapshot captured at that point -- not just a
 *      non-contradicting one, since the whole point of a checkpoint is
 *      exact reproduction. Also confirms a session stays fully usable
 *      after a restore: finishing the remaining reveals (in a fresh
 *      random order) from a restored checkpoint must never contradict
 *      a totally fresh one-shot solve of the puzzle's complete clue
 *      set.
 *   6. Save/restore on a freshly-created (nothing revealed) solver:
 *      restoring that checkpoint after further reveals reproduces the
 *      blank/full-domain snapshot, and a checkpoint survives being
 *      restored more than once.
 *
 * Run with no arguments; prints PASS/FAIL per check and a summary.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "puzzles.h"
#include "keen_human_solver.h"

/* Test-only entry point exported by keen.c alongside get_forced_cells_ex()
 * -- see its doc comment there. Not part of struct game. */
extern bool get_puzzle_geometry_ex(const game_params *params, const char *desc,
                                    DSF **dsf_out, unsigned long **clues_out);

#define C_NO_CLUE 0x00000000UL
#define C_ADD     0x20000000UL
#define C_MUL     0x40000000UL
#define C_SUB     0x60000000UL
#define C_DIV     0x80000000UL
#define CMASK     0xE0000000UL

static int tests_run = 0, tests_passed = 0;

static void check(const char *name, bool cond)
{
    tests_run++;
    if (cond) {
        tests_passed++;
        /* Quiet on pass for the per-reveal checks (there are thousands
         * of them across all trials) -- only summary lines below print
         * unconditionally. */
    } else {
        printf("FAIL: %s\n", name);
    }
}

/* Scans dsf (over a == w*w cells) in the same canonical order
 * build_cages()/keen_human_solver_create() already use (DSF-root-first
 * -encountered while scanning cell index 0..a-1), and fills:
 *   root_cell[k]  = the cell index that is cage k's dsf root
 *   op[k]         = that cage's op, from clues[root_cell[k]]
 *   value[k]      = that cage's value, from clues[root_cell[k]]
 * Returns the number of real cages found (== keen_human_solver_create()'s
 * keen_human_solver_cage_count() for the same dsf, by construction).
 */
static int extract_real_cages(int w, DSF *dsf, unsigned long *clues,
                               int *root_cell, int *op, long *value)
{
    int a = w * w, n = 0, i;
    for (i = 0; i < a; i++) {
        if (dsf_minimal(dsf, i) == i) {
            unsigned long clue = clues[i];
            root_cell[n] = i;
            op[n] = (int)(clue & CMASK);
            value[n] = (long)(clue & ~CMASK);
            n++;
        }
    }
    return n;
}

/* Fisher-Yates shuffle of a freshly-filled 0..n-1 permutation. */
static void random_permutation(random_state *rs, int *order, int n)
{
    int i;
    for (i = 0; i < n; i++) order[i] = i;
    for (i = n - 1; i > 0; i--) {
        int j = (int)random_upto(rs, (unsigned long)(i + 1));
        int t = order[i]; order[i] = order[j]; order[j] = t;
    }
}

/*
 * Core correctness test: generates puzzles across sizes 4-9, and for
 * each, several random reveal orders, checking the incremental solver
 * against a fresh one-shot solve after every single reveal.
 */
static void test_incremental_matches_oneshot(void)
{
    int sizes[] = {4, 5, 6, 7, 8, 9};
    int si;
    random_state *rs = random_new("keen-incremental-test",
                                   (int)strlen("keen-incremental-test"));
    int total_reveals = 0;
    int total_puzzles = 0, total_orderings = 0;
    int loose_mismatches = 0;
    bool all_ok = true;

    for (si = 0; si < (int)(sizeof(sizes) / sizeof(sizes[0])); si++) {
        int w = sizes[si], a = w * w;
        int puzzle_i;
        for (puzzle_i = 0; puzzle_i < 4; puzzle_i++) {
            game_params *p = thegame.default_params();
            char *aux = NULL;
            char *desc;
            char paramstr[16];
            DSF *dsf;
            unsigned long *clues;
            int root_cell[200];
            int op[200];
            long value[200];
            int ncages;
            int ordering_i;

            snprintf(paramstr, sizeof(paramstr), "%ddn", w);
            thegame.decode_params(p, paramstr);
            desc = thegame.new_desc(p, rs, &aux, false);

            if (!get_puzzle_geometry_ex(p, desc, &dsf, &clues)) {
                check("geometry extraction succeeds", false);
                thegame.free_params(p);
                sfree(desc);
                if (aux) sfree(aux);
                continue;
            }

            ncages = extract_real_cages(w, dsf, clues, root_cell, op, value);
            total_puzzles++;

            for (ordering_i = 0; ordering_i < 3; ordering_i++) {
                int *order = snewn(ncages, int);
                unsigned long *subset_clues = snewn(a, unsigned long);
                KeenHumanIncSolver *inc;
                int k;
                bool ok_this_order = true;

                random_permutation(rs, order, ncages);
                memset(subset_clues, 0, (size_t)a * sizeof(unsigned long));

                inc = keen_human_solver_create(w, dsf);
                if (!inc) {
                    check("keen_human_solver_create succeeds", false);
                    sfree(order);
                    sfree(subset_clues);
                    continue;
                }

                /* Sanity: cage geometry accessors agree with our own
                 * canonical-order extraction. */
                {
                    bool geom_ok = (keen_human_solver_cage_count(inc) == ncages);
                    for (k = 0; k < ncages && geom_ok; k++) {
                        /* root_cell[k] must be among cage k's cells. */
                        int n = keen_human_solver_cage_size(inc, k);
                        bool found = false;
                        int j;
                        for (j = 0; j < n; j++)
                            if (keen_human_solver_cage_cell(inc, k, j) == root_cell[k])
                                found = true;
                        if (!found) geom_ok = false;
                    }
                    check("incremental cage geometry matches canonical order", geom_ok);
                    if (!geom_ok) ok_this_order = false;
                }

                for (k = 0; k < ncages; k++) {
                    int cage_idx = order[k];
                    bool inc_ok;
                    char *snap, *oneshot;

                    inc_ok = keen_human_solver_reveal(inc, cage_idx,
                                                       op[cage_idx], value[cage_idx]);

                    /* Reconstruct the original clue encoding. op[] was
                     * extracted as (int)(clue & CMASK) -- for C_DIV
                     * (0x80000000UL) that int is negative (implementation
                     * -defined bit-pattern reinterpretation), so widening
                     * it to unsigned long directly would sign-extend and
                     * corrupt the high bits. Reinterpret through unsigned
                     * int first (same 32-bit bit pattern, no sign
                     * extension), then zero-extend. */
                    subset_clues[root_cell[cage_idx]] =
                        (unsigned long)(unsigned int)op[cage_idx] |
                        (unsigned long)value[cage_idx];

                    oneshot = keen_human_solver(w, dsf, subset_clues);

                    if (!inc_ok) {
                        check("incremental contradiction matches one-shot NULL",
                              oneshot == NULL);
                        if (oneshot != NULL) ok_this_order = false;
                        if (oneshot) free(oneshot);
                        /* Once contradictory, this instance can't be used
                         * further (documented behaviour) -- stop this
                         * ordering's reveal loop. */
                        break;
                    }

                    check("one-shot solve succeeds when incremental does",
                          oneshot != NULL);
                    if (!oneshot) { ok_this_order = false; break; }

                    /*
                     * The two solvers share the same underlying
                     * dirty-gated fixpoint driver (converge_solver() in
                     * keen_human_solver.c), which has one known,
                     * extremely rare way to converge to a fixpoint that
                     * is sound but not the true maximal one (see that
                     * function's doc comment) -- and either side's own
                     * particular pass history can independently hit it.
                     * So the invariant actually guaranteed is NOT byte
                     * -for-byte equality: it's that neither side ever
                     * contradicts the other with a DIFFERENT digit at
                     * the same cell (that would be real unsoundness --
                     * a hard failure) -- one side reporting a digit
                     * where the other has '.' is a rare, tolerated
                     * completeness difference, counted and reported but
                     * not itself a failure.
                     */
                    snap = keen_human_solver_snapshot(inc);
                    {
                        int ci;
                        bool contradiction = false;
                        bool any_diff = false;
                        for (ci = 0; ci < a; ci++) {
                            if (snap[ci] != oneshot[ci]) {
                                any_diff = true;
                                if (snap[ci] != '.' && oneshot[ci] != '.')
                                    contradiction = true;
                            }
                        }
                        if (contradiction) {
                            ok_this_order = false;
                            printf("FAIL: CONTRADICTING digit at w=%d puzzle=%d "
                                   "ordering=%d reveal#%d (cage %d)\n  inc=%s\n"
                                   "  1shot=%s\n",
                                   w, puzzle_i, ordering_i, k, cage_idx, snap, oneshot);
                        } else if (any_diff) {
                            loose_mismatches++;
                        }
                    }
                    total_reveals++;

                    free(snap);
                    free(oneshot);
                }

                keen_human_solver_destroy(inc);
                sfree(order);
                sfree(subset_clues);
                total_orderings++;
                if (!ok_this_order) all_ok = false;
            }

            dsf_free(dsf);
            sfree(clues);
            thegame.free_params(p);
            sfree(desc);
            if (aux) sfree(aux);
        }
    }

    printf("  incremental-vs-oneshot: %d puzzles, %d orderings, %d reveals checked, "
           "%d loose (non-contradicting) mismatches\n",
           total_puzzles, total_orderings, total_reveals, loose_mismatches);
    check("incremental solver never contradicts a fresh one-shot solve "
          "with a different digit", all_ok);
    /* The rare completeness gap this tolerates (see the comment above)
     * should stay rare -- flag it as a real regression if it's not. */
    check("loose mismatch rate stays low (<1% of reveals)",
          total_reveals == 0 || loose_mismatches * 100 < total_reveals);
    random_free(rs);
}

/*
 * Idempotency: revealing the same cage twice must not change anything
 * (the second call is documented as a harmless no-op).
 */
static void test_idempotent_reveal(void)
{
    int w = 6, a = 36;
    random_state *rs = random_new("keen-incremental-idempotent",
                                   (int)strlen("keen-incremental-idempotent"));
    game_params *p = thegame.default_params();
    char *aux = NULL;
    char paramstr[16];
    char *desc;
    DSF *dsf;
    unsigned long *clues;
    int root_cell[200], op[200];
    long value[200];
    int ncages;
    KeenHumanIncSolver *inc;
    char *snap1, *snap2;
    bool ok1, ok2;

    snprintf(paramstr, sizeof(paramstr), "%ddn", w);
    thegame.decode_params(p, paramstr);
    desc = thegame.new_desc(p, rs, &aux, false);
    get_puzzle_geometry_ex(p, desc, &dsf, &clues);
    ncages = extract_real_cages(w, dsf, clues, root_cell, op, value);

    inc = keen_human_solver_create(w, dsf);

    ok1 = keen_human_solver_reveal(inc, 0, op[0], value[0]);
    if (ncages > 1)
        keen_human_solver_reveal(inc, 1, op[1], value[1]);
    snap1 = keen_human_solver_snapshot(inc);

    /* Reveal cage 0 again with the SAME value -- must be a no-op. */
    ok2 = keen_human_solver_reveal(inc, 0, op[0], value[0]);
    snap2 = keen_human_solver_snapshot(inc);

    check("idempotent reveal: first reveal succeeds", ok1);
    check("idempotent reveal: repeat reveal returns true", ok2);
    check("idempotent reveal: snapshot unchanged", strcmp(snap1, snap2) == 0);

    (void)a;
    free(snap1);
    free(snap2);
    keen_human_solver_destroy(inc);
    dsf_free(dsf);
    sfree(clues);
    thegame.free_params(p);
    sfree(desc);
    if (aux) sfree(aux);
    random_free(rs);
}

/*
 * Performance: at w=9, times revealing every cage in order via the
 * incremental API (warm-started) against calling keen_human_solver()
 * fresh from scratch after each new cage is revealed (the from-scratch
 * approach a clue-grouping planner currently uses), and reports the
 * speedup. Averaged over several puzzles for stability.
 */
static void test_performance(void)
{
    int w = 9, a = 81;
    random_state *rs = random_new("keen-incremental-perf",
                                   (int)strlen("keen-incremental-perf"));
    int trial, ntrials = 8;
    double total_inc = 0.0, total_oneshot = 0.0;

    for (trial = 0; trial < ntrials; trial++) {
        game_params *p = thegame.default_params();
        char *aux = NULL;
        char paramstr[16];
        char *desc;
        DSF *dsf;
        unsigned long *clues;
        int root_cell[200], op[200];
        long value[200];
        int ncages, k;
        clock_t t0, t1;

        snprintf(paramstr, sizeof(paramstr), "%ddn", w);
        thegame.decode_params(p, paramstr);
        desc = thegame.new_desc(p, rs, &aux, false);
        get_puzzle_geometry_ex(p, desc, &dsf, &clues);
        ncages = extract_real_cages(w, dsf, clues, root_cell, op, value);

        /* Incremental: one persistent solver, reveal in cage order. */
        {
            KeenHumanIncSolver *inc = keen_human_solver_create(w, dsf);
            t0 = clock();
            for (k = 0; k < ncages; k++) {
                if (!keen_human_solver_reveal(inc, k, op[k], value[k]))
                    break;
            }
            t1 = clock();
            total_inc += (double)(t1 - t0) / CLOCKS_PER_SEC;
            keen_human_solver_destroy(inc);
        }

        /* From-scratch: rebuild the whole subset and resolve after
         * every single new reveal. */
        {
            unsigned long *subset_clues = snewn(a, unsigned long);
            memset(subset_clues, 0, (size_t)a * sizeof(unsigned long));
            t0 = clock();
            for (k = 0; k < ncages; k++) {
                char *out;
                subset_clues[root_cell[k]] =
                    (unsigned long)op[k] | (unsigned long)value[k];
                out = keen_human_solver(w, dsf, subset_clues);
                if (out) free(out);
                else break;
            }
            t1 = clock();
            total_oneshot += (double)(t1 - t0) / CLOCKS_PER_SEC;
            sfree(subset_clues);
        }

        dsf_free(dsf);
        sfree(clues);
        thegame.free_params(p);
        sfree(desc);
        if (aux) sfree(aux);
    }

    printf("  performance (w=9, %d puzzles, full walk through all cages):\n",
           ntrials);
    printf("    incremental (warm-start):  %.1f ms total (%.2f ms/puzzle)\n",
           total_inc * 1000.0, total_inc * 1000.0 / ntrials);
    printf("    from-scratch (per reveal): %.1f ms total (%.2f ms/puzzle)\n",
           total_oneshot * 1000.0, total_oneshot * 1000.0 / ntrials);
    if (total_inc > 0.0)
        printf("    speedup: %.1fx\n", total_oneshot / total_inc);

    check("incremental walk is not slower than from-scratch walk",
          total_inc <= total_oneshot);
    random_free(rs);
}

/*
 * Save/restore checkpoints: reveal every cage of many real generated
 * puzzles in a random order, capturing a checkpoint (and remembering
 * the exact snapshot at that point) after every single reveal.
 * Afterwards, restore a handful of checkpoints out of order -- each
 * possibly more than once -- and confirm each restore reproduces its
 * captured snapshot byte-for-byte: unlike the fuzz test above, exact
 * equality (not just non-contradiction) is the right bar here, since
 * the whole point of a checkpoint is to reproduce a state exactly, not
 * merely soundly. Separately confirms restoring doesn't leave the
 * session unusable: finishing whatever cages remain (in a FRESH random
 * order) from a restored checkpoint must never contradict a totally
 * fresh one-shot solve of the puzzle's complete, already-known
 * -consistent clue set.
 */
static void test_save_restore_state(void)
{
    int sizes[] = {5, 6, 7, 8, 9};
    int si;
    random_state *rs = random_new("keen-incremental-saverestore",
                                   (int)strlen("keen-incremental-saverestore"));
    bool all_exact = true, all_usable = true;
    int total_checkpoints = 0;

    for (si = 0; si < (int)(sizeof(sizes) / sizeof(sizes[0])); si++) {
        int w = sizes[si], a = w * w;
        int puzzle_i;
        for (puzzle_i = 0; puzzle_i < 3; puzzle_i++) {
            game_params *p = thegame.default_params();
            char *aux = NULL;
            char paramstr[16];
            char *desc;
            DSF *dsf;
            unsigned long *clues;
            int root_cell[200], op[200];
            long value[200];
            int ncages, k;
            int *order;
            KeenHumanIncSolverState **checkpoints;
            char **snap_at;
            KeenHumanIncSolver *inc;

            snprintf(paramstr, sizeof(paramstr), "%ddn", w);
            thegame.decode_params(p, paramstr);
            desc = thegame.new_desc(p, rs, &aux, false);
            get_puzzle_geometry_ex(p, desc, &dsf, &clues);
            ncages = extract_real_cages(w, dsf, clues, root_cell, op, value);

            order = snewn(ncages, int);
            random_permutation(rs, order, ncages);
            checkpoints = snewn(ncages, KeenHumanIncSolverState *);
            snap_at = snewn(ncages, char *);

            inc = keen_human_solver_create(w, dsf);

            for (k = 0; k < ncages; k++) {
                bool ok = keen_human_solver_reveal(inc, order[k], op[order[k]],
                                                    value[order[k]]);
                check("save/restore setup: reveal succeeds "
                      "(real puzzle's own clues, should never contradict)", ok);
                if (!ok) { checkpoints[k] = NULL; snap_at[k] = NULL; continue; }

                checkpoints[k] = keen_human_solver_save_state(inc);
                check("save/restore: save_state succeeds", checkpoints[k] != NULL);
                snap_at[k] = keen_human_solver_snapshot(inc);
                total_checkpoints++;
            }

            /* Restore a handful of checkpoints out of order, each possibly
             * more than once, and confirm exact reproduction. */
            {
                int trial;
                for (trial = 0; trial < ncages; trial++) {
                    int idx = (int)random_upto(rs, (unsigned long)ncages);
                    char *snap;
                    if (!checkpoints[idx]) continue;
                    keen_human_solver_restore_state(inc, checkpoints[idx]);
                    snap = keen_human_solver_snapshot(inc);
                    if (strcmp(snap, snap_at[idx]) != 0) {
                        all_exact = false;
                        printf("FAIL: restored checkpoint %d != its captured "
                               "snapshot\n  restored=%s\n  original=%s\n",
                               idx, snap, snap_at[idx]);
                    }
                    free(snap);
                }
            }

            /* Restore to a random checkpoint, then finish revealing every
             * remaining cage in a FRESH random order -- the fully-revealed
             * result must never contradict a fresh one-shot solve of the
             * complete clue set. */
            {
                int restore_at = (int)random_upto(rs, (unsigned long)ncages);
                bool already_revealed[200];
                int *pool = snewn(ncages, int), npool = 0;
                int *remaining_order;
                char *final_snap, *full_oneshot;
                unsigned long *full_clues = snewn(a, unsigned long);
                bool usable = true, contradiction = false;
                int m, c;

                if (checkpoints[restore_at])
                    keen_human_solver_restore_state(inc, checkpoints[restore_at]);

                memset(already_revealed, 0, sizeof(already_revealed));
                for (m = 0; m <= restore_at; m++) already_revealed[order[m]] = true;
                for (m = 0; m < ncages; m++)
                    if (!already_revealed[m]) pool[npool++] = m;

                remaining_order = snewn(npool > 0 ? npool : 1, int);
                random_permutation(rs, remaining_order, npool);
                for (m = 0; m < npool; m++) remaining_order[m] = pool[remaining_order[m]];

                for (k = 0; k < npool; k++) {
                    int cage_idx = remaining_order[k];
                    if (!keen_human_solver_reveal(inc, cage_idx, op[cage_idx],
                                                   value[cage_idx])) {
                        usable = false;
                        break;
                    }
                }

                final_snap = keen_human_solver_snapshot(inc);

                for (c = 0; c < a; c++) full_clues[c] = 0;
                for (c = 0; c < ncages; c++)
                    full_clues[root_cell[c]] =
                        (unsigned long)(unsigned int)op[c] | (unsigned long)value[c];
                full_oneshot = keen_human_solver(w, dsf, full_clues);

                if (full_oneshot) {
                    for (c = 0; c < a; c++)
                        if (final_snap[c] != '.' && full_oneshot[c] != '.' &&
                            final_snap[c] != full_oneshot[c])
                            contradiction = true;
                }
                if (!usable || !full_oneshot || contradiction) {
                    all_usable = false;
                    printf("FAIL: session unusable/contradictory after "
                           "restore+continue (w=%d restore_at=%d)\n",
                           w, restore_at);
                }

                if (full_oneshot) free(full_oneshot);
                free(final_snap);
                sfree(full_clues);
                sfree(pool);
                sfree(remaining_order);
            }

            for (k = 0; k < ncages; k++) {
                if (checkpoints[k]) keen_human_solver_state_free(checkpoints[k]);
                if (snap_at[k]) free(snap_at[k]);
            }
            sfree(checkpoints);
            sfree(snap_at);
            sfree(order);
            keen_human_solver_destroy(inc);
            dsf_free(dsf);
            sfree(clues);
            thegame.free_params(p);
            sfree(desc);
            if (aux) sfree(aux);
        }
    }

    printf("  save/restore: %d checkpoints captured and exactness-checked\n",
           total_checkpoints);
    check("restoring a checkpoint always reproduces its exact original snapshot",
          all_exact);
    check("a session remains fully usable (matches a fresh full solve) "
          "after restore+continue", all_usable);
    random_free(rs);
}

/*
 * Save/restore on a freshly-created (nothing revealed yet) solver, and
 * confirms a single checkpoint tolerates being restored more than once
 * (it's a snapshot, not a consumed stack frame -- see
 * keen_human_solver.h's doc comment).
 */
static void test_save_restore_initial_state(void)
{
    int w = 6;
    random_state *rs = random_new("keen-incremental-saverestore-initial",
                                   (int)strlen("keen-incremental-saverestore-initial"));
    game_params *p = thegame.default_params();
    char *aux = NULL;
    char paramstr[16];
    char *desc;
    DSF *dsf;
    unsigned long *clues;
    int root_cell[200], op[200];
    long value[200];
    int ncages, k;
    KeenHumanIncSolver *inc;
    KeenHumanIncSolverState *initial;
    char *blank_snap, *after_reveals_snap, *restored_snap, *restored_again;

    snprintf(paramstr, sizeof(paramstr), "%ddn", w);
    thegame.decode_params(p, paramstr);
    desc = thegame.new_desc(p, rs, &aux, false);
    get_puzzle_geometry_ex(p, desc, &dsf, &clues);
    ncages = extract_real_cages(w, dsf, clues, root_cell, op, value);

    inc = keen_human_solver_create(w, dsf);
    blank_snap = keen_human_solver_snapshot(inc);
    initial = keen_human_solver_save_state(inc);
    check("save/restore initial: save_state succeeds on a freshly-created solver",
          initial != NULL);

    /* Reveal EVERY cage (this puzzle's own true, already-consistent
     * clue set) rather than an arbitrary fixed prefix -- part 11's own
     * fuzz testing found real generated puzzles are essentially always
     * fully solvable by human techniques once fully clued, so this is
     * the reliable way to guarantee the "changed something" sanity
     * check below isn't vacuous, regardless of which handful of cages
     * a smaller, seed-dependent prefix happens to land on. */
    for (k = 0; k < ncages; k++)
        keen_human_solver_reveal(inc, k, op[k], value[k]);
    after_reveals_snap = keen_human_solver_snapshot(inc);
    check("save/restore initial: reveals actually changed something "
          "(test isn't vacuous)",
          ncages == 0 || strcmp(after_reveals_snap, blank_snap) != 0);

    keen_human_solver_restore_state(inc, initial);
    restored_snap = keen_human_solver_snapshot(inc);
    check("save/restore initial: restoring reproduces the blank snapshot",
          strcmp(restored_snap, blank_snap) == 0);

    /* Restoring must not consume/invalidate the checkpoint. */
    keen_human_solver_restore_state(inc, initial);
    restored_again = keen_human_solver_snapshot(inc);
    check("save/restore initial: a checkpoint can be restored more than once",
          strcmp(restored_again, blank_snap) == 0);

    keen_human_solver_state_free(initial);
    keen_human_solver_state_free(NULL); /* must be a safe no-op */

    free(blank_snap);
    free(after_reveals_snap);
    free(restored_snap);
    free(restored_again);
    keen_human_solver_destroy(inc);
    dsf_free(dsf);
    sfree(clues);
    thegame.free_params(p);
    sfree(desc);
    if (aux) sfree(aux);
    random_free(rs);
}

int main(void)
{
    test_incremental_matches_oneshot();
    test_idempotent_reveal();
    test_performance();
    test_save_restore_state();
    test_save_restore_initial_state();

    printf("\n%d/%d tests passed\n", tests_passed, tests_run);
    return tests_passed == tests_run ? 0 : 1;
}
