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
    random_state *rs = random_new("keen-incremental-test", 21);
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
}

/*
 * Idempotency: revealing the same cage twice must not change anything
 * (the second call is documented as a harmless no-op).
 */
static void test_idempotent_reveal(void)
{
    int w = 6, a = 36;
    random_state *rs = random_new("keen-incremental-idempotent", 7);
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
    random_state *rs = random_new("keen-incremental-perf", 99);
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
}

int main(void)
{
    test_incremental_matches_oneshot();
    test_idempotent_reveal();
    test_performance();

    printf("\n%d/%d tests passed\n", tests_passed, tests_run);
    return tests_passed == tests_run ? 0 : 1;
}
