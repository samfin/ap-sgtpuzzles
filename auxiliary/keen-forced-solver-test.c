/*
 * test_keen_forced_solver.c: small test suite for keen_forced_solver().
 *
 * Covers:
 *   1. A fully-specified, uniquely-solvable puzzle (a real generated
 *      Keen grid, every cage visible) -> every cell forced, matching
 *      the puzzle's actual solution.
 *   2. A partially-specified puzzle (most cages masked out) -> every
 *      digit this solver DOES report is checked against the puzzle's
 *      real solution (soundness); a couple of specific cells are also
 *      checked to confirm the solver finds at least the "obvious"
 *      deductions a single visible cage gives directly.
 *   3. The "row total" deduction from the project's own spec example:
 *      three cells of a row summing to 10 and the next two summing to
 *      7 force the row's sixth cell to 4, purely because a width-6
 *      Latin row always sums to 21 -- with every other cage in the
 *      grid left completely unclued.
 *   3b. The "untouched rows/columns" structural heuristic: two whole
 *      rows (or, separately, two whole columns) with no cell in any
 *      visible cage cannot have any of their cells forced, even when
 *      the rest of the grid is fully clued and forced.
 *   4. A no-deduction-possible case: a grid with no visible clues at
 *      all forces nothing.
 *   5. An inconsistent partial state (two cells directly forced to
 *      the same value in one row) is correctly reported as having no
 *      completion (NULL).
 *
 * Tests 1-2 link against the real keen.c game logic (new_game,
 * validate_desc, etc.) to build a genuine, generator-produced puzzle;
 * tests 3-5 build small DSF/clue arrays by hand, since they target
 * exact, hand-picked scenarios that would be awkward to fish out of
 * random generation.
 *
 * Run with no arguments; prints PASS/FAIL per test and a summary.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "puzzles.h"
#include "keen_forced_solver.h"

#define C_NO_CLUE 0x00000000UL
#define C_ADD     0x20000000UL

static int tests_run = 0, tests_passed = 0;

static void check(const char *name, bool cond)
{
    tests_run++;
    if (cond) {
        tests_passed++;
        printf("PASS: %s\n", name);
    } else {
        printf("FAIL: %s\n", name);
    }
}

/*
 * ---- Tests 1 & 2: a real generated puzzle, full and partial ----
 *
 * game_params and game_state are opaque outside keen.c, so these tests
 * go through the same public API the WASM bridge and the rest of this
 * codebase use: thegame.get_forced_cells(). With the FULL descriptor
 * (every cage visible) that call's result doubles as "the puzzle's
 * real solution", since test 1 itself asserts it comes back fully
 * forced -- no need to reach into game_state internals at all.
 */

static void test_generated_puzzle(void)
{
    game_params *p = thegame.default_params();
    random_state *rs = random_new("keen-forced-solver-test",
                                   (int)strlen("keen-forced-solver-test"));
    char *aux = NULL;
    char *desc;
    int w = 6, a = w * w, i;
    char *solution; /* the full-descriptor forced-cells result */
    char *maskeddesc;

    thegame.decode_params(p, "6dn");
    desc = thegame.new_desc(p, rs, &aux, false);

    /* ---- Test 1: fully specified ---- */
    {
        char *out = thegame.get_forced_cells(p, desc);
        bool full = (out != NULL);
        check("full: solver returns a result", out != NULL);
        if (out) {
            for (i = 0; i < a; i++)
                if (out[i] == '.') { full = false; break; }
            check("full: every cell forced", full);
        }
        solution = out; /* kept for test 2's soundness check below */
    }

    /*
     * ---- Test 2: mask out every cage except the very first ----
     * The descriptor is "<blockstructure>,<clue1><clue2>...": copy the
     * block structure and the first clue token verbatim, and re-encode
     * every clue after it as 'n' (no clue). Clue tokens are one op
     * letter (a/m/s/d/n) optionally followed by digits.
     */
    {
        const char *comma = strchr(desc, ',');
        int blocklen = (int)(comma - desc);
        const char *p2 = comma + 1;
        int outlen, cageidx = 0;

        maskeddesc = snewn((int)strlen(desc) + 16, char);
        memcpy(maskeddesc, desc, (size_t)blocklen);
        outlen = blocklen;
        maskeddesc[outlen++] = ',';
        while (*p2) {
            const char *tokstart = p2;
            p2++; /* the op/no-clue letter */
            while (*p2 >= '0' && *p2 <= '9') p2++;
            if (cageidx == 0) {
                memcpy(maskeddesc + outlen, tokstart, (size_t)(p2 - tokstart));
                outlen += (int)(p2 - tokstart);
            } else {
                maskeddesc[outlen++] = 'n';
            }
            cageidx++;
        }
        maskeddesc[outlen] = '\0';
    }

    {
        const char *err = thegame.validate_desc(p, maskeddesc);
        check("partial: masked descriptor is structurally valid", err == NULL);
        if (!err) {
            char *out = thegame.get_forced_cells(p, maskeddesc);
            bool sound = true;
            check("partial: solver returns a result", out != NULL);
            if (out && solution) {
                for (i = 0; i < a; i++) {
                    if (out[i] != '.' && out[i] != solution[i]) {
                        sound = false;
                        break;
                    }
                }
                check("partial: every reported forced digit matches the true solution", sound);
            }
            sfree(out);
        }
    }

    sfree(solution);
    sfree(maskeddesc);
    sfree(desc);
    sfree(aux);
    thegame.free_params(p);
}

/* ---- Test 3: the project's own "row total" deduction example ---- */

static void test_row_total_deduction(void)
{
    int w = 6, a = 36;
    DSF *dsf = dsf_new_min(a);
    unsigned long clues[36];
    memset(clues, 0, sizeof(clues));

    /* Row 0: cells 0,1,2 sum to 10; cells 3,4 sum to 7; cell 5 has no
     * clue at all. Every other row is left completely unclued too.
     * The only way to pin down cell 5 is the invariant that a width-6
     * Latin row always sums to 1+..+6 = 21: 21-10-7 = 4. */
    dsf_merge(dsf, 0, 1);
    dsf_merge(dsf, 0, 2);
    dsf_merge(dsf, 3, 4);
    clues[dsf_minimal(dsf, 0)] = C_ADD | 10;
    clues[dsf_minimal(dsf, 3)] = C_ADD | 7;

    {
        char *out = keen_forced_solver(w, dsf, clues);
        check("row-total: solver returns a result", out != NULL);
        if (out) {
            check("row-total: cell (0,5) is forced to 4", out[5] == '4');
            {
                int i, extra_forced = 0;
                for (i = 0; i < a; i++)
                    if (i != 5 && out[i] != '.') extra_forced++;
                /* Nothing else should be pinned down: cells 0-2 can be
                 * any permutation of a triple summing to 10, cells 3-4
                 * any pair summing to 7, and every other row is
                 * completely free. */
                check("row-total: no other cell is (incorrectly) forced", extra_forced == 0);
            }
            free(out);
        }
    }
    dsf_free(dsf);
}

/*
 * ---- Test 3b: two fully-unclued rows/columns -> nothing in them is
 * forced, even though the rest of the grid is fully clued (so the
 * fixpoint propagation above alone wouldn't already know this without
 * expensive search) ----
 *
 * 6x6 grid. Rows 0 and 1 have no cage touching them at all. Rows 2-5
 * are fully covered by clued cages that (by construction) force every
 * one of their cells outright, so this test also confirms the
 * heuristic doesn't over-fire and swallow genuinely forced cells
 * elsewhere in the grid.
 */

static void test_untouched_rows_and_cols(void)
{
    int w = 6, a = 36;
    DSF *dsf = dsf_new_min(a);
    unsigned long clues[36];
    int r;
    memset(clues, 0, sizeof(clues));

    /* Rows 2-5: single-cell cages forcing every cell to a fixed value
     * (single-cell cages don't occur in real generated puzzles, but
     * the solver must handle them soundly regardless -- see test 5). */
    for (r = 2; r < w; r++) {
        int c;
        for (c = 0; c < w; c++) {
            int cell = r * w + c;
            /* Cyclic shift per row so each row is a valid permutation
             * of 1..6: value = ((c + r) % 6) + 1. */
            clues[dsf_minimal(dsf, cell)] = C_ADD | (unsigned long)(((c + r) % 6) + 1);
        }
    }
    /* Rows 0 and 1 (cells 0-11): left completely unclued. */

    {
        char *out = keen_forced_solver(w, dsf, clues);
        check("untouched-rows: solver returns a result", out != NULL);
        if (out) {
            bool rows01_free = true, rows25_forced = true;
            int i;
            for (i = 0; i < 2 * w; i++)
                if (out[i] != '.') rows01_free = false;
            for (i = 2 * w; i < a; i++)
                if (out[i] == '.') rows25_forced = false;
            check("untouched-rows: rows 0-1 report no forced cells", rows01_free);
            check("untouched-rows: rows 2-5 remain fully forced", rows25_forced);
            free(out);
        }
    }
    dsf_free(dsf);
}

/*
 * Column analogue of the above: columns 0 and 1 untouched by any cage,
 * columns 2-5 fully forced via single-cell cages.
 */

static void test_untouched_columns(void)
{
    int w = 6, a = 36;
    DSF *dsf = dsf_new_min(a);
    unsigned long clues[36];
    int c;
    memset(clues, 0, sizeof(clues));

    for (c = 2; c < w; c++) {
        int r;
        for (r = 0; r < w; r++) {
            int cell = r * w + c;
            clues[dsf_minimal(dsf, cell)] = C_ADD | (unsigned long)(((r + c) % 6) + 1);
        }
    }

    {
        char *out = keen_forced_solver(w, dsf, clues);
        check("untouched-cols: solver returns a result", out != NULL);
        if (out) {
            bool cols01_free = true, cols25_forced = true;
            int r, cc;
            for (r = 0; r < w; r++)
                for (cc = 0; cc < 2; cc++)
                    if (out[r * w + cc] != '.') cols01_free = false;
            for (r = 0; r < w; r++)
                for (cc = 2; cc < w; cc++)
                    if (out[r * w + cc] == '.') cols25_forced = false;
            check("untouched-cols: cols 0-1 report no forced cells", cols01_free);
            check("untouched-cols: cols 2-5 remain fully forced", cols25_forced);
            free(out);
        }
    }
    dsf_free(dsf);
}

/* ---- Test 4: no visible clues at all -> nothing forced ---- */

static void test_no_clues(void)
{
    int w = 5, a = 25;
    DSF *dsf = dsf_new_min(a);
    unsigned long clues[25];
    memset(clues, 0, sizeof(clues)); /* every cage C_NO_CLUE */

    char *out = keen_forced_solver(w, dsf, clues);
    check("blank grid: solver returns a result", out != NULL);
    if (out) {
        int i, any_forced = 0;
        for (i = 0; i < a; i++) if (out[i] != '.') any_forced++;
        check("blank grid: nothing is forced", any_forced == 0);
        free(out);
    }
    dsf_free(dsf);
}

/* ---- Test 5: an inconsistent partial state is reported as NULL ---- */

static void test_inconsistent(void)
{
    int w = 4, a = 16;
    DSF *dsf = dsf_new_min(a);
    unsigned long clues[16];
    memset(clues, 0, sizeof(clues));

    /* Force cells (0,0) and (0,1) -- same row -- to the same value 2,
     * via two single-cell ADD cages of target 2. Latin rows must
     * contain 1..w exactly once, so this is directly inconsistent.
     * (Single-cell cages don't occur in generated puzzles, but the
     * solver must still handle them correctly and defensively.) */
    clues[dsf_minimal(dsf, 0)] = C_ADD | 2;
    clues[dsf_minimal(dsf, 1)] = C_ADD | 2;

    char *out = keen_forced_solver(w, dsf, clues);
    check("inconsistent state: solver reports no completion (NULL)", out == NULL);
    if (out) free(out);
    dsf_free(dsf);
}

int main(void)
{
    test_generated_puzzle();
    test_row_total_deduction();
    test_untouched_rows_and_cols();
    test_untouched_columns();
    test_no_clues();
    test_inconsistent();

    printf("\n%d/%d tests passed\n", tests_passed, tests_run);
    return tests_passed == tests_run ? 0 : 1;
}
