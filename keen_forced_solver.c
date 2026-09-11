/*
 * keen_forced_solver.c: fast specialized solver for determining which
 * cells of a partially-clued Keen puzzle are uniquely forced.
 *
 * See keen_forced_solver.h for the exact semantics.
 *
 * -------------------------------------------------------------------
 * Design
 * -------------------------------------------------------------------
 *
 * Cells hold a bitmask domain (bit d set <=> value d is still possible,
 * for d in 1..w). Three kinds of constraints feed propagation:
 *
 *   - Row / column Latin-square constraints (all-different).
 *   - Cage arithmetic constraints (+ - * /), for cages whose clue is
 *     visible (op != C_NO_CLUE). A masked-out cage (op == C_NO_CLUE)
 *     contributes nothing beyond the Latin-square constraints on its
 *     cells, by construction.
 *   - Synthetic "residual sum" cages: every row and every column of a
 *     completed Keen grid sums to the fixed constant w*(w+1)/2 (it is
 *     always some permutation of 1..w). So, for a row, if some of its
 *     cells are exactly covered by one or more fully-row-contained
 *     visible addition cages, the *rest* of the row's cells must sum
 *     to (w*(w+1)/2 - sum of those cages' targets) -- a real, always-
 *     true arithmetic constraint, not a guess. This is folded in as
 *     just another addition-type cage over the leftover cells, reusing
 *     the exact same propagation machinery as real cages. It is what
 *     lets a case like "first three cells of a row sum to 10, next two
 *     sum to 7" directly force the row's last cell to 4 by
 *     propagation alone, without needing to fall back to search.
 *
 * Propagation is a fixpoint loop over dirty rows, columns and cages,
 * each revised in turn until nothing changes:
 *
 *   - Revising a row/column removes, from every other cell in that
 *     unit, any value that is a "naked single" elsewhere in the unit,
 *     and assigns a "hidden single" (a value with exactly one possible
 *     cell left in the unit) to that cell.
 *   - Revising a cage recomputes, by bounded search over the current
 *     domains (pruned hard by the arithmetic target/op as it goes),
 *     which (cell, value) pairs still have *some* supporting complete
 *     assignment of the cage that also respects same-row/same-column
 *     distinctness among the cage's own cells. Any (cell, value) with
 *     no support is removed from that cell's domain.
 *
 * Whenever a domain shrinks, the owning row, column and cage(s) --
 * a cell can be relevant to more than one cage once residual cages are
 * folded in -- are marked dirty again. If a domain hits size 1 that is
 * an assignment; size 0 means the current (possibly speculative)
 * partial assignment is inconsistent.
 *
 * All of the above is exact constraint propagation: it can prove a
 * cell impossible-at-a-value but never incorrectly forces a cell. To
 * get full solving power (needed both to find one witness solution and
 * to refute alternate values when propagation alone is not enough) we
 * add MRV backtracking search with an undo trail, so propagation state
 * can be rolled back cheaply after a trial assignment fails, without
 * rebuilding anything from scratch.
 *
 * Forced-cell determination is two-phase and, crucially, EXACT for
 * every cell -- there is no "obviously free, skip checking it"
 * shortcut based merely on the *absence* of propagation activity,
 * because that is not a sound inference in general (the row/column
 * total argument above is a concrete example of a cell being forced
 * even though no single cage, considered alone, ever needed to narrow
 * any individual domain -- an "untouched-domain" heuristic would have
 * missed exactly that case). Instead:
 *
 *   1. Propagate to a fixpoint from the visible clues (plus the
 *      residual sum cages) alone. Any cell already at domain size 1 is
 *      forced -- trivially and cheaply.
 *   2. For the remaining cells: search for one full solution (MRV
 *      backtracking on top of the phase-1 state) as a witness. Then,
 *      for every cell not yet known-forced, check whether the grid
 *      could ever look different there: temporarily forbid the
 *      witness's value at that cell and search for a completion. If
 *      none exists, the cell is forced after all; if one exists, the
 *      cell is genuinely free -- and every cell where that *second*
 *      solution actually differs from the witness is thereby *proven*
 *      free too (we have an explicit second valid grid to point to),
 *      so it is cached and never re-verified from scratch. This cache
 *      is sound because it is built from a real witness, not a
 *      structural guess.
 *
 * -------------------------------------------------------------------
 * Complexity notes
 * -------------------------------------------------------------------
 *
 * Cage revision is the potentially expensive step. It is implemented
 * as a pruned recursive search over the cage's own cells (trying each
 * cell's current domain values in turn, maintaining a running
 * sum/product and same-row/-col distinctness, and cutting a branch the
 * moment it cannot possibly reach the target), which in practice is
 * extremely fast for the small cages (almost always <= 6 cells, per
 * keen.c's own MAXBLK) that Keen actually generates, and for the
 * residual sum cages (whose strong additive bounds prune heavily even
 * at size up to w). As a defensive measure against a pathological
 * cage, a node-visit budget bounds the work of a single cage revision;
 * if exceeded, that revision simply stops early without asserting
 * anything false (soundness is unaffected -- a value's support is
 * merely left unproven for that round, which only costs completeness/
 * speed of propagation, since the search phase behind it is exact and
 * will still catch anything propagation missed).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "keen_forced_solver.h"

/* Duplicated from keen.c: these #defines are file-local there. */
#define C_NO_CLUE 0x00000000UL
#define C_ADD     0x20000000UL
#define C_MUL     0x40000000UL
#define C_SUB     0x60000000UL
#define C_DIV     0x80000000UL
#define CMASK     0xE0000000UL

#define MAX_W 9
#define MAX_A (MAX_W * MAX_W)
#define FULL_MASK(w) ((unsigned short)((1u << ((w) + 1)) - 2u)) /* bits 1..w */

/* Node-visit budget for a single cage revision's recursive search. */
#define CAGE_REVISE_BUDGET 200000

/*
 * Whole-call node budget: bounds total work across every search this
 * Solver instance does, so a single pathological query can't run
 * unboundedly long. Calibrated generously above what realistic
 * puzzles ever need; see the Solver.total_budget comment for what
 * happens (and does not happen) when it runs out.
 */
#define TOTAL_NODE_BUDGET 6000000L

/* A cell can belong to its real cage, a row-residual cage and a
 * column-residual cage: 3 is enough, 4 leaves headroom. */
#define MAX_OWNERS 4

typedef struct {
    int op;                 /* one of C_ADD/C_MUL/C_SUB/C_DIV/C_NO_CLUE */
    long value;
    int n;
    int cells[MAX_W];        /* real cages: <= MAXBLK(6); residual: <= w */
} Cage;

/* One entry in the undo trail: cell whose domain changed, and its
 * value immediately before the change (so undo is a plain restore). */
typedef struct {
    int cell;
    unsigned short prevmask;
} TrailEntry;

typedef struct {
    int w, a;
    unsigned short domain[MAX_A];

    int ncages;
    Cage *cages;

    int nowners[MAX_A];
    int owners[MAX_A][MAX_OWNERS];

    bool row_dirty[MAX_W], col_dirty[MAX_W];
    bool *cage_dirty; /* [ncages] */

    TrailEntry *trail;
    int trail_top, trail_cap;

    /*
     * Whole-call node budget (decremented by cage_search, shared
     * across every propagate()/search call this Solver instance ever
     * makes). This bounds worst-case latency on pathological inputs:
     * once exhausted, the per-cell verification loop in
     * keen_forced_solver() stops early rather than continuing to hunt
     * for proofs. This can only make the result MISS a forced cell
     * (report '.' where the true answer has a digit) -- it can never
     * cause a wrong digit to be reported, so soundness (every digit
     * this function does return is genuinely forced) is unaffected;
     * only completeness is bounded.
     */
    long total_budget;
    bool budget_aborted;
} Solver;

static int cell_row(const Solver *s, int c) { return c / s->w; }
static int cell_col(const Solver *s, int c) { return c % s->w; }
static int cell_row_static(int w, int c) { return c / w; }
static int cell_col_static(int w, int c) { return c % w; }

static void trail_push(Solver *s, int cell, unsigned short prevmask)
{
    if (s->trail_top == s->trail_cap) {
        s->trail_cap = s->trail_cap ? s->trail_cap * 2 : 256;
        s->trail = realloc(s->trail, (size_t)s->trail_cap * sizeof(TrailEntry));
    }
    s->trail[s->trail_top].cell = cell;
    s->trail[s->trail_top].prevmask = prevmask;
    s->trail_top++;
}

static void undo_to(Solver *s, int mark)
{
    while (s->trail_top > mark) {
        s->trail_top--;
        s->domain[s->trail[s->trail_top].cell] = s->trail[s->trail_top].prevmask;
    }
}

/* Mark the row/col/cage(s) containing `cell` dirty, so they get
 * revisited by the propagation fixpoint loop. */
static void mark_dirty(Solver *s, int cell)
{
    int r = cell_row(s, cell), c = cell_col(s, cell), k;
    s->row_dirty[r] = true;
    s->col_dirty[c] = true;
    for (k = 0; k < s->nowners[cell]; k++)
        s->cage_dirty[s->owners[cell][k]] = true;
}

/* Remove `removemask` bits from cell's domain. Returns false if the
 * domain becomes empty (contradiction). Pushes an undo entry and marks
 * dependents dirty on any actual change. */
static bool remove_from_domain(Solver *s, int cell, unsigned short removemask)
{
    unsigned short cur = s->domain[cell];
    unsigned short next = (unsigned short)(cur & ~removemask);
    if (next == cur)
        return true; /* no-op */
    trail_push(s, cell, cur);
    s->domain[cell] = next;
    if (next == 0)
        return false;
    mark_dirty(s, cell);
    return true;
}

static bool assign_domain(Solver *s, int cell, unsigned short newmask)
{
    return remove_from_domain(s, cell, (unsigned short)(s->domain[cell] & ~newmask));
}

static int popcount16(unsigned short m)
{
    int c = 0;
    while (m) { m &= (unsigned short)(m - 1); c++; }
    return c;
}

/* Lowest set bit's value (1..w), assuming m != 0. */
static int lowest_value(unsigned short m)
{
    int v = 0;
    while (!(m & 1)) { m >>= 1; v++; }
    return v;
}

/* ------------------------------------------------------------------
 * Row/column (Latin square) propagation.
 * ------------------------------------------------------------------ */

static bool revise_unit(Solver *s, const int *cells, int n)
{
    int i;
    unsigned short singles = 0;

    /* Naked singles: collect the values already pinned down in this
     * unit; two cells pinned to the same value is a contradiction. */
    for (i = 0; i < n; i++) {
        unsigned short d = s->domain[cells[i]];
        if (popcount16(d) == 1) {
            if (singles & d)
                return false;
            singles |= d;
        }
    }
    if (singles) {
        for (i = 0; i < n; i++) {
            unsigned short d = s->domain[cells[i]];
            if (popcount16(d) == 1)
                continue;
            if (!remove_from_domain(s, cells[i], singles))
                return false;
        }
    }

    /* Hidden singles: a value with exactly one candidate cell left in
     * the unit must go there; a value with zero candidate cells is a
     * contradiction (every row/col must contain every value 1..w). */
    {
        int value;
        for (value = 1; value <= s->w; value++) {
            unsigned short bit = (unsigned short)(1u << value);
            int count = 0, only = -1;
            for (i = 0; i < n; i++) {
                if (s->domain[cells[i]] & bit) { count++; only = cells[i]; }
            }
            if (count == 0)
                return false;
            if (count == 1) {
                if (!assign_domain(s, only, bit))
                    return false;
            }
        }
    }

    return true;
}

/* ------------------------------------------------------------------
 * Cage arithmetic propagation.
 * ------------------------------------------------------------------ */

typedef struct {
    Solver *s;
    const Cage *cage;
    long budget;
    unsigned short support[MAX_W]; /* support[i] = bitmask of values
                                       proven reachable for cage->cells[i] */
    int assigned[MAX_W];           /* working assignment during search */
} CageCtx;

static void cage_search(CageCtx *ctx, int idx, long acc)
{
    const Cage *cage = ctx->cage;
    Solver *s = ctx->s;
    int n = cage->n;

    s->total_budget--;
    if (ctx->budget-- <= 0)
        return;

    if (idx == n) {
        bool ok;
        if (cage->op == C_ADD) {
            ok = (acc == cage->value);
        } else if (cage->op == C_MUL) {
            ok = (acc == cage->value);
        } else if (cage->op == C_SUB) {
            ok = (labs((long)ctx->assigned[0] - (long)ctx->assigned[1]) == cage->value);
        } else { /* C_DIV */
            int v0 = ctx->assigned[0], v1 = ctx->assigned[1];
            int num = v0 > v1 ? v0 : v1, den = v0 > v1 ? v1 : v0;
            ok = (den != 0 && num == den * (int)cage->value);
        }
        if (!ok) return;

        {
            int i;
            for (i = 0; i < n; i++)
                ctx->support[i] |= (unsigned short)(1u << ctx->assigned[i]);
        }
        return;
    }

    {
        int cell = cage->cells[idx];
        unsigned short dom = s->domain[cell];
        int value;
        for (value = 1; value <= s->w; value++) {
            unsigned short bit = (unsigned short)(1u << value);
            int i;
            bool clash = false;
            long newacc = acc;

            if (!(dom & bit)) continue;

            /* Distinctness against already-assigned cage cells sharing
             * this cell's row or column (Keen allows repeats within a
             * cage otherwise). */
            for (i = 0; i < idx; i++) {
                if (ctx->assigned[i] == value) {
                    int other = cage->cells[i];
                    if (cell_row(s, other) == cell_row(s, cell) ||
                        cell_col(s, other) == cell_col(s, cell)) {
                        clash = true;
                        break;
                    }
                }
            }
            if (clash) continue;

            if (cage->op == C_ADD) {
                newacc = acc + value;
                if (newacc > cage->value) continue;
                {
                    long best = newacc + (long)(n - idx - 1) * s->w;
                    if (best < cage->value) continue;
                }
            } else if (cage->op == C_MUL) {
                newacc = acc * value;
                if (newacc > cage->value || newacc <= 0) continue;
                if (cage->value % newacc != 0) continue;
            }

            ctx->assigned[idx] = value;
            cage_search(ctx, idx + 1, newacc);
            if (ctx->budget <= 0) return;
        }
    }
}

static bool revise_cage(Solver *s, int cageidx)
{
    Cage *cage = &s->cages[cageidx];
    CageCtx ctx;
    int i;

    if (cage->op == C_NO_CLUE)
        return true; /* masked cage: no arithmetic constraint at all */

    ctx.s = s;
    ctx.cage = cage;
    ctx.budget = CAGE_REVISE_BUDGET;
    for (i = 0; i < cage->n; i++) ctx.support[i] = 0;

    cage_search(&ctx, 0, cage->op == C_MUL ? 1 : 0);

    if (ctx.budget <= 0)
        return true; /* budget exhausted: skip filtering this round */

    for (i = 0; i < cage->n; i++) {
        if (ctx.support[i] == 0)
            return false; /* no completion at all for this cage */
        if (!remove_from_domain(s, cage->cells[i],
                                 (unsigned short)(s->domain[cage->cells[i]] & ~ctx.support[i])))
            return false;
    }
    return true;
}

/* ------------------------------------------------------------------
 * Fixpoint propagation loop.
 * ------------------------------------------------------------------ */

static bool propagate(Solver *s)
{
    bool progress = true;
    while (progress) {
        int i;
        progress = false;

        for (i = 0; i < s->w; i++) {
            if (s->row_dirty[i]) {
                int cells[MAX_W], k;
                s->row_dirty[i] = false;
                for (k = 0; k < s->w; k++) cells[k] = i * s->w + k;
                if (!revise_unit(s, cells, s->w)) return false;
            }
        }
        for (i = 0; i < s->w; i++) {
            if (s->col_dirty[i]) {
                int cells[MAX_W], k;
                s->col_dirty[i] = false;
                for (k = 0; k < s->w; k++) cells[k] = k * s->w + i;
                if (!revise_unit(s, cells, s->w)) return false;
            }
        }
        for (i = 0; i < s->ncages; i++) {
            if (s->cage_dirty[i]) {
                s->cage_dirty[i] = false;
                if (!revise_cage(s, i)) return false;
            }
        }

        for (i = 0; i < s->w; i++)
            if (s->row_dirty[i] || s->col_dirty[i]) { progress = true; break; }
        if (!progress)
            for (i = 0; i < s->ncages; i++)
                if (s->cage_dirty[i]) { progress = true; break; }
    }
    return true;
}

static void mark_all_dirty(Solver *s)
{
    int i;
    for (i = 0; i < s->w; i++) { s->row_dirty[i] = true; s->col_dirty[i] = true; }
    for (i = 0; i < s->ncages; i++) s->cage_dirty[i] = true;
}

/* ------------------------------------------------------------------
 * MRV backtracking search on top of the propagated domains.
 * ------------------------------------------------------------------ */

static int pick_mrv_cell(Solver *s)
{
    int best = -1, bestcount = MAX_W + 1, i;
    for (i = 0; i < s->a; i++) {
        int c = popcount16(s->domain[i]);
        if (c >= 2 && c < bestcount) { bestcount = c; best = i; }
    }
    return best;
}

/*
 * General backtracking search: descends via MRV + propagation until
 * every cell is a singleton (a "leaf", i.e. a complete valid solution
 * given the current domains), then asks `leaf_ok` whether that's a
 * good enough place to stop. If `leaf_ok` says yes, the whole search
 * returns true immediately, leaving s->domain as that leaf (the trail
 * is NOT unwound, so the caller can inspect it). If `leaf_ok` says no,
 * the search backtracks past this leaf and keeps looking for another
 * one, the same way it backtracks past any other dead end. If the
 * entire remaining search tree is exhausted without `leaf_ok` ever
 * returning true, the whole call returns false and every trail entry
 * it pushed is unwound (domains restored to how they were on entry).
 *
 * This one primitive covers everything phase 2 needs:
 *   - "find any solution" (leaf_always): used both to find the initial
 *     witness and, per remaining ambiguous cell, to look for some
 *     completion consistent with that cell's value having been ruled
 *     out.
 *   - "find a solution other than this specific one" (leaf_differs):
 *     used once, right after the witness is found, to cheaply settle
 *     the common case where the whole grid turns out to be uniquely
 *     forced -- if no other solution exists at all, every remaining
 *     cell is forced in one search, instead of needing one expensive
 *     failed (UNSAT) search per cell to establish the same thing.
 */
static bool search_enumerate(Solver *s, int depth_budget,
                              bool (*leaf_ok)(Solver *s, void *ctx), void *ctx)
{
    int cell, value;
    unsigned short dom;

    if (depth_budget <= 0)
        return false; /* defensive only; w <= 9 never needs this many */

    if (s->total_budget <= 0) {
        /* Whole-call node budget exhausted: unwind immediately rather
         * than trying further branches. The caller must check
         * s->budget_aborted before treating this "false" as a proof
         * of non-existence -- it isn't one. */
        s->budget_aborted = true;
        return false;
    }

    cell = pick_mrv_cell(s);
    if (cell == -1)
        return leaf_ok(s, ctx);

    dom = s->domain[cell];
    for (value = 1; value <= s->w; value++) {
        unsigned short bit = (unsigned short)(1u << value);
        int mark;
        if (!(dom & bit)) continue;

        mark = s->trail_top;
        if (assign_domain(s, cell, bit) && propagate(s)) {
            if (search_enumerate(s, depth_budget - 1, leaf_ok, ctx))
                return true;
            if (s->budget_aborted) {
                undo_to(s, mark);
                return false;
            }
        }
        undo_to(s, mark);
    }
    return false;
}

/* Accepts the first leaf reached, unconditionally: "find any solution". */
static bool leaf_always(Solver *s, void *vctx)
{
    (void)s; (void)vctx;
    return true;
}

/* Accepts a leaf only if it differs, in some cell, from EVERY grid in
 * a small list of already-known solutions: "find a solution other
 * than any of these, if one exists". With nexclude==1 this is just
 * "find a solution other than this one". */
#define MAX_EXCLUDE 6
typedef struct {
    const unsigned short *exclude[MAX_EXCLUDE];
    int nexclude;
    int a;
} ExcludeCtx;

static bool leaf_differs(Solver *s, void *vctx)
{
    ExcludeCtx *ctx = (ExcludeCtx *)vctx;
    int e;
    for (e = 0; e < ctx->nexclude; e++) {
        int k;
        bool same = true;
        for (k = 0; k < ctx->a; k++) {
            if (s->domain[k] != ctx->exclude[e][k]) { same = false; break; }
        }
        if (same) return false; /* matches a known solution: keep looking */
    }
    return true;
}

/* ------------------------------------------------------------------
 * Cage extraction from dsf + clues (mirrors keen.c's own solver()),
 * plus synthetic row/column residual-sum cages.
 * ------------------------------------------------------------------ */

static int build_cages(int w, DSF *dsf, unsigned long *clues, Cage **out_cages)
{
    int a = w * w;
    int i, j, n;
    int ncages = 0;
    Cage *cages;

    for (i = 0; i < a; i++)
        if (dsf_minimal(dsf, i) == i)
            ncages++;

    /* Room for the real cages plus up to 2*w synthetic residual-sum
     * cages (at most one per row, one per column), added in below. */
    cages = calloc((size_t)(ncages + 2 * w), sizeof(Cage));

    for (n = i = 0; i < a; i++) {
        if (dsf_minimal(dsf, i) == i) {
            unsigned long clue = clues[i];
            unsigned long op = clue & CMASK;
            long value = (long)(clue & ~CMASK);

            cages[n].op = (int)op;
            cages[n].value = value;
            cages[n].n = 0;
            for (j = 0; j < a; j++) {
                if (dsf_minimal(dsf, j) == i)
                    cages[n].cells[cages[n].n++] = j;
            }
            n++;
        }
    }
    assert(n == ncages);

    /*
     * Synthetic residual-sum cages: for each row and each column,
     * find the visible (C_ADD) cages entirely contained within it,
     * and -- if that covers some but not all of the unit's cells --
     * add one more C_ADD "cage" over exactly the leftover cells, with
     * target = w*(w+1)/2 minus the covered cages' targets. This is a
     * plain consequence of every row/column summing to that constant
     * in any valid completion; see the file header for why it matters.
     */
    {
        int total = w * (w + 1) / 2;
        int dim;
        for (dim = 0; dim < 2; dim++) {
            int u;
            for (u = 0; u < w; u++) {
                bool covered[MAX_W];
                int k, coveredcount = 0, ci;
                long ssum = 0;

                for (k = 0; k < w; k++) covered[k] = false;

                for (ci = 0; ci < ncages; ci++) {
                    Cage *cg = &cages[ci];
                    bool contained = true;
                    if (cg->op != C_ADD) continue;
                    for (k = 0; k < cg->n; k++) {
                        int cell = cg->cells[k];
                        int unit = (dim == 0) ? cell_row_static(w, cell)
                                               : cell_col_static(w, cell);
                        if (unit != u) { contained = false; break; }
                    }
                    if (!contained) continue;
                    for (k = 0; k < cg->n; k++) {
                        int cell = cg->cells[k];
                        int pos = (dim == 0) ? cell_col_static(w, cell)
                                              : cell_row_static(w, cell);
                        if (!covered[pos]) { covered[pos] = true; coveredcount++; }
                    }
                    ssum += cg->value;
                }

                if (coveredcount == 0 || coveredcount == w)
                    continue;

                {
                    Cage *rc = &cages[n];
                    int pos;
                    rc->op = (int)C_ADD;
                    rc->value = total - ssum;
                    rc->n = 0;
                    for (pos = 0; pos < w; pos++) {
                        if (!covered[pos]) {
                            int cell = (dim == 0) ? (u * w + pos) : (pos * w + u);
                            rc->cells[rc->n++] = cell;
                        }
                    }
                    n++;
                }
            }
        }
    }

    *out_cages = cages;
    return n;
}

/* ------------------------------------------------------------------
 * Public entry point.
 * ------------------------------------------------------------------ */

char *keen_forced_solver(int w, DSF *dsf, unsigned long *clues)
{
    Solver s;
    int a = w * w;
    int i;
    char *out;
    unsigned short witness[MAX_A];
    bool is_forced[MAX_A];
    bool proven_free[MAX_A];

    memset(&s, 0, sizeof(s));
    s.w = w;
    s.a = a;
    s.total_budget = TOTAL_NODE_BUDGET;
    s.budget_aborted = false;
    for (i = 0; i < a; i++) s.domain[i] = FULL_MASK(w);

    s.ncages = build_cages(w, dsf, clues, &s.cages);
    s.cage_dirty = calloc((size_t)s.ncages, sizeof(bool));

    for (i = 0; i < a; i++) s.nowners[i] = 0;
    {
        int ci;
        for (ci = 0; ci < s.ncages; ci++) {
            int k;
            for (k = 0; k < s.cages[ci].n; k++) {
                int cell = s.cages[ci].cells[k];
                if (s.nowners[cell] < MAX_OWNERS)
                    s.owners[cell][s.nowners[cell]++] = ci;
            }
        }
    }

    mark_all_dirty(&s);

    if (!propagate(&s)) {
        free(s.cages);
        free(s.cage_dirty);
        free(s.trail);
        return NULL;
    }

    out = malloc((size_t)a + 1);
    out[a] = '\0';

    for (i = 0; i < a; i++) { is_forced[i] = false; proven_free[i] = false; }
    for (i = 0; i < a; i++) {
        if (popcount16(s.domain[i]) == 1) {
            witness[i] = s.domain[i];
            is_forced[i] = true;
        }
    }

    /*
     * Cheap structural heuristic: if two (or more) whole rows contain no
     * cell belonging to any visible cage at all -- neither a real clued
     * cage nor a synthetic residual row/column-sum cage -- then no cell
     * in any of those rows can be forced, regardless of what the rest of
     * the grid looks like. Proof: take any two such untouched rows and
     * swap their entire contents between a valid completion and itself.
     * Every cage is unaffected (no cage touches either row), each row
     * remains a permutation of 1..w (we've just swapped two whole rows'
     * worth of values), and every column keeps the same *set* of values
     * across those two rows (only which of the two rows holds which
     * value changes), so column distinctness is preserved too. The
     * result is a second valid, genuinely different completion whenever
     * w >= 2, so every cell in either row disagrees between at least two
     * valid completions -- it cannot be forced. The same argument holds
     * for columns by symmetry. This needs no search at all, so it's
     * applied unconditionally up front, before the (much more
     * expensive) witness/verify machinery below -- and it also *reduces*
     * work for the cells that remain, since they no longer have to be
     * considered by the global "does any other completion exist" check.
     */
    {
        bool row_has_clue[MAX_W], col_has_clue[MAX_W];
        int r, c, ci, untouched_rows, untouched_cols;

        for (r = 0; r < w; r++) row_has_clue[r] = false;
        for (c = 0; c < w; c++) col_has_clue[c] = false;

        for (ci = 0; ci < s.ncages; ci++) {
            int k;
            if (s.cages[ci].op == C_NO_CLUE) continue;
            for (k = 0; k < s.cages[ci].n; k++) {
                int cell = s.cages[ci].cells[k];
                row_has_clue[cell_row_static(w, cell)] = true;
                col_has_clue[cell_col_static(w, cell)] = true;
            }
        }

        untouched_rows = 0;
        for (r = 0; r < w; r++) if (!row_has_clue[r]) untouched_rows++;
        untouched_cols = 0;
        for (c = 0; c < w; c++) if (!col_has_clue[c]) untouched_cols++;

        if (untouched_rows >= 2) {
            for (r = 0; r < w; r++)
                if (!row_has_clue[r])
                    for (c = 0; c < w; c++)
                        proven_free[r * w + c] = true;
        }
        if (untouched_cols >= 2) {
            for (c = 0; c < w; c++)
                if (!col_has_clue[c])
                    for (r = 0; r < w; r++)
                        proven_free[r * w + c] = true;
        }
    }

    {
        bool any_unforced = false;
        for (i = 0; i < a; i++)
            if (!is_forced[i] && !proven_free[i]) { any_unforced = true; break; }

        if (any_unforced) {
            int mark = s.trail_top;

            if (!search_enumerate(&s, a + 5, leaf_always, NULL)) {
                if (s.budget_aborted) {
                    /* Could not even find one completion within the
                     * node budget (should be exceptionally rare: this
                     * is normally the cheapest search of the whole
                     * call). Nothing is provably forced yet -- report
                     * only what phase-1 propagation already knows. */
                    undo_to(&s, mark);
                    goto done_verifying;
                }
                /* No completion at all: contradiction (shouldn't
                 * happen for a masked-down relaxation of a solvable
                 * puzzle, but handled defensively). */
                free(s.cages);
                free(s.cage_dirty);
                free(s.trail);
                free(out);
                return NULL;
            }
            for (i = 0; i < a; i++) witness[i] = s.domain[i];
            undo_to(&s, mark);

            /*
             * Before checking cells one at a time, ask the much more
             * powerful question "does *any* other solution exist at
             * all?" in a single search, and repeat it a few times
             * (excluding every solution seen so far) as long as it
             * keeps turning up new ones. This matters enormously when
             * the true answer (or close to it) is that the grid is
             * uniquely forced: finding that out costs a handful of
             * searches here, versus one expensive failed (UNSAT)
             * search per remaining cell if we went straight to the
             * per-cell loop below. Each alternate found frees, in one
             * shot, every cell where it differs from the witness.
             */
            {
                unsigned short altbuf[MAX_EXCLUDE - 1][MAX_A];
                ExcludeCtx ectx;
                int round;

                ectx.exclude[0] = witness;
                ectx.nexclude = 1;
                ectx.a = a;

                for (round = 0; round < MAX_EXCLUDE - 1; round++) {
                    int mark2 = s.trail_top;
                    bool any_left = false;

                    for (i = 0; i < a; i++)
                        if (!is_forced[i] && !proven_free[i]) { any_left = true; break; }
                    if (!any_left) break;

                    if (search_enumerate(&s, a + 5, leaf_differs, &ectx)) {
                        int k;
                        for (k = 0; k < a; k++) {
                            altbuf[round][k] = s.domain[k];
                            if (!is_forced[k] && s.domain[k] != witness[k])
                                proven_free[k] = true;
                        }
                        undo_to(&s, mark2);
                        ectx.exclude[ectx.nexclude++] = altbuf[round];
                    } else {
                        undo_to(&s, mark2);
                        if (!s.budget_aborted) {
                            /* Genuinely exhausted, not just cut off:
                             * no solution differs from any found so
                             * far, so everything still unresolved is
                             * forced. */
                            int k;
                            for (k = 0; k < a; k++)
                                if (!is_forced[k] && !proven_free[k])
                                    is_forced[k] = true;
                        }
                        break;
                    }
                }
            }

            if (s.budget_aborted) {
                /* Node budget spent: stop looking for more proofs.
                 * Cells not yet marked forced or free simply stay
                 * unresolved ('.') -- safe (never a wrong digit),
                 * just possibly incomplete for this one pathological
                 * input. */
                goto done_verifying;
            }

            /*
             * Whatever the bulk check above didn't already settle
             * (some cells forced, some free, mixed in a way that one
             * global search can't tease apart) falls back to checking
             * each remaining cell on its own: temporarily rule out its
             * witness value and see whether any completion still
             * exists. This is cheap for genuinely free cells (a
             * completion is usually found quickly) -- forced cells are
             * the expensive direction (proving none exists), but by
             * this point there are typically few of them left.
             */
            for (i = 0; i < a; i++) {
                unsigned short trial_value_bit;
                int trymark;

                if (is_forced[i] || proven_free[i])
                    continue;

                trial_value_bit = witness[i];
                trymark = s.trail_top;

                if (!remove_from_domain(&s, i, trial_value_bit)) {
                    /* Only one value was ever possible here: forced. */
                    undo_to(&s, trymark);
                    is_forced[i] = true;
                    continue;
                }

                if (propagate(&s) && search_enumerate(&s, a + 5, leaf_always, NULL)) {
                    /* Genuine alternate completion found: every cell
                     * that differs from the witness here is thereby
                     * proven free too, not just cell i. */
                    int k;
                    for (k = 0; k < a; k++) {
                        if (!is_forced[k] && s.domain[k] != witness[k])
                            proven_free[k] = true;
                    }
                } else if (!s.budget_aborted) {
                    is_forced[i] = true;
                }

                undo_to(&s, trymark);

                if (s.budget_aborted)
                    break; /* leave any remaining cells unresolved */
            }
        }
    }

done_verifying:
    for (i = 0; i < a; i++)
        out[i] = is_forced[i] ? (char)('0' + lowest_value(witness[i])) : '.';

    free(s.cages);
    free(s.cage_dirty);
    free(s.trail);
    return out;
}
