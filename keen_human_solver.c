/*
 * keen_human_solver.c: "human-style" partial solver for Keen.
 *
 * See keen_human_solver.h for why this exists alongside the exact
 * keen_forced_solver(). This file implements ONLY non-bifurcating
 * deduction: there is no trial assignment, no backtracking, no "assume
 * a value and look for a contradiction" anywhere in this file. Every
 * rule below is a direct logical inference from the current state, and
 * every domain/tuple removal is permanent (never needs to be undone),
 * which is what makes this solver's output an accessible proof of each
 * cell it reports, unlike a search-based result.
 *
 * -------------------------------------------------------------------
 * Data model
 * -------------------------------------------------------------------
 *
 * Per the project spec this implements, a cage's state is not just a
 * per-cell candidate bitmask (although that is derived from it): it is
 * the explicit list of every still-possible complete assignment of
 * digits to that cage's own cells ("tuples") that is consistent with
 * the cage's operation and target, mutual distinctness among cage cells
 * sharing a row or column, and the CURRENT candidate domains of its
 * cells. This tuple list is rebuilt from scratch, from the live
 * domains, every round any of its cells' domains changed -- so it is
 * always exact for the domains as they stand right now (never stale).
 * From it we derive:
 *
 *   - Per-cell support: which values still appear in at least one
 *     surviving tuple, at each cell -- values with none are removed
 *     from that cell's domain ("cage candidate elimination").
 *   - Per-digit and per-digit-pair minimum occurrence counts across the
 *     cage's cells: the smallest number of times digit d (or, for a
 *     pair {d1,d2}, either of them) appears in ANY surviving tuple. A
 *     nonzero minimum is a proven fact of the form "this cage's cells
 *     collectively contain at least one 3" / "at least one of {3,6}",
 *     used below by the counting/capacity rule.
 *
 * -------------------------------------------------------------------
 * Deduction techniques (the fixpoint loop applies all of these, in a
 * fixed order, repeatedly, until a full pass changes nothing)
 * -------------------------------------------------------------------
 *
 *  1. Cage candidate elimination (per-cell support, above).
 *  2. Row/column naked singles and hidden singles -- standard.
 *  3. Row/column naked and hidden SUBSETS of size 2 and 3: m cells whose
 *     combined candidates are exactly m values ("naked"), or m values
 *     whose combined candidate cells are exactly m cells ("hidden"),
 *     let every other cell/value in the unit be pruned accordingly.
 *  4. Synthetic residual-sum cages: for a row or column with one or
 *     more visible addition cages entirely contained in it, the
 *     leftover cells must sum to (the unit's fixed total) minus (those
 *     cages' targets) -- folded in as one more addition cage over
 *     exactly those leftover cells, so it gets the exact same
 *     candidate-elimination treatment as any other cage (this is what
 *     lets "three cells sum to 10, next two sum to 7" force a width-6
 *     row's last cell to 4, purely from row-sum arithmetic).
 *  5. Row/column-GROUP digit-set capacity/counting deduction -- the
 *     general technique the project spec asks for by name. For a group
 *     G of k whole rows (or k whole columns) and a set S of 1 or 2
 *     digits, exactly k*|S| of G's cells hold a value in S, in ANY
 *     completion (each of the k rows/columns contains each digit
 *     exactly once). Summing every cage's minimum-occurrence-of-S
 *     (technique 1 above) over the REAL cages (never a synthetic
 *     residual-sum cage from technique 4 -- see Cage.is_residual's
 *     comment for why a residual cage can overlap a real cage's cells,
 *     which would make summing their guarantees unsound) entirely
 *     confined to G gives a sound lower bound "demand" on how many of
 *     that capacity those cages alone already require, since real
 *     cages always partition the grid and so are guaranteed pairwise
 *     disjoint:
 *       (a) if demand == capacity exactly, every cell of G NOT
 *           belonging to one of those confined cages cannot hold a
 *           value in S (the capacity is already fully spoken for) --
 *           this is the row/column-total technique (4) generalised
 *           from a single arithmetic sum to any digit or digit pair,
 *           and to combinations of more than one row/column at once.
 *       (b) for a specific confined cage C and one of its surviving
 *           tuples T: if using T would push the demand from every OTHER
 *           confined cage plus T's own contribution of S past capacity,
 *           T can never be part of a completion -- remove it from C's
 *           tuple list. This is exactly the project spec's worked
 *           example: two rows have exactly two 3s and two 6s between
 *           them (capacity 4 for S={3,6}); if three cages there already
 *           each guarantee at least one of {3,6} (demand >= 3) and a
 *           fourth cage has a candidate tuple using both a 3 and a 6 at
 *           once (contributing 2), 3 + 2 = 5 > 4 is impossible, so that
 *           tuple is eliminated.
 *     See the file-level comment further down (search for "GROUP
 *     CAPACITY") for the soundness argument and the scope this
 *     implementation deliberately caps (group size <= 3, digit-set
 *     size <= 2) to keep the search over combinations bounded -- both
 *     caps are named constants and easy to widen.
 *
 * None of the above ever performs a trial assignment: every removal
 * (of a domain value or of a cage tuple) is justified purely by what
 * is CURRENTLY known to be impossible, which is exactly what makes it
 * safe to apply permanently with no undo mechanism at all -- unlike
 * keen_forced_solver.c, this file has no trail/backtracking machinery
 * whatsoever.
 *
 * -------------------------------------------------------------------
 * Soundness vs. completeness
 * -------------------------------------------------------------------
 *
 * Every individual rule above is a valid logical inference, so nothing
 * this file ever reports as forced can be wrong: it is always a SOUND
 * SUBSET of what keen_forced_solver() would report (verified for this
 * codebase by a randomised regression test that runs both solvers over
 * many random partial-clue states of real generated puzzles and checks
 * that every digit this solver reports agrees with the exact solver --
 * see auxiliary/keen-human-solver-test.c). It is not complete: there
 * exist forced cells (particularly ones only provable via full
 * backtracking search, or via counting arguments over digit sets larger
 * than 2, or groups larger than 3 rows/columns) that this file will
 * report as undetermined ('.') even though they are mathematically
 * forced. That incompleteness is the entire point of this file existing
 * separately from keen_forced_solver() -- see keen_human_solver.h.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "keen_human_solver.h"

/* Duplicated from keen.c (file-local #defines there), same as
 * keen_forced_solver.c. */
#define C_NO_CLUE 0x00000000UL
#define C_ADD     0x20000000UL
#define C_MUL     0x40000000UL
#define C_SUB     0x60000000UL
#define C_DIV     0x80000000UL
#define CMASK     0xE0000000UL

#define MAX_W 9
#define MAX_A (MAX_W * MAX_W)
#define FULL_MASK(w) ((unsigned short)((1u << ((w) + 1)) - 2u)) /* bits 1..w */

/* Real cages are <= MAXBLK(6) cells; residual cages are <= w cells. */
#define MAX_CAGE_CELLS MAX_W

/*
 * Cap on how many complete tuples one cage enumeration will collect
 * before giving up FOR THIS ROUND ONLY. Real Keen cages (<=6 cells,
 * tightly constrained arithmetic) and residual cages (strong additive
 * bounds) stay far below this in practice; it exists purely as a
 * defensive bound against a pathological input. When hit, the cage's
 * tuple list for this round is discarded entirely (not truncated) and
 * every rule above simply skips that cage until its next re-enumeration
 * -- see enumerate_cage()'s comment for why a truncated list would be
 * unsound to use, whereas skipping the cage entirely is always safe
 * (soundness depends only on which conclusions we draw, never on how
 * many rounds it takes to draw them).
 */
#define MAX_TUPLES 4096
#define CAGE_ENUM_BUDGET 300000

/* Largest row/column-group size the capacity rule (technique 5 above)
 * considers, and the largest digit-set size within a group. Both are
 * small, named constants specifically so they can be widened later
 * without touching the algorithm -- see the file header for why these
 * particular caps were chosen (bounding the number of combinations
 * checked each round, not the underlying technique). */
#define MAX_GROUP_SIZE 3
#define MAX_SET_SIZE 2

typedef struct {
    int op;                 /* C_ADD/C_MUL/C_SUB/C_DIV/C_NO_CLUE */
    long value;
    int n;
    int cells[MAX_CAGE_CELLS];

    unsigned int rowmask;    /* bit r set iff some cage cell is in row r */
    unsigned int colmask;    /* bit c set iff some cage cell is in col c */

    /*
     * Explicit list of every currently-possible complete assignment of
     * digits to cells[0..n-1] (tuples[t][i] is the value assigned to
     * cells[i] in candidate assignment t). tuples_valid is false
     * whenever the last enumeration attempt hit CAGE_ENUM_BUDGET or
     * MAX_TUPLES -- see enumerate_cage(). Every rule that reads a
     * cage's tuples must check tuples_valid first and skip the cage
     * (drawing no conclusion at all) if it's false.
     */
    bool tuples_valid;
    int ntuples;
    unsigned char (*tuples)[MAX_CAGE_CELLS];

    /* Derived from the tuple list whenever tuples_valid: mincount[d]
     * (1<=d<=w) is the fewest times digit d appears in any one
     * surviving tuple; mincount_pair[d1][d2] (1<=d1<d2<=w) is the same
     * for "d1 or d2 combined", i.e. min over tuples of (count of d1) +
     * (count of d2) in that tuple. Index 0 of each array is unused. */
    int mincount[MAX_W + 1];
    int mincount_pair[MAX_W + 1][MAX_W + 1];

    /*
     * true for a synthetic residual-sum cage (see build_cages()), false
     * for a real cage extracted from the puzzle's own clues. Real
     * cages always partition the grid -- every cell belongs to
     * EXACTLY one -- so they are guaranteed pairwise cell-disjoint. A
     * residual cage is NOT guaranteed disjoint from every other cage:
     * it covers a unit's "leftover" cells (those not covered by some
     * OTHER cage entirely contained in that same unit), but a cage
     * that spans multiple rows/columns (like a vertical or L-shaped
     * cage) is never "contained" in any one unit and so is never
     * excluded from a residual cage's leftover-cell computation --
     * meaning a residual cage's cells can genuinely overlap a real
     * cage's cells. The group-capacity technique's demand computation
     * (see apply_group_capacity()) sums mincount_S over the cages it
     * considers on the assumption that they are pairwise disjoint
     * (summing lower bounds on disjoint cell-sets is what makes the
     * sum itself a valid lower bound on the group's total) -- so it
     * must restrict itself to is_residual==false cages only, or an
     * overlapping residual cage's guaranteed occurrences could be
     * counted twice (once via itself, once via the real cage sharing
     * its cell), inflating demand past what is actually true and
     * risking a false contradiction. This field exists purely to let
     * that restriction be applied.
     */
    bool is_residual;

    /*
     * true iff some cell of this cage has had its domain change since
     * this cage was last (re-)enumerated -- see mark_dirty(). Only
     * dirty cages are re-enumerated each round (run_one_pass()): a
     * cage whose cells haven't changed would just recompute the exact
     * same tuple list (enumeration depends only on the current
     * domains of its own cells), so skipping it is a pure performance
     * win, never a soundness or completeness change. Starts true for
     * every cage so the first round enumerates everything.
     */
    bool dirty;

    /*
     * Meaningful only for a residual cage (is_residual == true), used
     * only by the incremental/warm-start API below (KeenHumanIncSolver):
     * true iff this residual slot currently covers at least one leftover
     * cell (n > 0). A residual cage that has never been activated (no
     * contained ADD cage revealed yet in its row/column) and one that
     * was activated but has since been fully covered again (every
     * position now covered by some revealed contained ADD cage) are
     * both represented as n == 0 and behave identically to every
     * downstream consumer (apply_cage_support, revise_unit_subsets's
     * caller, cage_confined_to, the group-capacity sums) -- a 0-cell
     * C_ADD cage is a complete no-op everywhere. This flag exists purely
     * so the incremental reveal code can tell "not yet started" apart
     * from "fully covered" when deciding whether to reinitialize versus
     * shrink; it is never read by the one-shot solver above, which never
     * creates a Cage in this ambiguous state (build_cages() only ever
     * creates a residual cage already fully formed, or not at all).
     */
    bool activated;
} Cage;

/* A cell can belong to its real cage, a row-residual cage and a
 * column-residual cage: 3 is enough, 4 leaves headroom. Used only to
 * mark the right cages dirty when a cell's domain changes -- see
 * mark_dirty(). */
#define MAX_CELL_OWNERS 4

typedef struct {
    int w, a;
    unsigned short domain[MAX_A];

    int ncages;
    Cage *cages;

    int nowners[MAX_A];
    int owners[MAX_A][MAX_CELL_OWNERS];
    bool row_dirty[MAX_W], col_dirty[MAX_W];
    bool group_capacity_dirty;

    FILE *trace;
} Solver;

static int cell_row(const Solver *s, int c) { return c / s->w; }
static int cell_col(const Solver *s, int c) { return c % s->w; }
static int cell_row_static(int w, int c) { return c / w; }
static int cell_col_static(int w, int c) { return c % w; }

static int popcount16(unsigned short m)
{
    int c = 0;
    while (m) { m &= (unsigned short)(m - 1); c++; }
    return c;
}

static int lowest_value(unsigned short m)
{
    int v = 0;
    while (!(m & 1)) { m >>= 1; v++; }
    return v;
}

/* Marks every cage owning `cell`, plus cell's row and column, dirty --
 * called whenever cell's domain actually changes, so run_one_pass()
 * knows what needs re-examining next round. Purely a performance
 * mechanism (see Cage.dirty's comment): never affects which
 * conclusions are drawn, only how much redundant recomputation is
 * skipped in reaching them. */
static void mark_dirty(Solver *s, int cell)
{
    int k;
    for (k = 0; k < s->nowners[cell]; k++)
        s->cages[s->owners[cell][k]].dirty = true;
    s->row_dirty[cell_row(s, cell)] = true;
    s->col_dirty[cell_col(s, cell)] = true;
    s->group_capacity_dirty = true;
}

/* Remove `removemask` bits from cell's domain. Returns false if the
 * domain becomes empty (contradiction). Sets *changed on any actual
 * change. No undo trail: every call here is a permanent, sound
 * deduction, never a speculative trial. */
static bool remove_from_domain(Solver *s, int cell, unsigned short removemask,
                                bool *changed)
{
    unsigned short cur = s->domain[cell];
    unsigned short next = (unsigned short)(cur & ~removemask);
    if (next == cur)
        return true;
    s->domain[cell] = next;
    *changed = true;
    mark_dirty(s, cell);
    if (s->trace)
        fprintf(s->trace, "  domain(%d,%d) -= %04x -> %04x\n",
                cell_row(s, cell), cell_col(s, cell),
                (unsigned)removemask, (unsigned)next);
    return next != 0;
}

static bool assign_domain(Solver *s, int cell, unsigned short newmask,
                           bool *changed)
{
    return remove_from_domain(s, cell,
                               (unsigned short)(s->domain[cell] & ~newmask),
                               changed);
}

/* ------------------------------------------------------------------
 * Cage extraction from dsf + clues, plus synthetic row/column
 * residual-sum cages -- structurally identical to
 * keen_forced_solver.c's build_cages(), duplicated here (rather than
 * shared) so this file has no compile-time dependency on that one.
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
                    rc->is_residual = true;
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

    /* rowmask/colmask, and tuple-storage allocation, for every cage
     * (real and residual alike). */
    for (i = 0; i < n; i++) {
        Cage *cg = &cages[i];
        int k;
        cg->rowmask = cg->colmask = 0;
        for (k = 0; k < cg->n; k++) {
            cg->rowmask |= 1u << cell_row_static(w, cg->cells[k]);
            cg->colmask |= 1u << cell_col_static(w, cg->cells[k]);
        }
        cg->tuples = malloc(sizeof(*cg->tuples) * MAX_TUPLES);
        cg->tuples_valid = false;
        cg->ntuples = 0;
        cg->dirty = true;
    }

    *out_cages = cages;
    return n;
}

/* Populates s->owners/nowners from the already-built s->cages, so
 * mark_dirty() knows which cages to flag when a cell's domain changes.
 * Called once, right after build_cages(). */
static void build_owners(Solver *s)
{
    int i;
    for (i = 0; i < s->a; i++) s->nowners[i] = 0;
    for (i = 0; i < s->ncages; i++) {
        Cage *cg = &s->cages[i];
        int k;
        for (k = 0; k < cg->n; k++) {
            int cell = cg->cells[k];
            if (s->nowners[cell] < MAX_CELL_OWNERS)
                s->owners[cell][s->nowners[cell]++] = i;
        }
    }
}

/* ------------------------------------------------------------------
 * Cage tuple enumeration.
 * ------------------------------------------------------------------ */

typedef struct {
    Solver *s;
    Cage *cage;
    long budget;
    unsigned char cur[MAX_CAGE_CELLS];
} EnumCtx;

static bool enum_leaf_ok(EnumCtx *ctx, long acc)
{
    Cage *cage = ctx->cage;
    if (cage->op == C_ADD || cage->op == C_MUL)
        return acc == cage->value;
    if (cage->op == C_SUB)
        return labs((long)ctx->cur[0] - (long)ctx->cur[1]) == cage->value;
    {
        /* C_DIV */
        int v0 = ctx->cur[0], v1 = ctx->cur[1];
        int num = v0 > v1 ? v0 : v1, den = v0 > v1 ? v1 : v0;
        return den != 0 && num == den * (int)cage->value;
    }
}

static void enum_recurse(EnumCtx *ctx, int idx, long acc, bool *overflow)
{
    Cage *cage = ctx->cage;
    Solver *s = ctx->s;

    if (*overflow) return;
    if (ctx->budget-- <= 0) { *overflow = true; return; }

    if (idx == cage->n) {
        if (!enum_leaf_ok(ctx, acc)) return;
        if (cage->ntuples >= MAX_TUPLES) { *overflow = true; return; }
        memcpy(cage->tuples[cage->ntuples], ctx->cur, (size_t)cage->n);
        cage->ntuples++;
        return;
    }

    {
        int cell = cage->cells[idx];
        unsigned short dom = s->domain[cell];
        int value;
        for (value = 1; value <= s->w; value++) {
            unsigned short bit = (unsigned short)(1u << value);
            long newacc = acc;
            int i;
            bool clash = false;

            if (!(dom & bit)) continue;

            for (i = 0; i < idx; i++) {
                if (ctx->cur[i] == value) {
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
                    long best = newacc + (long)(cage->n - idx - 1) * s->w;
                    if (best < cage->value) continue;
                }
            } else if (cage->op == C_MUL) {
                newacc = acc * value;
                if (newacc > cage->value || newacc <= 0) continue;
                if (cage->value % newacc != 0) continue;
            }

            ctx->cur[idx] = (unsigned char)value;
            enum_recurse(ctx, idx + 1, newacc, overflow);
            if (*overflow) return;
        }
    }
}

/*
 * Rebuilds cage->tuples from scratch against the CURRENT domains. On
 * success (tuples_valid = true), also derives mincount/mincount_pair.
 * On overflow (tuples_valid = false), the tuple list and every fact
 * derived from it are discarded for this round -- NOT truncated -- so
 * that no rule ever draws a conclusion from a partial enumeration.
 * A partial list would be unsound in general: a cell-support removal
 * based on "no *scanned* tuple uses this value" could wrongly discard a
 * value whose only support was in a tuple enumeration never reached,
 * and a mincount computed from a subset of tuples could overstate the
 * true minimum (which can only go down as more tuples are found) --
 * either mistake could cascade into reporting a wrong digit. Skipping
 * the cage entirely this round has no such risk: it only costs
 * completeness (a missed deduction, to be retried once other rules
 * shrink the domains and the same enumeration becomes cheap enough to
 * finish), never soundness.
 */
/*
 * (Re)derives cage->mincount[]/mincount_pair[][] from cage->tuples[0..
 * ntuples-1] as they currently stand. Factored out of enumerate_cage()
 * so that apply_group_capacity()'s rule (b) -- which prunes tuples
 * in-place without a full re-enumeration -- can call this immediately
 * after pruning to keep mincount/mincount_pair in sync with the tuple
 * list they're supposed to summarize. Without this, a cage whose
 * tuples were pruned by rule (b) keeps stale (too-loose) mincount
 * values until it next happens to be re-enumerated for an unrelated
 * reason (its own dirty flag is never set by tuple pruning alone,
 * since pruning isn't a domain change) -- a real completeness gap:
 * still sound (a stale mincount is always <= the true, tighter one,
 * since removing tuples can only raise the true minimum), but able to
 * silently miss a further group-capacity deduction that the freshly
 * -tightened bound would have enabled, for as long as nothing else
 * happens to mark that cage dirty. Caller must ensure cage->ntuples > 0
 * (a cage with zero surviving tuples is a contradiction, handled by
 * the caller before this would be reached).
 */
static void recompute_mincounts(Solver *s, Cage *cage)
{
    int d, t, i;
    for (d = 1; d <= s->w; d++) cage->mincount[d] = cage->n + 1;
    for (d = 1; d <= s->w; d++)
        for (i = d + 1; i <= s->w; i++)
            cage->mincount_pair[d][i] = cage->n + 1;

    for (t = 0; t < cage->ntuples; t++) {
        int count[MAX_W + 1];
        for (d = 1; d <= s->w; d++) count[d] = 0;
        for (i = 0; i < cage->n; i++) count[cage->tuples[t][i]]++;
        for (d = 1; d <= s->w; d++)
            if (count[d] < cage->mincount[d]) cage->mincount[d] = count[d];
        for (d = 1; d <= s->w; d++)
            for (i = d + 1; i <= s->w; i++) {
                int combined = count[d] + count[i];
                if (combined < cage->mincount_pair[d][i])
                    cage->mincount_pair[d][i] = combined;
            }
    }
}

static bool enumerate_cage(Solver *s, Cage *cage)
{
    EnumCtx ctx;
    bool overflow = false;

    if (cage->op == C_NO_CLUE) {
        cage->tuples_valid = false;
        cage->ntuples = 0;
        return true;
    }

    ctx.s = s;
    ctx.cage = cage;
    ctx.budget = CAGE_ENUM_BUDGET;
    cage->ntuples = 0;

    enum_recurse(&ctx, 0, cage->op == C_MUL ? 1 : 0, &overflow);

    if (overflow) {
        cage->tuples_valid = false;
        cage->ntuples = 0;
        return true;
    }

    cage->tuples_valid = true;
    if (cage->ntuples == 0)
        return false; /* no completion at all for this cage: contradiction */

    recompute_mincounts(s, cage);

    return true;
}

/* Cage candidate elimination: remove, from every cell of the cage, any
 * value not used by any surviving tuple. */
static bool apply_cage_support(Solver *s, Cage *cage, bool *changed)
{
    unsigned short support[MAX_CAGE_CELLS];
    int i, t;

    if (!cage->tuples_valid) return true;

    for (i = 0; i < cage->n; i++) support[i] = 0;
    for (t = 0; t < cage->ntuples; t++)
        for (i = 0; i < cage->n; i++)
            support[i] |= (unsigned short)(1u << cage->tuples[t][i]);

    for (i = 0; i < cage->n; i++) {
        if (!remove_from_domain(s, cage->cells[i],
                                 (unsigned short)(s->domain[cage->cells[i]] & ~support[i]),
                                 changed))
            return false;
    }
    return true;
}

/* ------------------------------------------------------------------
 * Row/column naked & hidden subset elimination (sizes 1..3, which
 * covers the classic "single" as the m==1 case of each).
 * ------------------------------------------------------------------ */

static bool revise_unit_subsets(Solver *s, const int *cells, int n, bool *changed)
{
    int maxm = n < 3 ? n : 3;
    int m;

    for (m = 1; m <= maxm; m++) {
        /* ---- naked subsets of size m: choose m of the n cells ---- */
        int idx[3];
        int i0, i1, i2;
        for (i0 = 0; i0 < n; i0++) {
            idx[0] = i0;
            for (i1 = (m >= 2 ? i0 + 1 : -1); i1 < (m >= 2 ? n : 0); i1++) {
                if (m >= 2) idx[1] = i1;
                for (i2 = (m >= 3 ? i1 + 1 : -1); i2 < (m >= 3 ? n : 0); i2++) {
                    if (m >= 3) idx[2] = i2;

                    {
                        unsigned short u = 0;
                        int k;
                        for (k = 0; k < m; k++) u |= s->domain[cells[idx[k]]];
                        if (popcount16(u) != m) continue;
                        /* This m-cell subset's candidates are exactly
                         * these m values: remove them from every other
                         * cell in the unit. */
                        for (k = 0; k < n; k++) {
                            bool ismember = false;
                            int j;
                            for (j = 0; j < m; j++)
                                if (idx[j] == k) { ismember = true; break; }
                            if (ismember) continue;
                            if (s->domain[cells[k]] & u) {
                                if (s->trace)
                                    fprintf(s->trace,
                                            "  naked-%d %04x among %d cells -> "
                                            "prune cell (%d,%d)\n",
                                            m, (unsigned)u, m,
                                            cell_row(s, cells[k]), cell_col(s, cells[k]));
                                if (!remove_from_domain(s, cells[k], u, changed))
                                    return false;
                            }
                        }
                    }
                    if (m < 3) break;
                }
                if (m < 2) break;
            }
        }

        /* ---- hidden subsets of size m: choose m of the w digits ---- */
        {
            int d0, d1, d2;
            for (d0 = 1; d0 <= s->w; d0++) {
                idx[0] = d0;
                for (d1 = (m >= 2 ? d0 + 1 : -1); d1 < (m >= 2 ? s->w + 1 : 0); d1++) {
                    if (m >= 2) idx[1] = d1;
                    for (d2 = (m >= 3 ? d1 + 1 : -1); d2 < (m >= 3 ? s->w + 1 : 0); d2++) {
                        if (m >= 3) idx[2] = d2;

                        {
                            unsigned short vmask = 0;
                            unsigned short cellmask_bits = 0; /* which of the n
                                                                  cells (by
                                                                  index into
                                                                  cells[]) hold
                                                                  >=1 of these
                                                                  values */
                            int k, cellcount = 0;
                            for (k = 0; k < m; k++) vmask |= (unsigned short)(1u << idx[k]);
                            for (k = 0; k < n; k++) {
                                if (s->domain[cells[k]] & vmask) {
                                    cellmask_bits |= (unsigned short)(1u << k);
                                    cellcount++;
                                }
                            }
                            if (cellcount != m) continue;
                            /* These m values only ever appear (between
                             * them) in exactly these m cells: restrict
                             * those cells to only these values. */
                            for (k = 0; k < n; k++) {
                                if (!(cellmask_bits & (1u << k))) continue;
                                if (s->domain[cells[k]] & ~vmask) {
                                    if (s->trace)
                                        fprintf(s->trace,
                                                "  hidden-%d values %04x -> "
                                                "restrict cell (%d,%d)\n",
                                                m, (unsigned)vmask,
                                                cell_row(s, cells[k]), cell_col(s, cells[k]));
                                    if (!assign_domain(s, cells[k], vmask, changed))
                                        return false;
                                }
                            }
                        }
                        if (m < 3) break;
                    }
                    if (m < 2) break;
                }
            }
        }
    }

    /* Basic Latin-square consistency check: every value must still
     * have at least one candidate cell (a value with zero candidates
     * anywhere in the unit is an outright contradiction), and no two
     * cells may be pinned (domain size 1) to the same value. This is
     * subsumed logically by the subset code above whenever it runs to
     * completion, but is re-checked directly here for cases m's loop
     * cap (3) doesn't cover (e.g. a genuine hidden-4+ situation, which
     * this file does not attempt to exploit for a further deduction,
     * but must still not silently miss an outright contradiction). */
    {
        int i, value;
        unsigned short singles = 0;
        for (i = 0; i < n; i++) {
            if (popcount16(s->domain[cells[i]]) == 1) {
                if (singles & s->domain[cells[i]]) return false;
                singles |= s->domain[cells[i]];
            }
        }
        for (value = 1; value <= s->w; value++) {
            unsigned short bit = (unsigned short)(1u << value);
            bool any = false;
            for (i = 0; i < n; i++)
                if (s->domain[cells[i]] & bit) { any = true; break; }
            if (!any) return false;
        }
    }

    return true;
}

/* ------------------------------------------------------------------
 * Row/column-GROUP digit-set capacity/counting deduction.
 *
 * See the file header ("GROUP CAPACITY") for the full explanation and
 * soundness argument; this section just implements it. `unitmask` is a
 * bitmask of which rows (dim==0) or columns (dim==1) make up the group;
 * `k` is its popcount (the number of whole rows/columns in it).
 * ------------------------------------------------------------------ */

/*
 * Whether `cage` participates in the group-capacity technique for this
 * group. Deliberately restricted to REAL cages only (never a synthetic
 * residual-sum cage): real cages always partition the grid -- every
 * cell belongs to exactly one -- so summing mincount_S over every real
 * cage confined to a group is guaranteed sound (a valid sum of
 * disjoint lower bounds). A residual cage is not guaranteed disjoint
 * from other confined cages (see Cage.is_residual's comment for a
 * concrete case where it overlaps a real cage), so including it here
 * could double-count one cell's contribution and inflate demand past
 * what is actually true. Residual cages still fully participate in
 * the ordinary per-cage candidate-elimination technique (technique 1
 * in the file header) via enumerate_cage()/apply_cage_support() --
 * this restriction is specific to the group-capacity sum.
 */
static bool cage_confined_to(const Cage *cage, int dim, unsigned int unitmask)
{
    unsigned int cagemask;
    if (cage->is_residual) return false;
    cagemask = (dim == 0) ? cage->rowmask : cage->colmask;
    return cagemask != 0 && (cagemask & ~unitmask) == 0;
}

/* mincount of digit-set S (1 or 2 digits, d2 == 0 means |S| == 1) for a
 * single cage, or -1 if the cage's tuples aren't currently valid. */
static int cage_mincount_set(const Cage *cage, int d1, int d2)
{
    if (!cage->tuples_valid) return -1;
    return d2 ? cage->mincount_pair[d1][d2] : cage->mincount[d1];
}

/* Per-tuple occurrence count of S in one specific candidate tuple. */
static int tuple_count_set(const Cage *cage, int t, int d1, int d2)
{
    int i, c = 0;
    for (i = 0; i < cage->n; i++) {
        int v = cage->tuples[t][i];
        if (v == d1 || (d2 && v == d2)) c++;
    }
    return c;
}

static bool apply_group_capacity(Solver *s, int dim, unsigned int unitmask, int k,
                                  int d1, int d2, bool *changed)
{
    int setsize = d2 ? 2 : 1;
    int capacity = k * setsize;
    int demand = 0;
    int ci;

    for (ci = 0; ci < s->ncages; ci++) {
        Cage *cage = &s->cages[ci];
        int mc;
        if (!cage_confined_to(cage, dim, unitmask)) continue;
        mc = cage_mincount_set(cage, d1, d2);
        if (mc < 0) continue; /* unresolved cage: contributes nothing
                                  (safe under-count, never an over-count) */
        demand += mc;
    }

    if (demand > capacity)
        return false; /* genuine contradiction: more forced occurrences
                          of S than the group has room for */

    if (demand == capacity && capacity > 0) {
        /* Rule (a): every group cell not owned by a confined cage
         * cannot hold a value in S. */
        int r;
        for (r = 0; r < s->w; r++) {
            if (!(unitmask & (1u << r))) continue;
            {
                int pos;
                for (pos = 0; pos < s->w; pos++) {
                    int cell = (dim == 0) ? (r * s->w + pos) : (pos * s->w + r);
                    bool owned = false;
                    for (ci = 0; ci < s->ncages; ci++) {
                        Cage *cage = &s->cages[ci];
                        int i;
                        if (!cage_confined_to(cage, dim, unitmask)) continue;
                        if (!cage->tuples_valid) continue;
                        for (i = 0; i < cage->n; i++)
                            if (cage->cells[i] == cell) { owned = true; break; }
                        if (owned) break;
                    }
                    if (owned) continue;
                    {
                        unsigned short smask = (unsigned short)(1u << d1);
                        if (d2) smask |= (unsigned short)(1u << d2);
                        if (s->domain[cell] & smask) {
                            if (s->trace)
                                fprintf(s->trace,
                                        "  group-capacity dim=%d units=%03x "
                                        "S={%d%s%d} demand==capacity==%d -> "
                                        "prune cell (%d,%d)\n",
                                        dim, unitmask, d1, d2 ? "," : "", d2,
                                        capacity, cell_row(s, cell), cell_col(s, cell));
                            if (!remove_from_domain(s, cell, smask, changed))
                                return false;
                        }
                    }
                }
            }
        }
    }

    /* Rule (b): per confined cage, eliminate any surviving tuple whose
     * own contribution to S, combined with every OTHER confined cage's
     * minimum, would exceed capacity. */
    for (ci = 0; ci < s->ncages; ci++) {
        Cage *cage = &s->cages[ci];
        int mc, demand_others, t, kept;
        if (!cage_confined_to(cage, dim, unitmask)) continue;
        if (!cage->tuples_valid) continue;
        mc = cage_mincount_set(cage, d1, d2);
        demand_others = demand - mc;
        if (demand_others + cage->n < capacity)
            continue; /* even this cage's max possible contribution
                         (all n cells in S) can't overflow: skip the scan */

        kept = 0;
        for (t = 0; t < cage->ntuples; t++) {
            int c = tuple_count_set(cage, t, d1, d2);
            if (demand_others + c > capacity) {
                if (s->trace)
                    fprintf(s->trace,
                            "  group-capacity dim=%d units=%03x S={%d%s%d}: "
                            "cage@cell%d tuple %d eliminated (would need %d > %d)\n",
                            dim, unitmask, d1, d2 ? "," : "", d2,
                            cage->cells[0], t, demand_others + c, capacity);
                *changed = true;
                continue; /* drop this tuple */
            }
            if (kept != t)
                memcpy(cage->tuples[kept], cage->tuples[t], (size_t)cage->n);
            kept++;
        }
        if (kept != cage->ntuples) {
            cage->ntuples = kept;
            if (kept == 0)
                return false; /* every tuple eliminated: contradiction */
            /* Keep mincount/mincount_pair in sync with the tuple list
             * we just shrank -- see recompute_mincounts()'s comment for
             * why this can't just wait for the next re-enumeration. */
            recompute_mincounts(s, cage);
        }
    }

    return true;
}

/* Enumerates every k-combination of {0..w-1} as a bitmask, for
 * k == 1, 2 or 3 (MAX_GROUP_SIZE), calling `body` on each. Kept as
 * explicit nested loops (rather than a generic combinatorial
 * iterator) since k's range is small and fixed. */
#define FOR_EACH_GROUP(w, k, maskvar, ...) do { \
    int _u0, _u1, _u2; \
    for (_u0 = 0; _u0 < (w); _u0++) { \
        if ((k) == 1) { \
            unsigned int maskvar = 1u << _u0; \
            __VA_ARGS__ \
            continue; \
        } \
        for (_u1 = _u0 + 1; _u1 < (w); _u1++) { \
            if ((k) == 2) { \
                unsigned int maskvar = (1u << _u0) | (1u << _u1); \
                __VA_ARGS__ \
                continue; \
            } \
            for (_u2 = _u1 + 1; _u2 < (w); _u2++) { \
                unsigned int maskvar = (1u << _u0) | (1u << _u1) | (1u << _u2); \
                __VA_ARGS__ \
            } \
        } \
    } \
} while (0)

static bool run_group_capacity_pass(Solver *s, bool *changed)
{
    int dim, k;
    for (dim = 0; dim < 2; dim++) {
        for (k = 1; k <= MAX_GROUP_SIZE && k <= s->w; k++) {
            bool ok = true;
            FOR_EACH_GROUP(s->w, k, unitmask, {
                int d1, d2;
                for (d1 = 1; d1 <= s->w && ok; d1++) {
                    if (!apply_group_capacity(s, dim, unitmask, k, d1, 0, changed)) {
                        ok = false;
                        break;
                    }
                    if (MAX_SET_SIZE >= 2) {
                        for (d2 = d1 + 1; d2 <= s->w; d2++) {
                            if (!apply_group_capacity(s, dim, unitmask, k, d1, d2, changed)) {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if (!ok) break;
                }
            });
            if (!ok) return false;
        }
    }
    return true;
}

/* ------------------------------------------------------------------
 * Fixpoint driver and public entry points.
 * ------------------------------------------------------------------ */

static bool run_one_pass(Solver *s, bool *changed)
{
    int i;

    /*
     * Every gate below (cage/row/col/group-capacity dirty flags) is
     * purely a performance mechanism, cleared right before the
     * corresponding (expensive) recomputation runs: if that
     * recomputation itself causes further domain changes,
     * mark_dirty() will set the flag again for the cells/cages/rows/
     * cols actually affected, so nothing is ever skipped that still
     * needs redoing -- only work whose result provably can't have
     * changed since it was last computed is skipped.
     */
    for (i = 0; i < s->ncages; i++) {
        if (!s->cages[i].dirty) continue;
        s->cages[i].dirty = false;
        if (!enumerate_cage(s, &s->cages[i]))
            return false;
    }
    for (i = 0; i < s->ncages; i++)
        if (!apply_cage_support(s, &s->cages[i], changed))
            return false;

    for (i = 0; i < s->w; i++) {
        if (!s->row_dirty[i]) continue;
        s->row_dirty[i] = false;
        {
            int cells[MAX_W], k;
            for (k = 0; k < s->w; k++) cells[k] = i * s->w + k;
            if (!revise_unit_subsets(s, cells, s->w, changed))
                return false;
        }
    }
    for (i = 0; i < s->w; i++) {
        if (!s->col_dirty[i]) continue;
        s->col_dirty[i] = false;
        {
            int cells[MAX_W], k;
            for (k = 0; k < s->w; k++) cells[k] = k * s->w + i;
            if (!revise_unit_subsets(s, cells, s->w, changed))
                return false;
        }
    }

    if (s->group_capacity_dirty) {
        s->group_capacity_dirty = false;
        if (!run_group_capacity_pass(s, changed))
            return false;
    }

    return true;
}

/*
 * Repeatedly runs run_one_pass() until a full pass changes nothing --
 * shared by the one-shot and incremental entry points below. rounds, if
 * non-NULL, is incremented once per run_one_pass() call and used only
 * for s->trace's pass numbering.
 *
 * Known limitation: dirty-gating (Cage.dirty/row_dirty/col_dirty/
 * group_capacity_dirty) is a pure performance mechanism, and this file
 * has one confirmed way for it to leave a rare, extremely narrow
 * completeness gap in place -- see recompute_mincounts()'s comment for
 * the specific (and fixed) case of a cage's mincount/mincount_pair going
 * stale after apply_group_capacity()'s rule (b) prunes its tuples
 * in-place. Fixing that closed the overwhelming majority of observed
 * cases in testing (auxiliary/keen-incremental-solver-test.c), but a
 * single further instance of the same general class was observed in
 * fuzz testing at w=9 (roughly 1 in 1500 reveal steps) whose exact
 * trigger was not pinned down. An unconditional "verify with an extra
 * fully-dirty pass" fix was tried and rejected: it can cascade into
 * many full O(cages) passes on exactly the large, heavily-masked boards
 * this dirty-gating exists to keep fast (the same hang class fixed
 * earlier -- see keen_human_solver.c's history), trading a
 * near-un-observable completeness gap for a real, reproducible
 * performance regression. Given this solver is already a deliberately
 * SOUND BUT INCOMPLETE subset of keen_forced_solver() by design (see
 * keen_human_solver.h), never reporting a wrong digit, an occasional
 * missed deduction in a rare cascade is the acceptable side to err on;
 * a wrong digit would not be. If this gap is ever pinned down precisely,
 * the right fix is another targeted recompute at its specific source
 * (as recompute_mincounts() was for the first one), not a blanket
 * re-verification pass here.
 */
static bool converge_solver(Solver *s, int *rounds)
{
    bool changed;

    do {
        changed = false;
        if (rounds) {
            ++*rounds;
            if (s->trace) fprintf(s->trace, "-- pass %d --\n", *rounds);
        }
        if (!run_one_pass(s, &changed))
            return false;
    } while (changed);

    return true;
}

char *keen_human_solver_trace(int w, DSF *dsf, unsigned long *clues, FILE *trace)
{
    Solver s;
    int a = w * w;
    int i;
    char *out;
    int rounds = 0;

    memset(&s, 0, sizeof(s));
    s.w = w;
    s.a = a;
    s.trace = trace;
    for (i = 0; i < a; i++) s.domain[i] = FULL_MASK(w);

    s.ncages = build_cages(w, dsf, clues, &s.cages);
    build_owners(&s);
    for (i = 0; i < w; i++) s.row_dirty[i] = s.col_dirty[i] = true;
    s.group_capacity_dirty = true;

    if (!converge_solver(&s, &rounds)) {
        for (i = 0; i < s.ncages; i++) free(s.cages[i].tuples);
        free(s.cages);
        return NULL;
    }

    out = malloc((size_t)a + 1);
    out[a] = '\0';
    for (i = 0; i < a; i++)
        out[i] = (popcount16(s.domain[i]) == 1)
                     ? (char)('0' + lowest_value(s.domain[i]))
                     : '.';

    for (i = 0; i < s.ncages; i++) free(s.cages[i].tuples);
    free(s.cages);
    return out;
}

char *keen_human_solver(int w, DSF *dsf, unsigned long *clues)
{
    return keen_human_solver_trace(w, dsf, clues, NULL);
}

/* ====================================================================
 * Incremental / warm-start API.
 *
 * Motivation: puzzle-generation clue-grouping planning calls this
 * solver over and over against the SAME fixed cage geometry, each time
 * with one more cage's clue revealed than last time -- e.g. "what's
 * forced with just cage 3 visible?", then "...cages 3 and 7?", then
 * "...3, 7 and 1?", and so on until every cage is visible. The one-shot
 * API above redoes every bit of propagation from scratch on every such
 * call, including re-enumerating every cage's tuples and rerunning the
 * whole fixpoint loop, even though almost nothing changed between two
 * consecutive calls.
 *
 * Soundness of warm-starting: revealing an additional cage's clue can
 * only ever SHRINK the set of valid grid completions (it adds a
 * constraint, never removes one), so every domain narrowing, forced
 * cell, and cage-tuple elimination made from a smaller revealed-cage
 * set remains valid forever once more cages are revealed on top of it
 * -- nothing this solver ever concludes needs to be retracted as more
 * clues appear. This is exactly why the one-shot solver above has no
 * undo trail at all: every removal is already permanent. Warm-starting
 * simply keeps one persistent Solver alive across many reveals instead
 * of rebuilding it, and lets the existing dirty-tracking machinery
 * (mark_dirty(), Cage.dirty, row_dirty/col_dirty, group_capacity_dirty)
 * do exactly what it already does in the one-shot loop: skip any
 * recomputation whose result can't have changed.
 *
 * Cages start out with op == C_NO_CLUE, exactly like any cage this file
 * has never been able to enumerate a clue for -- enumerate_cage()
 * already treats C_NO_CLUE as "no constraint, no tuples, always
 * succeeds" (see its top few lines), so an unrevealed real cage simply
 * contributes nothing anywhere, with zero special-casing needed outside
 * this section.
 *
 * The one piece of real bookkeeping this needs is the synthetic
 * row/column residual-sum cages (technique 4 in the file header): which
 * cells they cover and what they sum to depends on ALL CURRENTLY
 * REVEALED addition cages contained in that row/column, so revealing
 * one more such cage can shrink an already-active residual cage,
 * activate one that had no coverage at all yet, or (if a cage exactly
 * completes a row/column's coverage) deactivate one entirely. Cage
 * geometry (which real cage is entirely contained in which row/column,
 * i.e. home_row[]/home_col[] below) is fixed at creation time and never
 * changes, so recomputing one affected row's or column's residual cage
 * is a cheap O(w) scan over that unit's real cages -- structurally
 * identical to (and exactly reproducing) what build_cages() computes in
 * one shot, just re-run for one unit at a time instead of all 2w of
 * them. This keeps the incremental design simple and obviously correct
 * (it's the same formula, just re-evaluated) rather than trying to
 * patch a residual cage's cell list/value in place.
 * ==================================================================== */

struct KeenHumanIncSolver {
    Solver s;
    int real_ncages;
    int row_residual_idx[MAX_W];   /* cage index of row r's residual slot */
    int col_residual_idx[MAX_W];   /* cage index of col c's residual slot */
    int *home_row;  /* [real_ncages]; -1 if cage i isn't entirely in one row */
    int *home_col;  /* [real_ncages]; -1 if cage i isn't entirely in one col */
};

/* Marks `cg` itself, and every row/column touching one of its cells,
 * dirty -- used whenever a cage's op/value/cell-list changes directly
 * (as opposed to mark_dirty(), which is keyed off a CELL's domain
 * changing). Also unconditionally marks group_capacity_dirty, for the
 * same reason mark_dirty() does: a single cage's tuples changing can in
 * principle affect the group-capacity demand sum for many groups at
 * once, so there is no cheaper sound thing to do than reconsider it. */
static void mark_cage_and_units_dirty(Solver *s, Cage *cg)
{
    int k;
    cg->dirty = true;
    for (k = 0; k < cg->n; k++) {
        s->row_dirty[cell_row(s, cg->cells[k])] = true;
        s->col_dirty[cell_col(s, cg->cells[k])] = true;
    }
    s->group_capacity_dirty = true;
}

/* Recomputes row r's (dim==0) or column u's (dim==1) residual cage from
 * scratch, from the CURRENT op/value of every real cage entirely
 * contained in that unit -- exactly reproducing the relevant slice of
 * build_cages()'s one-shot computation (see there), just re-run for one
 * unit instead of all of them. O(real_ncages + w); cheap, and always
 * exactly correct regardless of reveal order, since it depends only on
 * the current (order-independent) set of revealed ADD cages contained
 * in this unit, never on how it got there. */
static void recompute_residual(KeenHumanIncSolver *inc, int dim, int u)
{
    Solver *s = &inc->s;
    Cage *rc = &s->cages[dim == 0 ? inc->row_residual_idx[u]
                                   : inc->col_residual_idx[u]];
    bool covered[MAX_W];
    int pos, coveredcount = 0, i;
    long ssum = 0;

    for (pos = 0; pos < s->w; pos++) covered[pos] = false;

    for (i = 0; i < inc->real_ncages; i++) {
        Cage *cg = &s->cages[i];
        int home = (dim == 0) ? inc->home_row[i] : inc->home_col[i];
        int k;
        if (cg->op != C_ADD) continue;
        if (home != u) continue;
        for (k = 0; k < cg->n; k++) {
            int cell = cg->cells[k];
            int p = (dim == 0) ? cell_col(s, cell) : cell_row(s, cell);
            if (!covered[p]) { covered[p] = true; coveredcount++; }
        }
        ssum += cg->value;
    }

    if (coveredcount == 0 || coveredcount == s->w) {
        if (rc->activated) mark_cage_and_units_dirty(s, rc);
        rc->n = 0;
        rc->value = 0;
        rc->activated = false;
        rc->rowmask = rc->colmask = 0;
        return;
    }

    {
        int total = s->w * (s->w + 1) / 2;
        rc->n = 0;
        for (pos = 0; pos < s->w; pos++) {
            if (covered[pos]) continue;
            rc->cells[rc->n++] = (dim == 0) ? (u * s->w + pos)
                                             : (pos * s->w + u);
        }
        rc->value = total - ssum;
        rc->activated = true;
        rc->rowmask = rc->colmask = 0;
        for (i = 0; i < rc->n; i++) {
            rc->rowmask |= 1u << cell_row(s, rc->cells[i]);
            rc->colmask |= 1u << cell_col(s, rc->cells[i]);
        }
        mark_cage_and_units_dirty(s, rc);
    }
}

/*
 * Creates a fresh incremental solver for a puzzle's fixed cage geometry
 * (w, dsf), with every real cage's clue unrevealed (op == C_NO_CLUE) --
 * equivalent to keen_human_solver()'s state before any reveal, and
 * cheap (no propagation work happens yet, since C_NO_CLUE cages and
 * full domains give the fixpoint nothing to do). Returns NULL only on
 * allocation failure or a malformed dsf (defensive; should not happen
 * for a real puzzle's own dsf). Cages are numbered 0..real_ncages-1 in
 * exactly the same canonical order build_cages() already uses (DSF-root
 * -first-encountered while scanning cell index 0..a-1), so cage_index
 * values here match the ordering the rest of the codebase already
 * relies on (descriptor encode/decode); residual-cage slots live at
 * fixed indices real_ncages..real_ncages+2*w-1 and are never addressed
 * by a caller directly.
 */
KeenHumanIncSolver *keen_human_solver_create(int w, DSF *dsf)
{
    int a = w * w;
    int i, j, n, real_ncages = 0;
    KeenHumanIncSolver *inc;
    Solver *s;

    for (i = 0; i < a; i++)
        if (dsf_minimal(dsf, i) == i)
            real_ncages++;

    inc = calloc(1, sizeof(*inc));
    if (!inc) return NULL;
    inc->real_ncages = real_ncages;
    inc->home_row = malloc(sizeof(int) * (size_t)real_ncages);
    inc->home_col = malloc(sizeof(int) * (size_t)real_ncages);

    s = &inc->s;
    s->w = w;
    s->a = a;
    for (i = 0; i < a; i++) s->domain[i] = FULL_MASK(w);

    s->ncages = real_ncages + 2 * w;
    s->cages = calloc((size_t)s->ncages, sizeof(Cage));

    for (n = i = 0; i < a; i++) {
        if (dsf_minimal(dsf, i) == i) {
            Cage *cg = &s->cages[n];
            cg->op = C_NO_CLUE;
            cg->value = 0;
            cg->n = 0;
            for (j = 0; j < a; j++)
                if (dsf_minimal(dsf, j) == i)
                    cg->cells[cg->n++] = j;
            n++;
        }
    }
    assert(n == real_ncages);

    /* Structural home_row/home_col, and rowmask/colmask, per real cage
     * -- fixed for the lifetime of this solver, computed once here. */
    for (i = 0; i < real_ncages; i++) {
        Cage *cg = &s->cages[i];
        int k;
        int r0 = cell_row(s, cg->cells[0]), c0 = cell_col(s, cg->cells[0]);
        bool samerow = true, samecol = true;
        cg->rowmask = cg->colmask = 0;
        for (k = 0; k < cg->n; k++) {
            int r = cell_row(s, cg->cells[k]), c = cell_col(s, cg->cells[k]);
            if (r != r0) samerow = false;
            if (c != c0) samecol = false;
            cg->rowmask |= 1u << r;
            cg->colmask |= 1u << c;
        }
        inc->home_row[i] = samerow ? r0 : -1;
        inc->home_col[i] = samecol ? c0 : -1;
    }

    /* Reserve 2*w residual slots at fixed indices, all inactive. */
    for (i = 0; i < w; i++) {
        inc->row_residual_idx[i] = real_ncages + i;
        inc->col_residual_idx[i] = real_ncages + w + i;
    }
    for (i = real_ncages; i < s->ncages; i++) {
        Cage *rc = &s->cages[i];
        rc->op = (int)C_ADD;
        rc->value = 0;
        rc->n = 0;
        rc->is_residual = true;
        rc->activated = false;
    }

    /* Tuple storage for every cage (real and residual alike). */
    for (i = 0; i < s->ncages; i++) {
        s->cages[i].tuples = malloc(sizeof(*s->cages[i].tuples) * MAX_TUPLES);
        s->cages[i].tuples_valid = false;
        s->cages[i].ntuples = 0;
        s->cages[i].dirty = true;
    }

    /* owners[]: for every cell, its real cage plus its row- and
     * column-residual slots -- fixed forever, regardless of which of
     * those residual slots is currently activated, since an inactive
     * slot is just a 0-cell cage rather than a nonexistent one (see
     * Cage.activated's comment). This is what lets residual-cage
     * activation/deactivation over time never need owners[] touched
     * again. */
    for (i = 0; i < a; i++) s->nowners[i] = 0;
    for (i = 0; i < real_ncages; i++) {
        Cage *cg = &s->cages[i];
        int k;
        for (k = 0; k < cg->n; k++) {
            int cell = cg->cells[k];
            s->owners[cell][s->nowners[cell]++] = i;
        }
    }
    for (i = 0; i < a; i++) {
        int r = cell_row(s, i), c = cell_col(s, i);
        s->owners[i][s->nowners[i]++] = inc->row_residual_idx[r];
        s->owners[i][s->nowners[i]++] = inc->col_residual_idx[c];
    }

    for (i = 0; i < w; i++) s->row_dirty[i] = s->col_dirty[i] = true;
    s->group_capacity_dirty = true;
    s->trace = NULL;

    if (!converge_solver(s, NULL)) {
        keen_human_solver_destroy(inc);
        return NULL;
    }

    return inc;
}

/*
 * Reveals cage_index's clue (op/value), reuses every previously-computed
 * domain/tuple/dirty-flag as its starting point, and reruns the fixpoint
 * loop until nothing more changes -- doing only the marginal propagation
 * work this one reveal's consequences require, never redoing work from
 * earlier reveals. Idempotent: revealing an already-revealed cage again
 * is a no-op that returns true without touching any state. Returns false
 * iff the revealed clue set is now outright contradictory (mirrors the
 * one-shot solver returning NULL); the solver's internal state is left
 * as-is in that case (get a fresh one via keen_human_solver_create() to
 * continue).
 */
bool keen_human_solver_reveal(KeenHumanIncSolver *inc, int cage_index,
                               int op, long value)
{
    Solver *s = &inc->s;
    Cage *cg;

    assert(cage_index >= 0 && cage_index < inc->real_ncages);
    cg = &s->cages[cage_index];

    if (cg->op != C_NO_CLUE)
        return true; /* already revealed: idempotent no-op */

    cg->op = op;
    cg->value = value;
    mark_cage_and_units_dirty(s, cg);

    if (op == (int)C_ADD) {
        if (inc->home_row[cage_index] >= 0)
            recompute_residual(inc, 0, inc->home_row[cage_index]);
        if (inc->home_col[cage_index] >= 0)
            recompute_residual(inc, 1, inc->home_col[cage_index]);
    }

    return converge_solver(s, NULL);
}

/*
 * Cheap read-only snapshot of the current forced-cells state -- just
 * reads s.domain[], no propagation work at all. Same format as
 * keen_human_solver()'s return value (a newly allocated (w*w+1)-byte
 * string, digit or '.' per cell in row-major order; free with sfree()).
 */
char *keen_human_solver_snapshot(KeenHumanIncSolver *inc)
{
    Solver *s = &inc->s;
    char *out = malloc((size_t)s->a + 1);
    int i;
    out[s->a] = '\0';
    for (i = 0; i < s->a; i++)
        out[i] = (popcount16(s->domain[i]) == 1)
                     ? (char)('0' + lowest_value(s->domain[i]))
                     : '.';
    return out;
}

int keen_human_solver_cage_count(KeenHumanIncSolver *inc)
{
    return inc->real_ncages;
}

int keen_human_solver_cage_size(KeenHumanIncSolver *inc, int cage_index)
{
    assert(cage_index >= 0 && cage_index < inc->real_ncages);
    return inc->s.cages[cage_index].n;
}

int keen_human_solver_cage_cell(KeenHumanIncSolver *inc, int cage_index, int k)
{
    assert(cage_index >= 0 && cage_index < inc->real_ncages);
    assert(k >= 0 && k < inc->s.cages[cage_index].n);
    return inc->s.cages[cage_index].cells[k];
}

void keen_human_solver_destroy(KeenHumanIncSolver *inc)
{
    int i;
    if (!inc) return;
    if (inc->s.cages) {
        for (i = 0; i < inc->s.ncages; i++)
            free(inc->s.cages[i].tuples);
        free(inc->s.cages);
    }
    free(inc->home_row);
    free(inc->home_col);
    free(inc);
}

