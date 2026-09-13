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
 * This technique set is a direct port of the reasoning keen.c's own
 * difficulty-graded solver() uses at DIFF_EXTREME (built on latin.c's
 * generic Latin-square solving framework), MINUS its one bifurcating
 * step (recursion/guessing, which starts only at DIFF_UNREASONABLE and
 * is deliberately never used here) and MINUS forcing chains
 * (latin_solver_forcing) -- everything else solver() can prove without
 * guessing, this file can prove too, plus one technique solver() itself
 * does not have (residual-sum cages, item 5 below):
 *
 *  1. Cage candidate elimination (per-cell support): a value not used
 *     by ANY surviving complete assignment of a cage's own cells is
 *     removed from that cell -- equivalent to solver_clue_candidate()'s
 *     DIFF_NORMAL mode in keen.c, computed here from the cage's
 *     explicit tuple list instead of an inline recursive enumeration.
 *  2. Per-cage pointing (cage->row and cage->column restriction): for a
 *     cage and one row (or column) it touches, if some digit appears in
 *     that row's slice of the cage in EVERY surviving tuple, that digit
 *     must appear somewhere in the cage's part of the row -- so it can
 *     be eliminated from the rest of the row outside the cage. Direct
 *     port of solver_clue_candidate()'s DIFF_HARD mode (there expressed
 *     as a bitmap-AND over candidate layouts; here as a bitmask AND
 *     over cage->tuples[]).
 *  2b. Per-unit claiming (row/column->cage restriction, the REVERSE of
 *     technique 2): for a unit (row or column) u and a cage C with one
 *     or more cells in u, if some digit is possible somewhere in C's
 *     cells-in-u but nowhere else in u, then C's cells-in-u must
 *     collectively contain that digit no matter how C is completed --
 *     so any surviving tuple of C that fails to place the digit at one
 *     of those cells can be eliminated. This is genuinely NOT part of
 *     solver_clue_candidate()/latin_solver_diff_set()/
 *     latin_solver_forcing(): confirmed by running keen.c's own
 *     solver() directly (not just this port) on hand-worked examples a
 *     human solves this way, at every difficulty up to and including
 *     DIFF_EXTREME (forcing chains included) -- solver() provably
 *     cannot complete them without recursion (DIFF_UNREASONABLE, i.e.
 *     guessing), even though the deduction needs only one cage plus
 *     ordinary Latin row/column reasoning and no hypothetical at all.
 *     So unlike every other numbered technique here, this one is not a
 *     port of anything in keen.c/latin.c -- it is a new,
 *     independently-verified-sound rule, added because solver()'s own
 *     technique set has a real gap here that a human solver has no
 *     reason to inherit (see the project's progress notes for the
 *     worked examples and the direct-solver() test that established
 *     this). Implemented by mutating cage->tuples[]/ntuples in place,
 *     like enumerate_cage() -- see apply_cage_claiming()'s own comment
 *     for why that is still safe under this file's no-stale-cache
 *     discipline.
 *  3. Row/column naked and hidden SUBSETS, exhaustively, of every size
 *     from 1 up to floor(w/2) (checking beyond that adds nothing new,
 *     by duality: a naked subset of size m is the same fact as a
 *     hidden subset of size w-m elsewhere in the unit): m cells whose
 *     combined candidates are exactly m values ("naked"), or m values
 *     whose combined candidate cells are exactly m cells ("hidden"),
 *     let every other cell/value in the unit be pruned accordingly.
 *     Port of latin_solver_diff_set()'s non-extreme (row-only /
 *     column-only) mode -- w <= 9 keeps the 2^w subset enumeration this
 *     uses cheap regardless of size.
 *  4. Whole-grid single-digit row/column set elimination ("X-wing" and
 *     its larger generalisations, swordfish/jellyfish/...): for one
 *     digit d, if d's still-possible columns among some set of k whole
 *     rows number exactly k, d can be eliminated from those columns in
 *     every OTHER row (and symmetrically, rows <-> columns). Port of
 *     latin_solver_diff_set()'s extreme mode -- the one piece of
 *     DIFF_EXTREME reasoning that ignores cages entirely, operating
 *     purely on the Latin-square (each digit once per row/column)
 *     constraint.
 *  5. Synthetic residual-sum cages: for a row or column with one or
 *     more visible addition cages entirely contained in it, the
 *     leftover cells must sum to (the unit's fixed total) minus (those
 *     cages' targets) -- folded in as one more addition cage over
 *     exactly those leftover cells, so it gets the exact same
 *     candidate-elimination and pointing treatment (techniques 1-2
 *     above) as any other cage. This is NOT part of solver()/latin.c
 *     (see the comment above get_forced_cells() in keen.c, which
 *     documents solver()/DIFF_EXTREME lacking any notion of "this
 *     row's cells always sum to a fixed constant") -- it is this file's
 *     one addition beyond what was ported, kept because dropping it
 *     would be a strict regression for exactly the puzzles it was
 *     originally added to catch (e.g. "three cells sum to 10, next two
 *     sum to 7" forcing a width-6 row's last cell to 4).
 *
 * Deliberately NOT ported: forcing chains (latin_solver_forcing) --
 * DIFF_EXTREME's remaining technique, a BFS over two-candidate-cell
 * chains. Everything above already goes well beyond what the previous
 * (group-capacity-based) version of this file could do; forcing chains
 * are left as a possible future addition rather than risk their
 * considerably trickier bookkeeping under this rewrite's time budget --
 * see the project's progress notes for this session's scope decision.
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
 * Every individual rule above is a valid logical inference (including
 * 2b, independently verified sound even though it is not a port), so
 * nothing this file ever reports as forced can be wrong: it is always a
 * SOUND SUBSET of what keen_forced_solver() would report (verified for
 * this
 * codebase by a randomised regression test that runs both solvers over
 * many random partial-clue states of real generated puzzles and checks
 * that every digit this solver reports agrees with the exact solver --
 * see auxiliary/keen-human-solver-test.c). It is not complete: there
 * exist forced cells (provable only via full backtracking search, or via
 * a forcing chain -- see "Deliberately NOT ported" above) that this file
 * will report as undetermined ('.') even though they are mathematically
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
     * Meaningful only for a synthetic residual-sum cage (see
     * build_cages()), used only by the incremental/warm-start API below
     * (KeenHumanIncSolver): true iff this residual slot currently covers
     * at least one leftover cell (n > 0). A residual cage that has never
     * been activated (no contained ADD cage revealed yet in its
     * row/column) and one that was activated but has since been fully
     * covered again (every position now covered by some revealed
     * contained ADD cage) are both represented as n == 0 and behave
     * identically to every downstream consumer (apply_cage_support,
     * apply_cage_pointing, revise_unit_subsets's caller) -- a 0-cell
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

    /* Set whenever ANY cell's domain changes anywhere on the grid; only
     * cleared right before the whole-grid single-digit set-elimination
     * pass (technique 4, apply_extreme_digit_sets()) runs, since that
     * technique isn't confined to one cage/row/column the way the
     * others are and so has no narrower dirty granularity to exploit --
     * a pure performance gate, same contract as row_dirty/col_dirty/
     * Cage.dirty (see mark_dirty()'s comment). */
    bool grid_dirty;

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
    s->grid_dirty = true;
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
 * overflow (tuples_valid = false), the tuple list is discarded for this
 * round -- NOT truncated -- so that no rule ever draws a conclusion from
 * a partial enumeration. A partial list would be unsound in general: a
 * cell-support removal based on "no *scanned* tuple uses this value"
 * could wrongly discard a value whose only support was in a tuple
 * enumeration never reached, which could cascade into reporting a wrong
 * digit. Skipping the cage entirely this round has no such risk: it
 * only costs completeness (a missed deduction, to be retried once other
 * rules shrink the domains and the same enumeration becomes cheap
 * enough to finish), never soundness.
 */
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
 * Row/column naked & hidden subset elimination, EXHAUSTIVE over every
 * size from 1 to floor(n/2) -- port of latin_solver_diff_set()'s
 * non-extreme mode (latin.c), which achieves the same result via a
 * different algorithm (a "rectangle of zeroes" search over a boolean
 * matrix); this version instead enumerates subsets directly as
 * bitmasks against this file's own domain[] representation, which is
 * simpler here and just as cheap: n, s->w <= 9 always (Keen's maximum
 * grid size), so a 2^n or 2^w enumeration is at most 512 iterations.
 * Checking sizes beyond floor(n/2) adds nothing new: a naked subset of
 * size m is the exact same fact as a hidden subset of size n-m
 * elsewhere in the same unit, so running both the naked and hidden
 * loops up to floor(n/2) each already covers every size with no gaps.
 * ------------------------------------------------------------------ */

static bool revise_unit_subsets(Solver *s, const int *cells, int n, bool *changed)
{
    int maxm = n / 2;
    unsigned int subset;

    /* ---- naked subsets: every nonempty subset of the n cells,
     * of popcount 1..maxm ---- */
    for (subset = 1; subset < (1u << n); subset++) {
        int m = popcount16((unsigned short)subset);
        if (m < 1 || m > maxm) continue;
        {
            unsigned short u = 0;
            int k;
            for (k = 0; k < n; k++)
                if (subset & (1u << k)) u |= s->domain[cells[k]];
            if (popcount16(u) != m) continue;
            /* This m-cell subset's candidates are exactly these m
             * values: remove them from every other cell in the unit. */
            for (k = 0; k < n; k++) {
                if (subset & (1u << k)) continue;
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
    }

    /* ---- hidden subsets: every nonempty subset of the w digits,
     * of popcount 1..maxm ---- */
    for (subset = 1; subset < (1u << s->w); subset++) {
        int m = popcount16((unsigned short)subset);
        if (m < 1 || m > maxm) continue;
        {
            /* subset's bit (d-1) <-> digit d, so shift left 1 to land
             * on domain[]'s own bit-per-digit convention (bit 0 unused,
             * digit d is bit d). */
            unsigned short vmask = (unsigned short)(subset << 1);
            unsigned short cellmask_bits = 0; /* which of the n cells
                                                  (by index into cells[])
                                                  hold >=1 of these
                                                  values */
            int k, cellcount = 0;
            for (k = 0; k < n; k++) {
                if (s->domain[cells[k]] & vmask) {
                    cellmask_bits |= (unsigned short)(1u << k);
                    cellcount++;
                }
            }
            if (cellcount != m) continue;
            /* These m values only ever appear (between them) in
             * exactly these m cells: restrict those cells to only
             * these values. */
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
    }

    /* Basic Latin-square consistency check: every value must still
     * have at least one candidate cell (a value with zero candidates
     * anywhere in the unit is an outright contradiction), and no two
     * cells may be pinned (domain size 1) to the same value. This is
     * subsumed logically by the subset code above whenever it runs to
     * completion, but is re-checked directly here as a cheap explicit
     * safety net regardless. */
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
 * Per-cage pointing (technique 2 in the file header). Port of
 * solver_clue_candidate()'s DIFF_HARD mode in keen.c: there, this is
 * computed by ANDing a bitmap across every candidate layout found
 * during an inline recursive enumeration; here, the same AND is taken
 * directly over the already-enumerated cage->tuples[].
 * ------------------------------------------------------------------ */

static bool apply_cage_pointing(Solver *s, Cage *cage, bool *changed)
{
    int dim;

    if (!cage->tuples_valid || cage->ntuples == 0) return true;

    for (dim = 0; dim < 2; dim++) {
        unsigned int unitset = (dim == 0) ? cage->rowmask : cage->colmask;
        int u;
        for (u = 0; u < s->w; u++) {
            if (!(unitset & (1u << u))) continue;
            {
                /* must: AND, over every surviving tuple, of the digits
                 * that tuple assigns within this cage's slice of unit u.
                 * A digit surviving the AND is guaranteed to appear
                 * somewhere in cage-cells-in-unit-u no matter which
                 * completion is real, so it can be eliminated from the
                 * rest of unit u outside the cage. */
                unsigned short must = FULL_MASK(s->w);
                int t;
                for (t = 0; t < cage->ntuples && must; t++) {
                    unsigned short here = 0;
                    int i;
                    for (i = 0; i < cage->n; i++) {
                        int cell = cage->cells[i];
                        int cu = (dim == 0) ? cell_row(s, cell) : cell_col(s, cell);
                        if (cu == u)
                            here |= (unsigned short)(1u << cage->tuples[t][i]);
                    }
                    must &= here;
                }
                if (!must) continue;

                {
                    int pos;
                    for (pos = 0; pos < s->w; pos++) {
                        int cell = (dim == 0) ? (u * s->w + pos) : (pos * s->w + u);
                        bool incage = false;
                        int i;
                        for (i = 0; i < cage->n; i++)
                            if (cage->cells[i] == cell) { incage = true; break; }
                        if (incage) continue;
                        if (s->domain[cell] & must) {
                            if (s->trace)
                                fprintf(s->trace,
                                        "  pointing dim=%d unit=%d cage@cell%d: "
                                        "must=%04x -> prune cell (%d,%d)\n",
                                        dim, u, cage->cells[0], (unsigned)must,
                                        cell_row(s, cell), cell_col(s, cell));
                            if (!remove_from_domain(s, cell, must, changed))
                                return false;
                        }
                    }
                }
            }
        }
    }

    return true;
}

/* ------------------------------------------------------------------
 * Per-unit claiming (technique 2b in the file header): the reverse
 * direction of pointing. For a unit u (row or column) and a cage with
 * one or more cells in u, take the union of domains of the cage's
 * cells IN u ("cage_mask") and the union of domains of every other
 * cell in u ("other_mask"). Any digit in cage_mask but not in
 * other_mask cannot go anywhere in unit u except inside this cage's
 * cells-in-u -- so every surviving tuple that fails to place that
 * digit at one of those cells is impossible and can be dropped.
 *
 * NOT a port -- see the file header's technique 2b entry for why this
 * genuinely goes beyond solver()/latin.c's own technique set (verified
 * by testing keen.c's actual solver() directly), not just this port of
 * it.
 *
 * Unlike apply_cage_pointing (which only ever removes from domain[]),
 * this mutates cage->tuples[]/ntuples in place, the same way
 * enumerate_cage() does. That is safe here for the same reason it is
 * safe there: nothing in this file caches any derived fact about a
 * cage's tuple list except what apply_cage_support() and
 * apply_cage_pointing() recompute FRESH from tuples[] every single
 * round (see converge_solver()'s comment on why the previous,
 * group-capacity-based version of this file could go stale in place
 * and this one cannot) -- so narrowing tuples[] here is picked up
 * correctly by both of those the next time they run, with nothing left
 * behind to go stale. A cage whose tuples shrink to zero here is a
 * genuine contradiction (no assignment of the cage's own cells can be
 * reconciled with a unit it touches), handled exactly like
 * enumerate_cage() finding zero tuples.
 * ------------------------------------------------------------------ */

static bool apply_cage_claiming(Solver *s, Cage *cage, bool *changed)
{
    int dim;

    if (!cage->tuples_valid || cage->ntuples == 0) return true;

    for (dim = 0; dim < 2; dim++) {
        unsigned int unitset = (dim == 0) ? cage->rowmask : cage->colmask;
        int u;
        for (u = 0; u < s->w; u++) {
            if (!(unitset & (1u << u))) continue;

            {
                unsigned short cage_mask = 0, other_mask = 0, confined;
                int i, pos;

                for (i = 0; i < cage->n; i++) {
                    int cell = cage->cells[i];
                    int cu = (dim == 0) ? cell_row(s, cell) : cell_col(s, cell);
                    if (cu == u) cage_mask |= s->domain[cell];
                }
                for (pos = 0; pos < s->w; pos++) {
                    int cell = (dim == 0) ? (u * s->w + pos) : (pos * s->w + u);
                    bool incage = false;
                    for (i = 0; i < cage->n; i++)
                        if (cage->cells[i] == cell) { incage = true; break; }
                    if (incage) continue;
                    other_mask |= s->domain[cell];
                }

                confined = (unsigned short)(cage_mask & ~other_mask);
                if (!confined) continue;

                {
                    int t, keep = 0;
                    for (t = 0; t < cage->ntuples; t++) {
                        unsigned short here = 0;
                        for (i = 0; i < cage->n; i++) {
                            int cell = cage->cells[i];
                            int cu = (dim == 0) ? cell_row(s, cell) : cell_col(s, cell);
                            if (cu == u)
                                here |= (unsigned short)(1u << cage->tuples[t][i]);
                        }
                        if ((here & confined) == confined) {
                            if (keep != t)
                                memcpy(cage->tuples[keep], cage->tuples[t],
                                       (size_t)cage->n);
                            keep++;
                        }
                    }
                    if (keep < cage->ntuples) {
                        if (s->trace)
                            fprintf(s->trace,
                                    "  claiming dim=%d unit=%d cage@cell%d: "
                                    "confined=%04x -> tuples %d -> %d\n",
                                    dim, u, cage->cells[0], (unsigned)confined,
                                    cage->ntuples, keep);
                        cage->ntuples = keep;
                        *changed = true;
                        if (cage->ntuples == 0) return false; /* contradiction */
                    }
                }
            }
        }
    }

    return true;
}

/* ------------------------------------------------------------------
 * Whole-grid single-digit row/column set elimination (technique 4 in
 * the file header: "X-wing" and its larger generalisations). Port of
 * latin_solver_diff_set()'s extreme mode. Unlike every other technique
 * in this file, this one is cage-agnostic -- it only uses the
 * Latin-square constraint (each digit exactly once per row/column) --
 * so it is checked once per digit against the whole grid rather than
 * per cage or per single unit.
 * ------------------------------------------------------------------ */

static bool apply_extreme_digit_sets(Solver *s, int digit, bool *changed)
{
    unsigned short rowposmask[MAX_W]; /* bit c set iff (r,c) can hold digit */
    unsigned short colposmask[MAX_W]; /* bit r set iff (r,c) can hold digit */
    unsigned short bit = (unsigned short)(1u << digit);
    int maxm = s->w / 2;
    int r, c;
    unsigned int subset;

    for (r = 0; r < s->w; r++) {
        unsigned short m = 0;
        for (c = 0; c < s->w; c++)
            if (s->domain[r * s->w + c] & bit) m |= (unsigned short)(1u << c);
        rowposmask[r] = m;
    }
    for (c = 0; c < s->w; c++) {
        unsigned short m = 0;
        for (r = 0; r < s->w; r++)
            if (s->domain[r * s->w + c] & bit) m |= (unsigned short)(1u << r);
        colposmask[c] = m;
    }

    /* A subset of rows whose digit's possible columns (union over the
     * subset) number exactly the subset's own size confines digit to
     * those columns within those rows -- eliminate it from those
     * columns in every OTHER row. (Size-1 is an ordinary hidden single
     * already covered by revise_unit_subsets(); this technique's real
     * value starts at size 2, the classic "X-wing".) */
    for (subset = 1; subset < (1u << s->w); subset++) {
        int m = popcount16((unsigned short)subset);
        if (m < 1 || m > maxm) continue;
        {
            unsigned short u = 0;
            int k;
            for (k = 0; k < s->w; k++)
                if (subset & (1u << k)) u |= rowposmask[k];
            if (popcount16(u) != m) continue;
            for (r = 0; r < s->w; r++) {
                if (subset & (1u << r)) continue;
                for (c = 0; c < s->w; c++) {
                    int cell;
                    if (!(u & (1u << c))) continue;
                    cell = r * s->w + c;
                    if (s->domain[cell] & bit) {
                        if (s->trace)
                            fprintf(s->trace,
                                    "  extreme-set digit=%d rows=%03x -> "
                                    "prune cell (%d,%d)\n",
                                    digit, subset, r, c);
                        if (!remove_from_domain(s, cell, bit, changed))
                            return false;
                    }
                }
            }
        }
    }

    /* Mirror image: a subset of COLUMNS confining digit to that many
     * rows -- eliminate it from those rows in every other column. */
    for (subset = 1; subset < (1u << s->w); subset++) {
        int m = popcount16((unsigned short)subset);
        if (m < 1 || m > maxm) continue;
        {
            unsigned short u = 0;
            int k;
            for (k = 0; k < s->w; k++)
                if (subset & (1u << k)) u |= colposmask[k];
            if (popcount16(u) != m) continue;
            for (c = 0; c < s->w; c++) {
                if (subset & (1u << c)) continue;
                for (r = 0; r < s->w; r++) {
                    int cell;
                    if (!(u & (1u << r))) continue;
                    cell = r * s->w + c;
                    if (s->domain[cell] & bit) {
                        if (s->trace)
                            fprintf(s->trace,
                                    "  extreme-set digit=%d cols=%03x -> "
                                    "prune cell (%d,%d)\n",
                                    digit, subset, r, c);
                        if (!remove_from_domain(s, cell, bit, changed))
                            return false;
                    }
                }
            }
        }
    }

    return true;
}

static bool run_extreme_pass(Solver *s, bool *changed)
{
    int d;
    for (d = 1; d <= s->w; d++)
        if (!apply_extreme_digit_sets(s, d, changed))
            return false;
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
    for (i = 0; i < s->ncages; i++)
        if (!apply_cage_pointing(s, &s->cages[i], changed))
            return false;
    for (i = 0; i < s->ncages; i++)
        if (!apply_cage_claiming(s, &s->cages[i], changed))
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

    if (s->grid_dirty) {
        s->grid_dirty = false;
        if (!run_extreme_pass(s, changed))
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
 * Dirty-gating (Cage.dirty/row_dirty/col_dirty/grid_dirty) is a pure
 * performance mechanism. Only enumerate_cage() (rebuild a cage's tuples
 * from its cells' current domains) is gated by Cage.dirty; the three
 * consumers of cage->tuples[] -- apply_cage_support, apply_cage_pointing,
 * and apply_cage_claiming (which, like enumerate_cage(), mutates
 * tuples[]/ntuples in place rather than only reading them) -- all run
 * unconditionally every round regardless of any dirty flag, so a tuple
 * list narrowed by apply_cage_claiming() is always picked up by the
 * other two on their very next call, with no cached fact anywhere that
 * could go stale relative to it; only enumerate_cage()'s own rebuild
 * needs to skip cages it has no new domain information for, which
 * Cage.dirty already ensures happens only when nothing could change.
 * revise_unit_subsets/apply_extreme_digit_sets read domain[] directly
 * with no cached intermediate state of their own. Unlike the previous
 * (group-capacity-based) version of this file, no rule anywhere caches
 * a derived fact about a cage (such as the old mincount[]/mincount_pair[])
 * that could go stale after another rule mutates tuples[] out from under
 * it -- which is exactly the bug class that made this file's predecessor
 * lossy (see part 12's progress notes). So there is no known way left
 * for this dirty-gating to skip a computation whose result could
 * actually have changed.
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
    s.grid_dirty = true;

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
 * (mark_dirty(), Cage.dirty, row_dirty/col_dirty, grid_dirty) do
 * exactly what it already does in the one-shot loop: skip any
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
 * row/column residual-sum cages (technique 5 in the file header): which
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
 * changing). Also unconditionally marks grid_dirty, for the same
 * reason mark_dirty() does: a single cage's tuples changing can in
 * principle affect apply_extreme_digit_sets()'s whole-grid computation
 * for many digits at once, so there is no cheaper sound thing to do
 * than reconsider it. */
static void mark_cage_and_units_dirty(Solver *s, Cage *cg)
{
    int k;
    cg->dirty = true;
    for (k = 0; k < cg->n; k++) {
        s->row_dirty[cell_row(s, cg->cells[k])] = true;
        s->col_dirty[cell_col(s, cg->cells[k])] = true;
    }
    s->grid_dirty = true;
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
    s->grid_dirty = true;
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

