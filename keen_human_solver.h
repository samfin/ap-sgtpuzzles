/*
 * keen_human_solver.h: "human-style" partial solver for Keen, used to
 * decide which cells of a partially-clued puzzle can be filled in using
 * only non-bifurcating logical deduction -- the kind of reasoning a
 * person doing the puzzle with pencil and paper could actually perform,
 * as opposed to keen_forced_solver()'s exact-but-search-based notion of
 * "forced" (see keen_forced_solver.h).
 *
 * Why this exists alongside keen_forced_solver(): keen_forced_solver()
 * is mathematically exact -- a cell is reported iff EVERY completion
 * consistent with the visible clues agrees on it, even if the only way
 * to prove that is a full backtracking search with no visible logical
 * "reason". That is the right tool for verifying a puzzle has a unique
 * solution, but the wrong tool for deciding what a *player* should be
 * asked to deduce next: a clue arrangement can force a cell in the exact
 * sense while offering no accessible reasoning path to it at all, which
 * playtesting showed makes some progressive-reveal stages feel like
 * guessing. keen_human_solver() answers a different, deliberately
 * weaker question: which cells can be pinned down by repeatedly applying
 * a fixed toolkit of human techniques (no trial assignments, no search,
 * no "assume X and look for a contradiction")? Its output is always a
 * SOUND SUBSET of keen_forced_solver()'s -- see the .c file's header for
 * the full list of techniques and why each one is safe.
 *
 * keen_forced_solver() itself is untouched by this addition and remains
 * available/compiled for anything that still wants the exact notion.
 */
#ifndef KEEN_HUMAN_SOLVER_H
#define KEEN_HUMAN_SOLVER_H

#include "puzzles.h"
#include "latin.h"

/*
 * Same calling convention as keen_forced_solver() (see that header for
 * the parameter documentation, which is identical here): w/dsf/clues
 * describe a partially-clued Keen puzzle, and the return value is a
 * newly allocated (w*w + 1)-byte string, one char per cell in row-major
 * order -- a digit for a cell this solver's human-style techniques pin
 * down, '.' for one they don't (which includes every cell that is only
 * forced via search, even though keen_forced_solver() would report it) --
 * or NULL if the given clues are outright inconsistent. Free with sfree().
 */
char *keen_human_solver(int w, DSF *dsf, unsigned long *clues);

/*
 * Identical computation, but if `trace` is non-NULL, prints one line per
 * rule application to it (which rule, which cells/cages/digits, and what
 * it concluded) -- intended for tests and for debugging/explaining a
 * specific deduction, not for production use. Passing trace == NULL here
 * is exactly equivalent to calling keen_human_solver() above (which is
 * implemented in terms of this function).
 */
char *keen_human_solver_trace(int w, DSF *dsf, unsigned long *clues, FILE *trace);

/*
 * -------------------------------------------------------------------
 * Incremental / warm-start API
 * -------------------------------------------------------------------
 *
 * For a caller (puzzle-generation clue-grouping planning) that solves
 * the SAME fixed cage geometry repeatedly, each time with one more
 * cage's clue revealed than last time, the one-shot keen_human_solver()
 * above redoes all propagation work from scratch on every call. This
 * API instead keeps one persistent solver instance alive per puzzle:
 * create it once from the puzzle's cage geometry (with every clue
 * unrevealed), then reveal cages one at a time in any order, each
 * reveal doing only the marginal propagation work its consequences
 * require by reusing everything already deduced from previously
 * revealed cages. This is sound because revealing more clues only ever
 * shrinks the set of valid completions -- see keen_human_solver.c's
 * "Incremental / warm-start API" section for the full argument.
 *
 * cage_index in every call below refers to a REAL cage, numbered
 * 0..keen_human_solver_cage_count()-1 in exactly the canonical order
 * build_cages() (see keen_human_solver.c) already uses -- the same
 * ordering the rest of the codebase relies on for descriptor
 * encode/decode.
 */
typedef struct KeenHumanIncSolver KeenHumanIncSolver;

/* Creates a fresh incremental solver for puzzle geometry (w, dsf), with
 * every cage's clue unrevealed. Returns NULL only on allocation failure
 * or a malformed dsf. Free with keen_human_solver_destroy(). */
KeenHumanIncSolver *keen_human_solver_create(int w, DSF *dsf);

/* Reveals cage_index's clue (op is one of the same C_ADD/C_MUL/C_SUB/
 * C_DIV values used elsewhere; value is its target). Idempotent:
 * revealing an already-revealed cage again is a harmless no-op.
 * Returns false iff the revealed clue set is now outright
 * contradictory (in which case this solver instance should be
 * discarded; further calls on it are not supported). */
bool keen_human_solver_reveal(KeenHumanIncSolver *inc, int cage_index,
                               int op, long value);

/* Cheap read-only snapshot of the current forced-cells state, in the
 * same format keen_human_solver() returns (free with sfree()). Does no
 * propagation work -- safe to call as often as wanted between
 * reveals. */
char *keen_human_solver_snapshot(KeenHumanIncSolver *inc);

/* Cage geometry accessors (fixed for the lifetime of the solver,
 * regardless of which cages have been revealed) -- lets a caller that
 * only has this solver instance (and not the original dsf/clues) still
 * enumerate real cages and their cells, e.g. to decide what to reveal
 * next. */
int keen_human_solver_cage_count(KeenHumanIncSolver *inc);
int keen_human_solver_cage_size(KeenHumanIncSolver *inc, int cage_index);
int keen_human_solver_cage_cell(KeenHumanIncSolver *inc, int cage_index, int k);

void keen_human_solver_destroy(KeenHumanIncSolver *inc);

#endif
