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

#endif
