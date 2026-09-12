/*
 * keen_forced_solver.h: fast specialized solver for determining which
 * cells of a partially-clued Keen puzzle are uniquely forced.
 *
 * A cell is "forced" iff every complete Keen solution consistent with the
 * currently-visible (non-masked) cages assigns that cell the same value.
 * This is the exact mathematical notion, not an approximation based on
 * whichever human-style techniques happen to be implemented -- it is
 * always correct regardless of how the visible cages are arranged.
 */
#ifndef KEEN_FORCED_SOLVER_H
#define KEEN_FORCED_SOLVER_H

#include "puzzles.h"
#include "latin.h"

/*
 * w: grid width (cells are a w*w grid, row-major, digits 1..w).
 * dsf: cage structure, dsf_new_min-style (same DSF keen.c's own solver()
 *      uses) -- dsf_minimal(dsf, i) == i identifies cage representatives.
 * clues: per-cell array, meaningful only at each cage's representative
 *      index, encoding (op | value) with op one of the C_NO_CLUE / C_ADD /
 *      C_SUB / C_MUL / C_DIV bit patterns used by keen.c (duplicated in
 *      this module's .c file, since keen.c's #defines are file-local).
 *
 * Returns a newly allocated (w*w + 1)-byte string (row-major, one char per
 * cell: a digit for a forced cell, '.' for one that is not uniquely
 * determined), or NULL if the given clues are outright inconsistent
 * (no valid completion at all -- should not happen for a masked-down
 * relaxation of an already-solvable puzzle, but handled defensively).
 * Free the result with sfree().
 */
char *keen_forced_solver(int w, DSF *dsf, unsigned long *clues);

/*
 * Same as keen_forced_solver() above, but if budget_aborted_out is
 * non-NULL, *budget_aborted_out is set to true iff this call's internal
 * node-visit budget (see the .c file's TOTAL_NODE_BUDGET) ran out before
 * every cell could be conclusively settled one way or the other, and
 * false if the answer is fully exhaustive. This matters because a '.'
 * in the returned string normally means "proven NOT uniquely forced" --
 * but when *budget_aborted_out comes back true, some of those '.'s may
 * simply be cells this call ran out of budget before it could check,
 * i.e. not yet proven either way. Every digit actually reported (every
 * non-'.' cell) is unaffected by this and remains a hard proof either
 * way, budget or no budget: only the meaning of '.' is weakened when
 * budget_aborted_out comes back true. Pass NULL to ignore this
 * (equivalent to keen_forced_solver() above, which is implemented in
 * terms of this function). Added so callers that need to know how much
 * to trust an absence of forced cells -- such as this project's own
 * regression tests, which cross-check keen_human_solver()'s output
 * against this solver's -- can tell a genuine "not forced" apart from
 * "budget ran out before we could tell".
 */
char *keen_forced_solver_ex(int w, DSF *dsf, unsigned long *clues,
                             bool *budget_aborted_out);

#endif
