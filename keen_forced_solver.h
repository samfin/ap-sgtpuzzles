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

#endif
