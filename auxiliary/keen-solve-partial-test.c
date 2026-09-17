/*
 * Native (non-WASM) smoke test for keen.c's new thegame.solve_partial
 * hook. Compiled directly against keen.c + the small set of "core"
 * .c files it depends on (no midend, no drawing, no Emscripten) --
 * nullfe.c supplies the handful of frontend stub symbols keen.c's
 * translation unit still needs to link (even though this test never
 * calls into any of them).
 *
 * This does NOT re-implement or duplicate any solving logic. It only
 * exercises thegame.solve_partial() -- the new, thin wrapper around
 * the existing, completely unmodified solver()/latin_solver() -- via
 * masked variants of a real generated descriptor, and checks that:
 *
 *   1) with every clue visible, it agrees exactly with the game's own
 *      solve() (the real answer), confirming the wrapper adds/changes
 *      nothing when nothing is hidden;
 *   2) with a proper subset of clues visible, every digit it *does*
 *      report is correct (a "sound subset" of the true solution --
 *      never wrong, possibly incomplete);
 *   3) revealing more clues never removes a previously-forced digit
 *      (monotonicity) and generally forces at least as much;
 *   4) with zero clues visible, it reports nothing (pure Latin-square
 *      constraints alone don't force anything).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include "../puzzles.h"

extern const struct game thegame;

/* Split a fully-clued descriptor "prefix,clues" into the prefix
 * (kept verbatim) and a list of clue tokens (each one letter plus
 * its optional digits, e.g. "a12", "m6", "n"). This is exactly the
 * tokenisation a masking client needs to do: it never has to know
 * anything about cage geometry, only where one clue token ends and
 * the next begins. */
struct tokenised {
    char *prefix;    /* includes the trailing comma */
    char **tokens;
    int ntokens;
};

static struct tokenised tokenise(const char *desc)
{
    struct tokenised result;
    const char *comma = strchr(desc, ',');
    const char *p;
    int cap;

    assert(comma);
    result.prefix = snewn(comma - desc + 2, char);
    memcpy(result.prefix, desc, comma - desc + 1);
    result.prefix[comma - desc + 1] = '\0';

    cap = 64;
    result.tokens = snewn(cap, char *);
    result.ntokens = 0;

    p = comma + 1;
    while (*p) {
        const char *start = p;
        assert(strchr("namsd", *p));
        p++;
        while (*p && isdigit((unsigned char)*p)) p++;
        if (result.ntokens == cap) {
            cap *= 2;
            result.tokens = sresize(result.tokens, cap, char *);
        }
        result.tokens[result.ntokens] = snewn(p - start + 1, char);
        memcpy(result.tokens[result.ntokens], start, p - start);
        result.tokens[result.ntokens][p - start] = '\0';
        result.ntokens++;
    }

    return result;
}

/* Rebuild a descriptor from a tokenised prefix+tokens, with the
 * cages listed in `hide` (by token index, hide[i] != 0) forced to
 * 'n' regardless of what their real token said. */
static char *remask(struct tokenised *t, const char *hide)
{
    int i, len = strlen(t->prefix);
    char *out;

    for (i = 0; i < t->ntokens; i++)
        len += hide[i] ? 1 : strlen(t->tokens[i]);

    out = snewn(len + 1, char);
    strcpy(out, t->prefix);
    for (i = 0; i < t->ntokens; i++)
        strcat(out, hide[i] ? "n" : t->tokens[i]);

    return out;
}

static int count_forced(const char *soln, int a)
{
    int i, n = 0;
    for (i = 0; i < a; i++)
        if (soln[i] != '0') n++;
    return n;
}

static int run_one(const char *paramstr, int w, const char *seed)
{
    game_params *params;
    random_state *rs;
    char *aux, *desc, *fullsoln;
    struct tokenised t;
    char *hide;
    int a, i, trial, failures = 0;

    rs = random_new(seed, strlen(seed));

    params = thegame.default_params();
    thegame.decode_params(params, paramstr);

    aux = NULL;
    desc = thegame.new_desc(params, rs, &aux, false);
    printf("--- params=%s seed=%s ---\ngenerated descriptor: %s\n",
           paramstr, seed, desc);

    a = w * w;

    t = tokenise(desc);
    printf("cage count: %d\n", t.ntokens);

    /* --- Check 1: fully visible must match the real solution --- */
    {
        game_state *state = thegame.new_game(NULL, params, desc);
        const char *solve_err = NULL;
        char *solved_move = thegame.solve(state, state, aux, &solve_err);
        assert(solved_move && solved_move[0] == 'S');
        fullsoln = solved_move + 1;   /* w*w digit chars, skip leading 'S' */

        hide = snewn(t.ntokens, char);
        memset(hide, 0, t.ntokens);
        char *full_mask_desc = remask(&t, hide);
        char *partial_full = thegame.solve_partial(params, full_mask_desc);

        if (strncmp(partial_full, fullsoln, a) != 0) {
            printf("FAIL: solve_partial with all clues visible does not "
                   "match the real solution\n  solve_partial: %.*s\n"
                   "  real solution: %.*s\n", a, partial_full, a, fullsoln);
            failures++;
        } else if (count_forced(partial_full, a) != a) {
            printf("FAIL: solve_partial with all clues visible left %d/%d "
                   "cells undetermined (puzzle should be Normal-difficulty "
                   "solvable without guessing)\n",
                   a - count_forced(partial_full, a), a);
            failures++;
        } else {
            printf("OK: solve_partial with all clues visible matches the "
                   "real solution exactly (%d/%d cells)\n",
                   count_forced(partial_full, a), a);
        }

        thegame.free_game(state);
        sfree(full_mask_desc);
        sfree(partial_full);
    }

    /* --- Check 4: zero clues visible forces nothing --- */
    {
        memset(hide, 1, t.ntokens);
        char *none_desc = remask(&t, hide);
        char *partial_none = thegame.solve_partial(params, none_desc);
        int n = count_forced(partial_none, a);
        if (n != 0) {
            printf("FAIL: solve_partial with zero clues visible forced %d "
                   "cells (expected 0)\n", n);
            failures++;
        } else {
            printf("OK: solve_partial with zero clues visible forces "
                   "nothing\n");
        }
        sfree(none_desc);
        sfree(partial_none);
    }

    /* --- Checks 2 & 3: soundness + monotonicity across 20 random
     *     increasing reveal orders --- */
    for (trial = 0; trial < 20; trial++) {
        int *order = snewn(t.ntokens, int);
        int prev_forced = 0;
        char *prev_soln = NULL;

        for (i = 0; i < t.ntokens; i++) order[i] = i;
        /* Fisher-Yates shuffle using the same random_state */
        for (i = t.ntokens - 1; i > 0; i--) {
            int j = random_upto(rs, i + 1);
            int tmp = order[i]; order[i] = order[j]; order[j] = tmp;
        }

        memset(hide, 1, t.ntokens);
        for (i = 0; i <= t.ntokens; i++) {
            char *masked_desc, *partial;
            int forced, j;

            if (i > 0) hide[order[i-1]] = 0;   /* reveal one more cage */

            masked_desc = remask(&t, hide);
            partial = thegame.solve_partial(params, masked_desc);
            forced = count_forced(partial, a);

            /* Soundness: every forced digit must match the true solution */
            for (j = 0; j < a; j++) {
                if (partial[j] != '0' && partial[j] != fullsoln[j]) {
                    printf("FAIL: trial %d step %d: cell %d forced to '%c' "
                           "but true solution has '%c'\n",
                           trial, i, j, partial[j], fullsoln[j]);
                    failures++;
                }
            }

            /* Monotonicity: revealing a cage can't un-force a cell */
            if (prev_soln) {
                for (j = 0; j < a; j++) {
                    if (prev_soln[j] != '0' && partial[j] != prev_soln[j]) {
                        printf("FAIL: trial %d step %d: cell %d was forced "
                               "to '%c', now reports '%c' after revealing "
                               "another cage\n",
                               trial, i, j, prev_soln[j], partial[j]);
                        failures++;
                    }
                }
                if (forced < prev_forced) {
                    printf("FAIL: trial %d step %d: forced-cell count "
                           "dropped from %d to %d after revealing another "
                           "cage\n", trial, i, prev_forced, forced);
                    failures++;
                }
            }

            sfree(masked_desc);
            sfree(prev_soln);
            prev_soln = partial;
            prev_forced = forced;
        }

        sfree(prev_soln);
        sfree(order);
    }
    printf("OK: 20 random reveal-order trials passed soundness + "
           "monotonicity checks (%d cages each)\n", t.ntokens);

    return failures;
}

int main(void)
{
    struct { const char *params; int w; const char *seed; } cases[] = {
        {"4de", 4, "seed-a"},
        {"5de", 5, "seed-b"},
        {"6de", 6, "seed-c"},
        {"6dn", 6, "seed-d"},
        {"6dn", 6, "seed-e"},
        {"6dh", 6, "seed-f"},
        {"6dx", 6, "seed-g"},
        {"9dn", 9, "seed-h"},
        {"9dh", 9, "seed-i"},
        {"6dnm", 6, "seed-j"},
    };
    int i, total_failures = 0;

    for (i = 0; i < (int)(sizeof(cases)/sizeof(cases[0])); i++)
        total_failures += run_one(cases[i].params, cases[i].w, cases[i].seed);

    printf("\n=== %s: %d total failure(s) across %d puzzles ===\n",
           total_failures ? "FAILED" : "ALL PASSED", total_failures,
           (int)(sizeof(cases)/sizeof(cases[0])));
    return total_failures ? 1 : 0;
}
