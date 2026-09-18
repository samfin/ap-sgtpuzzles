/*
 * Native (non-WASM) smoke test for keen.c's new thegame.current_grid
 * hook and its plumbing through midend_current_grid(). Compiled
 * directly against keen.c + the core library (which now includes
 * midend.c) + nullfe.c, exactly like keen-solve-partial-test.c but
 * additionally exercising the real midend this time, since
 * current_grid's whole point is reading LIVE midend state rather than
 * a freshly-constructed one.
 *
 * Two levels are checked:
 *
 *   1) Direct, no-midend level (mirrors keen-solve-partial-test.c's
 *      style): thegame.current_grid() called straight on states
 *      produced by new_game()/execute_move(), confirming it reports
 *      exactly the digits actually entered -- an empty grid reads as
 *      all '0's, a single "Rx,y,n" move sets exactly that cell and no
 *      other, and it never performs any solving of its own (entering
 *      a wrong digit is reported back verbatim, not corrected).
 *
 *   2) Through midend_current_grid(), with a real midend: confirms
 *      the dispatch (me->ourgame->current_grid on
 *      me->states[me->statepos-1].state) is wired correctly end to
 *      end -- an empty grid immediately after midend_new_game() is
 *      all '0's, and after midend_solve() it matches the real
 *      solution exactly, the same one thegame.solve() itself
 *      produces.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "../puzzles.h"

extern const struct game thegame;

static int failures = 0;

static void check(int cond, const char *msg)
{
    if (!cond) {
        printf("FAIL: %s\n", msg);
        failures++;
    }
}

static void run_direct_level(const char *paramstr, int w, const char *seed)
{
    game_params *params;
    random_state *rs;
    char *aux, *desc;
    game_state *state, *next;
    char *grid;
    int a;

    rs = random_new(seed, strlen(seed));
    params = thegame.default_params();
    thegame.decode_params(params, paramstr);

    aux = NULL;
    desc = thegame.new_desc(params, rs, &aux, false);
    state = thegame.new_game(NULL, params, desc);
    a = w * w;

    printf("--- direct level: params=%s seed=%s desc=%s ---\n",
           paramstr, seed, desc);

    /* A freshly-generated state has nothing entered. */
    grid = thegame.current_grid(state);
    {
        int i, allzero = 1;
        for (i = 0; i < a; i++) if (grid[i] != '0') allzero = 0;
        check(allzero, "fresh game_state's current_grid isn't all zeros");
        check((int)strlen(grid) == a, "current_grid length != w*w");
    }
    sfree(grid);

    /* Enter a single digit via a real "R" move (the same move format
     * the UI itself generates -- see interpret_move()) and confirm
     * current_grid reflects exactly that one cell, verbatim, with no
     * solving performed -- even if the digit is deliberately wrong. */
    {
        char movebuf[32];
        int wrong_digit = (w >= 2) ? 2 : 1;   /* doesn't need to be correct */
        sprintf(movebuf, "R%d,%d,%d", 0, 0, wrong_digit);
        next = thegame.execute_move(state, movebuf);
        check(next != NULL, "execute_move(\"R0,0,n\") returned NULL");

        grid = thegame.current_grid(next);
        check(grid[0] == '0' + wrong_digit,
              "current_grid didn't reflect the single entered digit at (0,0)");
        {
            int i, othersclear = 1;
            for (i = 1; i < a; i++) if (grid[i] != '0') othersclear = 0;
            check(othersclear, "current_grid set cells other than the one entered");
        }
        sfree(grid);
        thegame.free_game(next);
    }

    /* Full solve via thegame.solve(), then current_grid() must match
     * it exactly (this is the real answer, not a re-derivation). */
    {
        const char *solve_err = NULL;
        char *solved_move = thegame.solve(state, state, aux, &solve_err);
        game_state *solved_state;

        check(solved_move && solved_move[0] == 'S',
              "thegame.solve() didn't return an 'S' move");
        solved_state = thegame.execute_move(state, solved_move);
        check(solved_state != NULL, "execute_move on the solve string failed");

        grid = thegame.current_grid(solved_state);
        check(strncmp(grid, solved_move + 1, a) == 0,
              "current_grid after a full solve doesn't match the solve string");
        sfree(grid);

        thegame.free_game(solved_state);
        sfree(solved_move);
    }

    thegame.free_game(state);
    thegame.free_params(params);
    sfree(desc);
    sfree(aux);
    random_free(rs);
}

static void run_midend_level(const char *paramstr, const char *seed)
{
    midend *me;
    char *fullseed, *gameid;
    const char *err;
    char *grid;

    printf("--- midend level: params=%s seed=%s ---\n", paramstr, seed);

    me = midend_new(NULL, &thegame, NULL, NULL);

    fullseed = snewn(strlen(paramstr) + strlen(seed) + 2, char);
    sprintf(fullseed, "%s#%s", paramstr, seed);
    err = midend_game_id(me, fullseed);
    check(err == NULL, "midend_game_id on a seed string failed");
    sfree(fullseed);

    midend_new_game(me);

    /* Nothing entered yet. */
    grid = midend_current_grid(me);
    check(grid != NULL, "midend_current_grid returned NULL right after midend_new_game");
    if (grid) {
        int i, allzero = 1, len = (int)strlen(grid);
        for (i = 0; i < len; i++) if (grid[i] != '0') allzero = 0;
        check(allzero, "midend_current_grid isn't all zeros on a fresh game");
        sfree(grid);
    }

    /* Solve it via the midend's own solve entry point, then confirm
     * midend_current_grid() reports the real solution. */
    gameid = midend_get_game_id(me);
    err = midend_solve(me);
    check(err == NULL, "midend_solve failed");

    grid = midend_current_grid(me);
    check(grid != NULL, "midend_current_grid returned NULL after midend_solve");
    if (grid) {
        /* Cross-check against solve_partial_desc() (already verified
         * elsewhere) with every clue visible -- both should now agree
         * exactly, since the puzzle is fully and correctly solved. */
        char *desc = strchr(gameid, ':') + 1;
        game_params *params = thegame.default_params();
        char *parampart = dupstr(gameid);
        *strchr(parampart, ':') = '\0';
        thegame.decode_params(params, parampart);
        {
            char *partial = thegame.solve_partial(params, desc);
            check(partial != NULL, "solve_partial failed on the fully-clued descriptor");
            if (partial) {
                check(strcmp(grid, partial) == 0,
                      "midend_current_grid after midend_solve doesn't match solve_partial's fully-clued answer");
                sfree(partial);
            }
        }
        thegame.free_params(params);
        sfree(parampart);
        sfree(grid);
    }

    sfree(gameid);
    midend_free(me);
}

int main(void)
{
    struct { const char *params; int w; const char *seed; } cases[] = {
        {"4de", 4, "seed-a"},
        {"5de", 5, "seed-b"},
        {"6de", 6, "seed-c"},
        {"6dn", 6, "seed-d"},
        {"6dh", 6, "seed-f"},
        {"6dx", 6, "seed-g"},
        {"9dn", 9, "seed-h"},
        {"9dh", 9, "seed-i"},
    };
    int i;

    for (i = 0; i < (int)(sizeof(cases)/sizeof(cases[0])); i++) {
        run_direct_level(cases[i].params, cases[i].w, cases[i].seed);
        run_midend_level(cases[i].params, cases[i].seed);
    }

    printf("\n=== %s: %d total failure(s) across %d puzzles ===\n",
           failures ? "FAILED" : "ALL PASSED", failures,
           (int)(sizeof(cases)/sizeof(cases[0])));
    return failures ? 1 : 0;
}
