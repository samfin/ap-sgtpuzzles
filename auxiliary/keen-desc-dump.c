/*
 * Tiny native helper, companion to keen-solve-partial-test.c: generates
 * real Keen descriptors and prints them one per line as
 *   <w>|<params>|<descriptor>
 * so a client-side (JS) descriptor parser can be round-trip-tested
 * against real output from the game's own new_desc(), without needing
 * to reimplement or guess at generation. Doesn't touch or duplicate
 * any solving logic -- this only calls the existing, unmodified
 * new_desc().
 */

#include <stdio.h>
#include <string.h>

#include "../puzzles.h"

extern const struct game thegame;

int main(void)
{
    struct { const char *params; int w; const char *seed; } cases[] = {
        {"4de", 4, "dump-a"},
        {"5de", 5, "dump-b"},
        {"6de", 6, "dump-c"},
        {"6dn", 6, "dump-d"},
        {"6dn", 6, "dump-e"},
        {"6dh", 6, "dump-f"},
        {"6dx", 6, "dump-g"},
        {"9dn", 9, "dump-h"},
        {"9dh", 9, "dump-i"},
        {"6dnm", 6, "dump-j"},
        {"3de", 3, "dump-k"},
        {"9de", 9, "dump-l"},
    };
    int i;

    for (i = 0; i < (int)(sizeof(cases)/sizeof(cases[0])); i++) {
        game_params *params;
        random_state *rs;
        char *aux, *desc;

        rs = random_new(cases[i].seed, strlen(cases[i].seed));
        params = thegame.default_params();
        thegame.decode_params(params, cases[i].params);

        aux = NULL;
        desc = thegame.new_desc(params, rs, &aux, false);

        printf("%d|%s|%s\n", cases[i].w, cases[i].params, desc);
    }

    return 0;
}
