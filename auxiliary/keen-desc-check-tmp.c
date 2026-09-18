#include <stdio.h>
#include <string.h>

#include "../puzzles.h"

extern const struct game thegame;

int main(void)
{
    char line[8192];

    while (fgets(line, sizeof(line), stdin)) {
        char *nl = strchr(line, '\n');
        if (nl) *nl = '\0';

        char *sep = strchr(line, '|');
        if (!sep) { printf("ERROR malformed line: %s\n", line); continue; }
        *sep = '\0';
        const char *paramstr = line;
        const char *desc = sep + 1;

        game_params *params = thegame.default_params();
        thegame.decode_params(params, paramstr);

        char *result = thegame.solve_partial(params, desc);
        if (!result) {
            printf("ERROR solve_partial returned NULL for params=%s desc=%s\n", paramstr, desc);
        } else {
            int n = (int)strlen(result), forced = 0, i;
            for (i = 0; i < n; i++) if (result[i] != '0') forced++;
            printf("OK %d/%d %s\n", forced, n, result);
            sfree(result);
        }

        thegame.free_params(params);
    }

    return 0;
}
