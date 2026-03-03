#include <stdio.h>
#include <string.h>
#include "tinyexpr.h"
#include "common.h"

int main(void) {
    char input[512];

    puts("TinyExpr REPL");
    puts("Type an expression and press Enter.");
    puts("Vector examples: <1,2,3>, 2*<1,2,3>, |<1,2,3>|, dot(<1,0,0>,<0,1,0>), cross(<1,0,0>,<0,1,0>)");
    puts("Projection order is function(B,A): proj(B,A), oproj(B,A), comp(B,A), ocomp(B,A)");
    puts("Unit vector: unit(<3,4,0>)");
    puts("Type 'exit' or 'quit' to end.");

    while (1) {
        int error = 0;
        te_value result;

        printf("> ");
        if (!fgets(input, sizeof(input), stdin)) {
            putchar('\n');
            break;
        }

        input[strcspn(input, "\r\n")] = '\0';
        if (input[0] == '\0') {
            continue;
        }
        if (strcmp(input, "exit") == 0 || strcmp(input, "quit") == 0) {
            break;
        }

        result = te_interp_value(input, 0, 0, &error);
        if (error != 0) {
            printf("parse error at character %d\n", error);
            continue;
        }
        disp(result);
    }

    return 0;
}
