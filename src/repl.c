#include <stdio.h>
#include <string.h>
#include "tinyexpr.h"

static void print_value(te_value value) {
    switch (value.kind) {
        case TE_VAL_VEC3:
            printf("<%.6f, %.6f, %.6f>\n", value.vec3.x, value.vec3.y, value.vec3.z);
            break;
        case TE_VAL_SCALAR:
            printf("%.6f\n", value.scalar);
            break;
        default:
            printf("error\n");
            break;
    }
}

int main(void) {
    char input[512];

    puts("TinyExpr REPL");
    puts("Type an expression and press Enter.");
    puts("Vector examples: <1,2,3>, 2*<1,2,3>, |<1,2,3>|, dot(<1,0,0>,<0,1,0>), cross(<1,0,0>,<0,1,0>)");
    puts("Projection order is function(B,A): proj(B,A), oproj(B,A), comp(B,A), ocomp(B,A)");
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
        print_value(result);
    }

    return 0;
}
