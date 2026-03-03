#include <stdio.h>
#include "tinyexpr.h"
#include "common.h"

double evaluate_expression(char* expression_text, double a, int* error_ptr) {
    double x = a;
    te_variable vars[] = {{"x", &x}};
    te_expr* expression_ptr = te_compile(expression_text, vars, 1, error_ptr);
    return te_eval(expression_ptr);
}

double derivative(char* expression_text, double a) {
    int error;
    double delta_x = 0.00001;

    double y2 = evaluate_expression(expression_text, (a + 0.0001), &error);
    double y1 = evaluate_expression(expression_text, (a - 0.0001), &error);

    return (y2 - y1) / (2 * delta_x);
}

double integral(char* expression_text, double a, double b) {
    int n = 10000;
    if (n % 2) n++;

    double h = (b - a) / n;
    int error;

    double sum = evaluate_expression(expression_text, a, &error) + evaluate_expression(expression_text, b, &error);

    for (int i = 1; i < n; i++) {
        double x = a + i * h;

        if (i % 2 == 0) {
            sum += 2.0 * evaluate_expression(expression_text, x, &error);
        } else {
            sum += 4.0 * evaluate_expression(expression_text, x, &error);
        }
    }

    return (h / 3.0) * sum;
}

void main() {
    const char *labels[] = {
        "vector literal",
        "scalar * vector",
        "vector * scalar",
        "vector / scalar",
        "magnitude |v|",
        "unit(v)",
        "dot(B, A)",
        "cross(B, A)",
        "proj(B, A)",
        "oproj(B, A)",
        "comp(B, A)",
        "ocomp(B, A)"
    };

    const char *exprs[] = {
        "<1,2,3>",
        "2*<1,2,3>",
        "<1,2,3>*2",
        "<6,8,10>/2",
        "|<3,4,12>|",
        "unit(<3,4,0>)",
        "dot(<2,0,0>,<3,4,0>)",
        "cross(<1,0,0>,<0,1,0>)",
        "proj(<2,0,0>,<3,4,0>)",
        "oproj(<2,0,0>,<3,4,0>)",
        "comp(<2,0,0>,<3,4,0>)",
        "ocomp(<2,0,0>,<3,4,0>)"
    };

    int total = (int)(sizeof(exprs) / sizeof(exprs[0]));

    for (int i = 0; i < total; i++) {
        int error = 0;
        te_value result = te_interp_value(exprs[i], 0, 0, &error);

        printf("%s: %s -> ", labels[i], exprs[i]);
        if (error != 0 || result.kind == TE_VAL_ERROR) {
            printf("evaluation failed (error=%d)\n", error);
            continue;
        }
        disp(result);
    }
}
