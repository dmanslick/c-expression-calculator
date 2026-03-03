// SPDX-License-Identifier: Zlib
/*
 * TINYEXPR - Tiny recursive descent parser and evaluation engine in C
 *
 * Copyright (c) 2015-2020 Lewis Van Winkle
 *
 * http://CodePlea.com
 *
 * This software is provided 'as-is', without any express or implied
 * warranty. In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 * claim that you wrote the original software. If you use this software
 * in a product, an acknowledgement in the product documentation would be
 * appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 * misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 */

#ifndef TINYEXPR_H
#define TINYEXPR_H


#ifdef __cplusplus
extern "C" {
#endif



typedef struct te_value te_value;

typedef struct te_expr {
    int type;
    union {double value; const double *bound; const te_value *value_bound; const void *function;};
    void *parameters[1];
} te_expr;

typedef struct {
    double x;
    double y;
    double z;
} te_vec3;

typedef enum {
    TE_VAL_SCALAR = 0,
    TE_VAL_VEC3,
    TE_VAL_ERROR
} te_value_kind;

struct te_value {
    te_value_kind kind;
    union {
        double scalar;
        te_vec3 vec3;
    };
};


enum {
    TE_VARIABLE = 0,

    TE_FUNCTION0 = 8, TE_FUNCTION1, TE_FUNCTION2, TE_FUNCTION3,
    TE_FUNCTION4, TE_FUNCTION5, TE_FUNCTION6, TE_FUNCTION7,

    TE_CLOSURE0 = 16, TE_CLOSURE1, TE_CLOSURE2, TE_CLOSURE3,
    TE_CLOSURE4, TE_CLOSURE5, TE_CLOSURE6, TE_CLOSURE7,

    TE_FLAG_PURE = 32
};

typedef struct te_variable {
    const char *name;
    const void *address;
    int type;
    void *context;
} te_variable;

typedef struct te_binding {
    const char *name;
    te_value value;
} te_binding;



/* Parses the input expression, evaluates it, and frees it. */
/* Returns NaN on error. */
double te_interp(const char *expression, int *error);

/* Parses the input expression and binds variables. */
/* Returns NULL on error. */
te_expr *te_compile(const char *expression, const te_variable *variables, int var_count, int *error);
te_expr *te_compile_value(const char *expression, const te_binding *bindings, int bind_count, int *error);

/* Evaluates the expression. */
double te_eval(const te_expr *n);
te_value te_eval_value(const te_expr *n);

/* Prints debugging information on the syntax tree. */
void te_print(const te_expr *n);

/* Frees the expression. */
/* This is safe to call on NULL pointers. */
void te_free(te_expr *n);

/* Parses, evaluates, and frees an expression with scalar/vector bindings. */
te_value te_interp_value(const char *expression, const te_binding *bindings, int bind_count, int *error);


#ifdef __cplusplus
}
#endif

#endif /*TINYEXPR_H*/
