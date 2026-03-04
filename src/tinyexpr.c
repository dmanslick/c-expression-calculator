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

/* COMPILE TIME OPTIONS */

/* Exponentiation associativity:
For a^b^c = (a^b)^c and -a^b = (-a)^b do nothing.
For a^b^c = a^(b^c) and -a^b = -(a^b) uncomment the next line.*/
/* #define TE_POW_FROM_RIGHT */

/* Logarithms
For log = base 10 log do nothing
For log = natural log uncomment the next line. */
/* #define TE_NAT_LOG */

#include "tinyexpr.h"
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <limits.h>

#ifndef NAN
#define NAN (0.0/0.0)
#endif

#ifndef INFINITY
#define INFINITY (1.0/0.0)
#endif


typedef double (*te_fun2)(double, double);

enum {
    TOK_NULL = TE_CLOSURE7+1, TOK_ERROR, TOK_END, TOK_SEP,
    TOK_OPEN, TOK_CLOSE, TOK_VOPEN, TOK_VCLOSE, TOK_BAR, TOK_NUMBER, TOK_VARIABLE, TOK_INFIX
};

enum {
    OP_NONE = 0,
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_DIV,
    OP_POW,
    OP_MOD
};

enum {TE_CONSTANT = 1, TE_VALUE_VARIABLE = 2};


typedef struct state {
    const char *start;
    const char *next;
    int type;
    union {double value; const double *bound; const te_value *value_bound; const void *function;};
    void *context;
    int var_is_value;
    int op;

    const te_variable *lookup;
    int lookup_len;
    const te_binding *value_lookup;
    int value_lookup_len;
} state;


#define TYPE_MASK(TYPE) ((TYPE)&0x0000001F)

#define IS_PURE(TYPE) (((TYPE) & TE_FLAG_PURE) != 0)
#define IS_FUNCTION(TYPE) (((TYPE) & TE_FUNCTION0) != 0)
#define IS_CLOSURE(TYPE) (((TYPE) & TE_CLOSURE0) != 0)
#define ARITY(TYPE) ( ((TYPE) & (TE_FUNCTION0 | TE_CLOSURE0)) ? ((TYPE) & 0x00000007) : 0 )
#define NEW_EXPR(type, ...) new_expr((type), (const te_expr*[]){__VA_ARGS__})
#define CHECK_NULL(ptr, ...) if ((ptr) == NULL) { __VA_ARGS__; return NULL; }

static te_expr *new_expr(const int type, const te_expr *parameters[]) {
    const int arity = ARITY(type);
    const int psize = sizeof(void*) * arity;
    const int size = (sizeof(te_expr) - sizeof(void*)) + psize + (IS_CLOSURE(type) ? sizeof(void*) : 0);
    te_expr *ret = malloc(size);
    CHECK_NULL(ret);

    memset(ret, 0, size);
    if (arity && parameters) {
        memcpy(ret->parameters, parameters, psize);
    }
    ret->type = type;
    ret->bound = 0;
    return ret;
}


void te_free_parameters(te_expr *n) {
    if (!n) return;
    switch (TYPE_MASK(n->type)) {
        case TE_FUNCTION7: case TE_CLOSURE7: te_free(n->parameters[6]);     /* Falls through. */
        case TE_FUNCTION6: case TE_CLOSURE6: te_free(n->parameters[5]);     /* Falls through. */
        case TE_FUNCTION5: case TE_CLOSURE5: te_free(n->parameters[4]);     /* Falls through. */
        case TE_FUNCTION4: case TE_CLOSURE4: te_free(n->parameters[3]);     /* Falls through. */
        case TE_FUNCTION3: case TE_CLOSURE3: te_free(n->parameters[2]);     /* Falls through. */
        case TE_FUNCTION2: case TE_CLOSURE2: te_free(n->parameters[1]);     /* Falls through. */
        case TE_FUNCTION1: case TE_CLOSURE1: te_free(n->parameters[0]);
    }
}


void te_free(te_expr *n) {
    if (!n) return;
    te_free_parameters(n);
    free(n);
}


static double pi(void) {return 3.14159265358979323846;}
static double e(void) {return 2.71828182845904523536;}
static double deg_to_rad(double a) {return a * (pi() / 180.0);}
static double rad_to_deg(double a) {return a * (180.0 / pi());}
static double fac(double a) {/* simplest version of fac */
    if (a < 0.0)
        return NAN;
    if (a > UINT_MAX)
        return INFINITY;
    unsigned int ua = (unsigned int)(a);
    unsigned long int result = 1, i;
    for (i = 1; i <= ua; i++) {
        if (i > ULONG_MAX / result)
            return INFINITY;
        result *= i;
    }
    return (double)result;
}
static double ncr(double n, double r) {
    if (n < 0.0 || r < 0.0 || n < r) return NAN;
    if (n > UINT_MAX || r > UINT_MAX) return INFINITY;
    unsigned long int un = (unsigned int)(n), ur = (unsigned int)(r), i;
    unsigned long int result = 1;
    if (ur > un / 2) ur = un - ur;
    for (i = 1; i <= ur; i++) {
        if (result > ULONG_MAX / (un - ur + i))
            return INFINITY;
        result *= un - ur + i;
        result /= i;
    }
    return result;
}
static double npr(double n, double r) {return ncr(n, r) * fac(r);}
static double comp(double a, double b);
static double dot(double a, double b);
static double ocomp(double a, double b);
static double oproj(double a, double b);
static double proj(double a, double b);
static double cross(double a, double b);
static double unit(double a);
static double derivative_eval(const te_expr *compiled_expr, te_binding *x_binding, int *error, double at_point);
static double integral_eval(const te_expr *compiled_expr, te_binding *x_binding, int *error, double lower, double upper);
static int eval_compiled_scalar_at_x(const te_expr *compiled_expr, te_binding *x_binding, double x, double *out);
static int evaluate_scalar_text(const char *text, const te_binding *bindings, int bind_count, double *out, int *error);
static int parse_calculus_call(const char *expression, int *is_derivative, char **arg0, char **arg1, char **arg2);
static int split_calculus_args(const char *args_start, const char *args_end, int expected_count, char **arg0, char **arg1, char **arg2);
static char *copy_trimmed_slice(const char *start, const char *end);
static void free_calculus_args(char **arg0, char **arg1, char **arg2);
static int evaluate_calculus_call(const char *expression, const te_binding *bindings, int bind_count, te_value *result, int *error);
static char *expand_calculus_calls(const char *expression, const te_binding *bindings, int bind_count, int *error);
static te_value make_error(void);
static te_value make_scalar(double x);
static te_value expressions[26];
static int expression_is_set[26];

#ifdef _MSC_VER
#pragma function (ceil)
#pragma function (floor)
#endif

static const te_variable functions[] = {
    /* must be in alphabetical order */
    {"abs", fabs,     TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"acos", acos,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"asin", asin,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"atan", atan,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"atan2", atan2,  TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"ceil", ceil,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"comp", comp,    TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"cos", cos,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"cosh", cosh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"cross", cross,  TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"deg_to_rad", deg_to_rad, TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"dot", dot,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"e", e,          TE_FUNCTION0 | TE_FLAG_PURE, 0},
    {"exp", exp,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"fac", fac,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"floor", floor,  TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"ln", log,       TE_FUNCTION1 | TE_FLAG_PURE, 0},
#ifdef TE_NAT_LOG
    {"log", log,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
#else
    {"log", log10,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
#endif
    {"log10", log10,  TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"ncr", ncr,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"npr", npr,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"ocomp", ocomp,  TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"oproj", oproj,  TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"pi", pi,        TE_FUNCTION0 | TE_FLAG_PURE, 0},
    {"pow", pow,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"proj", proj,    TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"rad_to_deg", rad_to_deg, TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"sin", sin,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"sinh", sinh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"sqrt", sqrt,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"tan", tan,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"tanh", tanh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"unit", unit,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {0, 0, 0, 0}
};

static const te_variable *find_builtin(const char *name, int len) {
    int imin = 0;
    int imax = sizeof(functions) / sizeof(te_variable) - 2;

    /*Binary search.*/
    while (imax >= imin) {
        const int i = (imin + ((imax-imin)/2));
        int c = strncmp(name, functions[i].name, len);
        if (!c) c = '\0' - functions[i].name[len];
        if (c == 0) {
            return functions + i;
        } else if (c > 0) {
            imin = i + 1;
        } else {
            imax = i - 1;
        }
    }

    return 0;
}

static const te_variable *find_lookup(const state *s, const char *name, int len) {
    int iters;
    const te_variable *var;
    if (!s->lookup) return 0;

    for (var = s->lookup, iters = s->lookup_len; iters; ++var, --iters) {
        if (strncmp(name, var->name, len) == 0 && var->name[len] == '\0') {
            return var;
        }
    }
    return 0;
}

static const te_binding *find_value_lookup(const state *s, const char *name, int len) {
    int iters;
    const te_binding *var;
    if (!s->value_lookup) return 0;

    for (var = s->value_lookup, iters = s->value_lookup_len; iters; ++var, --iters) {
        if (strncmp(name, var->name, len) == 0 && var->name[len] == '\0') {
            return var;
        }
    }
    return 0;
}



static double add(double a, double b) {return a + b;}
static double sub(double a, double b) {return a - b;}
static double mul(double a, double b) {return a * b;}
static double divide(double a, double b) {return a / b;}
static double comp(double a, double b) {(void)a; (void)b; return NAN;}
static double dot(double a, double b) {(void)a; (void)b; return NAN;}
static double ocomp(double a, double b) {(void)a; (void)b; return NAN;}
static double oproj(double a, double b) {(void)a; (void)b; return NAN;}
static double proj(double a, double b) {(void)a; (void)b; return NAN;}
static double cross(double a, double b) {(void)a; (void)b; return NAN;}
static double unit(double a) {(void)a; return NAN;}
static double vec3_literal(double a, double b, double c) {(void)a; (void)b; (void)c; return NAN;}
static double magnitude(double a) {(void)a; return NAN;}
static double negate(double a) {return -a;}
static double comma(double a, double b) {(void)a; return b;}


void next_token(state *s) {
    s->type = TOK_NULL;
    s->op = OP_NONE;
    s->var_is_value = 0;

    do {

        if (!*s->next){
            s->type = TOK_END;
            return;
        }

        /* Try reading a number. */
        if ((s->next[0] >= '0' && s->next[0] <= '9') || s->next[0] == '.') {
            s->value = strtod(s->next, (char**)&s->next);
            s->type = TOK_NUMBER;
        } else {
            /* Look for a variable or builtin function call. */
            if (isalpha(s->next[0])) {
                const char *start;
                int len;
                start = s->next;
                while (isalpha(s->next[0]) || isdigit(s->next[0]) || (s->next[0] == '_')) s->next++;
                len = (int)(s->next - start);

                const te_variable *var = find_lookup(s, start, len);
                const te_binding *vvar = find_value_lookup(s, start, len);
                const te_value *stored_value = 0;
                if (!var) var = find_builtin(start, s->next - start);

                if (!vvar && len == 1 && start[0] >= 'A' && start[0] <= 'Z') {
                    int stored_index = start[0] - 'A';
                    if (expression_is_set[stored_index]) {
                        stored_value = &expressions[stored_index];
                    }
                }

                if (vvar) {
                    s->type = TOK_VARIABLE;
                    s->var_is_value = 1;
                    s->value_bound = &vvar->value;
                } else if (stored_value) {
                    s->type = TOK_VARIABLE;
                    s->var_is_value = 1;
                    s->value_bound = stored_value;
                } else if (!var) {
                    s->type = TOK_ERROR;
                } else {
                    switch(TYPE_MASK(var->type))
                    {
                        case TE_VARIABLE:
                            s->type = TOK_VARIABLE;
                            s->bound = var->address;
                            break;

                        case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:         /* Falls through. */
                        case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:         /* Falls through. */
                            s->context = var->context;                                                  /* Falls through. */

                        case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:     /* Falls through. */
                        case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:     /* Falls through. */
                            s->type = var->type;
                            s->function = var->address;
                            break;
                    }
                }

            } else {
                /* Look for an operator or special character. */
                switch (s->next++[0]) {
                    case '+': s->type = TOK_INFIX; s->op = OP_ADD; s->function = add; break;
                    case '-': s->type = TOK_INFIX; s->op = OP_SUB; s->function = sub; break;
                    case '*': s->type = TOK_INFIX; s->op = OP_MUL; s->function = mul; break;
                    case '/': s->type = TOK_INFIX; s->op = OP_DIV; s->function = divide; break;
                    case '^': s->type = TOK_INFIX; s->op = OP_POW; s->function = pow; break;
                    case '%': s->type = TOK_INFIX; s->op = OP_MOD; s->function = fmod; break;
                    case '(': s->type = TOK_OPEN; break;
                    case ')': s->type = TOK_CLOSE; break;
                    case '<': s->type = TOK_VOPEN; break;
                    case '>': s->type = TOK_VCLOSE; break;
                    case '|': s->type = TOK_BAR; break;
                    case ',': s->type = TOK_SEP; break;
                    case ' ': case '\t': case '\n': case '\r': break;
                    default:
                        s->type = TOK_ERROR;
                        break;
                }
            }
        }
    } while (s->type == TOK_NULL);
}


static te_expr *list(state *s);
static te_expr *expr(state *s);
static te_expr *power(state *s);

static int eval_compiled_scalar_at_x(const te_expr *compiled_expr, te_binding *x_binding, double x, double *out) {
    te_value value;
    if (!compiled_expr || !x_binding || !out) return -1;
    x_binding->value.kind = TE_VAL_SCALAR;
    x_binding->value.scalar = x;
    value = te_eval_value(compiled_expr);
    if (value.kind != TE_VAL_SCALAR) return -1;
    *out = value.scalar;
    return 0;
}

static double derivative_eval(const te_expr *compiled_expr, te_binding *x_binding, int *error, double at_point) {
    const double h = 1e-5;
    double y_plus;
    double y_minus;

    if (eval_compiled_scalar_at_x(compiled_expr, x_binding, at_point + h, &y_plus) != 0 ||
        eval_compiled_scalar_at_x(compiled_expr, x_binding, at_point - h, &y_minus) != 0) {
        if (error) *error = 1;
        return NAN;
    }

    return (y_plus - y_minus) / (2.0 * h);
}

static double integral_eval(const te_expr *compiled_expr, te_binding *x_binding, int *error, double lower, double upper) {
    int i;
    int n = 10000;
    double h;
    double y_lower;
    double y_upper;
    double sum;

    if (n % 2) n++;
    h = (upper - lower) / n;

    if (eval_compiled_scalar_at_x(compiled_expr, x_binding, lower, &y_lower) != 0 ||
        eval_compiled_scalar_at_x(compiled_expr, x_binding, upper, &y_upper) != 0) {
        if (error) *error = 1;
        return NAN;
    }

    sum = y_lower + y_upper;
    for (i = 1; i < n; ++i) {
        double x = lower + i * h;
        double y;
        if (eval_compiled_scalar_at_x(compiled_expr, x_binding, x, &y) != 0) {
            if (error) *error = 1;
            return NAN;
        }
        if (i % 2 == 0) {
            sum += 2.0 * y;
        } else {
            sum += 4.0 * y;
        }
    }

    return (h / 3.0) * sum;
}

static int evaluate_scalar_text(const char *text, const te_binding *bindings, int bind_count, double *out, int *error) {
    te_expr *compiled;
    te_value value;
    int local_error = 0;
    if (!text || !out) return -1;

    compiled = te_compile_value(text, bindings, bind_count, &local_error);
    if (!compiled) {
        if (error) *error = local_error ? local_error : 1;
        return -1;
    }

    value = te_eval_value(compiled);
    te_free(compiled);
    if (value.kind != TE_VAL_SCALAR) {
        if (error) *error = 1;
        return -1;
    }
    *out = value.scalar;
    if (error) *error = 0;
    return 0;
}

static char *copy_trimmed_slice(const char *start, const char *end) {
    char *out;
    size_t len;
    const char *left = start;
    const char *right = end;

    if (!start || !end || end < start) return 0;
    while (left < right && isspace((unsigned char)*left)) left++;
    while (right > left && isspace((unsigned char)*(right - 1))) right--;

    len = (size_t)(right - left);
    out = (char*)malloc(len + 1);
    if (!out) return 0;

    if (len > 0) memcpy(out, left, len);
    out[len] = '\0';
    return out;
}

static void free_calculus_args(char **arg0, char **arg1, char **arg2) {
    if (arg0 && *arg0) {
        free(*arg0);
        *arg0 = 0;
    }
    if (arg1 && *arg1) {
        free(*arg1);
        *arg1 = 0;
    }
    if (arg2 && *arg2) {
        free(*arg2);
        *arg2 = 0;
    }
}

static int split_calculus_args(const char *args_start, const char *args_end, int expected_count, char **arg0, char **arg1, char **arg2) {
    const char *segment_start;
    const char *p;
    const char *arg_starts[3];
    const char *arg_ends[3];
    int depth_paren = 0;
    int depth_vec = 0;
    int count = 0;

    if (!args_start || !args_end || args_end < args_start || expected_count < 2 || expected_count > 3) return -1;

    segment_start = args_start;
    p = args_start;

    while (p < args_end) {
        char ch = *p;
        if (ch == '(') {
            depth_paren++;
        } else if (ch == ')') {
            if (depth_paren <= 0) return -1;
            depth_paren--;
        } else if (ch == '<') {
            depth_vec++;
        } else if (ch == '>') {
            if (depth_vec <= 0) return -1;
            depth_vec--;
        } else if (ch == ',' && depth_paren == 0 && depth_vec == 0) {
            if (count >= expected_count - 1) return -1;
            arg_starts[count] = segment_start;
            arg_ends[count] = p;
            count++;
            segment_start = p + 1;
        }
        p++;
    }

    if (depth_paren != 0 || depth_vec != 0) return -1;
    if (count != expected_count - 1) return -1;

    arg_starts[count] = segment_start;
    arg_ends[count] = args_end;
    count++;

    *arg0 = copy_trimmed_slice(arg_starts[0], arg_ends[0]);
    *arg1 = copy_trimmed_slice(arg_starts[1], arg_ends[1]);
    *arg2 = (expected_count == 3) ? copy_trimmed_slice(arg_starts[2], arg_ends[2]) : 0;

    if (!*arg0 || !*arg1 || (expected_count == 3 && !*arg2)) {
        free_calculus_args(arg0, arg1, arg2);
        return -1;
    }
    if ((*arg0)[0] == '\0' || (*arg1)[0] == '\0' || (expected_count == 3 && (*arg2)[0] == '\0')) {
        free_calculus_args(arg0, arg1, arg2);
        return -1;
    }

    return 0;
}

static int parse_calculus_call(const char *expression, int *is_derivative, char **arg0, char **arg1, char **arg2) {
    const char *p;
    const char *name_end;
    const char *open_paren;
    const char *close_paren = 0;
    const char *args_start;
    int depth = 0;
    int expected_count;
    const char *derivative_name = "derivative";
    const char *integral_name = "integral";

    if (!expression || !is_derivative || !arg0 || !arg1 || !arg2) return 0;

    *arg0 = 0;
    *arg1 = 0;
    *arg2 = 0;

    p = expression;
    while (isspace((unsigned char)*p)) p++;

    if (strncmp(p, derivative_name, strlen(derivative_name)) == 0) {
        *is_derivative = 1;
        name_end = p + (int)strlen(derivative_name);
    } else if (strncmp(p, integral_name, strlen(integral_name)) == 0) {
        *is_derivative = 0;
        name_end = p + (int)strlen(integral_name);
    } else {
        return 0;
    }

    if (isalpha((unsigned char)*name_end) || isdigit((unsigned char)*name_end) || *name_end == '_') {
        return 0;
    }

    while (isspace((unsigned char)*name_end)) name_end++;
    if (*name_end != '(') return -1;
    open_paren = name_end;

    p = open_paren;
    while (*p) {
        if (*p == '(') {
            depth++;
        } else if (*p == ')') {
            depth--;
            if (depth == 0) {
                close_paren = p;
                break;
            }
            if (depth < 0) return -1;
        }
        p++;
    }
    if (!close_paren || depth != 0) return -1;

    p = close_paren + 1;
    while (isspace((unsigned char)*p)) p++;
    if (*p != '\0') return -1;

    args_start = open_paren + 1;
    expected_count = *is_derivative ? 2 : 3;
    if (split_calculus_args(args_start, close_paren, expected_count, arg0, arg1, arg2) != 0) {
        return -1;
    }
    return 1;
}

static int evaluate_calculus_call(const char *expression, const te_binding *bindings, int bind_count, te_value *result, int *error) {
    int is_derivative = 0;
    char *expr_arg = 0;
    char *arg1 = 0;
    char *arg2 = 0;
    int parse_status;
    double at_or_lower;
    double upper = 0.0;
    te_binding x_binding;
    te_binding *merged_bindings = 0;
    int merged_count = 1;
    int i;
    te_expr *compiled_expr = 0;
    double answer;
    int local_error = 0;

    parse_status = parse_calculus_call(expression, &is_derivative, &expr_arg, &arg1, &arg2);
    if (parse_status == 0) return 0;
    if (parse_status < 0) {
        if (error) *error = 1;
        free_calculus_args(&expr_arg, &arg1, &arg2);
        *result = make_error();
        return 1;
    }

    if (evaluate_scalar_text(arg1, bindings, bind_count, &at_or_lower, &local_error) != 0) {
        if (error) *error = local_error ? local_error : 1;
        free_calculus_args(&expr_arg, &arg1, &arg2);
        *result = make_error();
        return 1;
    }
    if (!is_derivative) {
        if (evaluate_scalar_text(arg2, bindings, bind_count, &upper, &local_error) != 0) {
            if (error) *error = local_error ? local_error : 1;
            free_calculus_args(&expr_arg, &arg1, &arg2);
            *result = make_error();
            return 1;
        }
    }

    if (bindings && bind_count > 0) {
        for (i = 0; i < bind_count; ++i) {
            if (bindings[i].name && strcmp(bindings[i].name, "x") != 0) {
                merged_count++;
            }
        }
    }

    merged_bindings = (te_binding*)malloc((size_t)merged_count * sizeof(te_binding));
    if (!merged_bindings) {
        if (error) *error = 1;
        free_calculus_args(&expr_arg, &arg1, &arg2);
        *result = make_error();
        return 1;
    }

    x_binding.name = "x";
    x_binding.value = make_scalar(0.0);
    merged_bindings[0] = x_binding;

    if (bindings && bind_count > 0) {
        int next = 1;
        for (i = 0; i < bind_count; ++i) {
            if (!bindings[i].name || strcmp(bindings[i].name, "x") == 0) continue;
            merged_bindings[next++] = bindings[i];
        }
    }

    compiled_expr = te_compile_value(expr_arg, merged_bindings, merged_count, &local_error);
    if (!compiled_expr) {
        if (error) *error = local_error ? local_error : 1;
        free(merged_bindings);
        free_calculus_args(&expr_arg, &arg1, &arg2);
        *result = make_error();
        return 1;
    }

    if (is_derivative) {
        answer = derivative_eval(compiled_expr, &merged_bindings[0], &local_error, at_or_lower);
    } else {
        answer = integral_eval(compiled_expr, &merged_bindings[0], &local_error, at_or_lower, upper);
    }

    te_free(compiled_expr);
    free(merged_bindings);
    free_calculus_args(&expr_arg, &arg1, &arg2);

    if (local_error != 0) {
        if (error) *error = local_error;
        *result = make_error();
        return 1;
    }

    if (error) *error = 0;
    *result = make_scalar(answer);
    return 1;
}

static char *expand_calculus_calls(const char *expression, const te_binding *bindings, int bind_count, int *error) {
    const char *p = expression;
    char *out = 0;
    size_t out_len = 0;
    size_t out_cap = 0;
    const char *derivative_name = "derivative";
    const char *integral_name = "integral";

    while (*p) {
        int matched = 0;
        const char *name = 0;
        size_t name_len = 0;

        if (strncmp(p, derivative_name, strlen(derivative_name)) == 0) {
            matched = 1;
            name = derivative_name;
            name_len = strlen(derivative_name);
        } else if (strncmp(p, integral_name, strlen(integral_name)) == 0) {
            matched = 1;
            name = integral_name;
            name_len = strlen(integral_name);
        }

        if (matched) {
            const char *q = p + name_len;
            const char *call_end = 0;
            int depth = 0;
            te_value value = make_error();
            int local_error = 0;
            char *call_text;
            char number_buf[64];
            int number_len;

            if (p > expression) {
                char prev = *(p - 1);
                if (isalpha((unsigned char)prev) || isdigit((unsigned char)prev) || prev == '_') {
                    matched = 0;
                }
            }
            if (matched) {
                while (isspace((unsigned char)*q)) q++;
                if (*q != '(') matched = 0;
            }

            if (matched) {
                const char *r = q;
                while (*r) {
                    if (*r == '(') {
                        depth++;
                    } else if (*r == ')') {
                        depth--;
                        if (depth == 0) {
                            call_end = r + 1;
                            break;
                        }
                        if (depth < 0) break;
                    }
                    r++;
                }
                if (!call_end || depth != 0) {
                    if (error) *error = 1;
                    free(out);
                    return 0;
                }
            }

            if (matched) {
                if (isalpha((unsigned char)*call_end) || isdigit((unsigned char)*call_end) || *call_end == '_') {
                    matched = 0;
                }
            }

            if (matched) {
                call_text = copy_trimmed_slice(p, call_end);
                if (!call_text) {
                    if (error) *error = 1;
                    free(out);
                    return 0;
                }

                if (!evaluate_calculus_call(call_text, bindings, bind_count, &value, &local_error) || value.kind != TE_VAL_SCALAR) {
                    free(call_text);
                    if (error) *error = local_error ? local_error : 1;
                    free(out);
                    return 0;
                }
                free(call_text);

                number_len = snprintf(number_buf, sizeof(number_buf), "%.17g", value.scalar);
                if (number_len < 0) {
                    if (error) *error = 1;
                    free(out);
                    return 0;
                }

                if (out_len + (size_t)number_len + 1 > out_cap) {
                    size_t new_cap = out_cap ? out_cap : 64;
                    while (out_len + (size_t)number_len + 1 > new_cap) new_cap *= 2;
                    {
                        char *grown = (char*)realloc(out, new_cap);
                        if (!grown) {
                            if (error) *error = 1;
                            free(out);
                            return 0;
                        }
                        out = grown;
                        out_cap = new_cap;
                    }
                }

                memcpy(out + out_len, number_buf, (size_t)number_len);
                out_len += (size_t)number_len;
                out[out_len] = '\0';
                p = call_end;
                continue;
            }
        }

        if (out_len + 2 > out_cap) {
            size_t new_cap = out_cap ? out_cap * 2 : 64;
            char *grown = (char*)realloc(out, new_cap);
            if (!grown) {
                if (error) *error = 1;
                free(out);
                return 0;
            }
            out = grown;
            out_cap = new_cap;
        }
        out[out_len++] = *p++;
        out[out_len] = '\0';
    }

    if (!out) {
        out = (char*)malloc(strlen(expression) + 1);
        if (!out) {
            if (error) *error = 1;
            return 0;
        }
        strcpy(out, expression);
    }
    if (error) *error = 0;
    return out;
}

static te_expr *base(state *s) {
    /* <base> = <constant> | <variable> | <vector-literal> | ... */
    te_expr *ret;
    int arity;
    int stype = s->type;
    if (IS_FUNCTION(s->type) || IS_CLOSURE(s->type)) {
        stype = TYPE_MASK(s->type);
    }

    switch (stype) {
        case TOK_NUMBER:
            ret = new_expr(TE_CONSTANT, 0);
            CHECK_NULL(ret);

            ret->value = s->value;
            next_token(s);
            break;

        case TOK_VARIABLE:
            ret = new_expr(s->var_is_value ? TE_VALUE_VARIABLE : TE_VARIABLE, 0);
            CHECK_NULL(ret);

            if (s->var_is_value) {
                ret->value_bound = s->value_bound;
            } else {
                ret->bound = s->bound;
            }
            next_token(s);
            break;

        case TE_FUNCTION0:
        case TE_CLOSURE0:
            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            ret->function = s->function;
            if (IS_CLOSURE(s->type)) ret->parameters[0] = s->context;
            next_token(s);
            if (s->type == TOK_OPEN) {
                next_token(s);
                if (s->type != TOK_CLOSE) {
                    s->type = TOK_ERROR;
                } else {
                    next_token(s);
                }
            }
            break;

        case TE_FUNCTION1:
        case TE_CLOSURE1:
            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            ret->function = s->function;
            if (IS_CLOSURE(s->type)) ret->parameters[1] = s->context;
            next_token(s);
            ret->parameters[0] = power(s);
            CHECK_NULL(ret->parameters[0], te_free(ret));
            break;

        case TE_FUNCTION2: case TE_FUNCTION3: case TE_FUNCTION4:
        case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
        case TE_CLOSURE2: case TE_CLOSURE3: case TE_CLOSURE4:
        case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
            arity = ARITY(s->type);

            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            ret->function = s->function;
            if (IS_CLOSURE(s->type)) ret->parameters[arity] = s->context;
            next_token(s);

            if (s->type != TOK_OPEN) {
                s->type = TOK_ERROR;
            } else {
                int i;
                for(i = 0; i < arity; i++) {
                    next_token(s);
                    ret->parameters[i] = expr(s);
                    CHECK_NULL(ret->parameters[i], te_free(ret));

                    if(s->type != TOK_SEP) {
                        break;
                    }
                }
                if(s->type != TOK_CLOSE || i != arity - 1) {
                    s->type = TOK_ERROR;
                } else {
                    next_token(s);
                }
            }

            break;

        case TOK_OPEN:
            next_token(s);
            ret = list(s);
            CHECK_NULL(ret);

            if (s->type != TOK_CLOSE) {
                s->type = TOK_ERROR;
            } else {
                next_token(s);
            }
            break;

        case TOK_BAR: {
            te_expr *inner;
            next_token(s);
            inner = expr(s);
            CHECK_NULL(inner);
            if (s->type != TOK_BAR) {
                te_free(inner);
                s->type = TOK_ERROR;
                return new_expr(0, 0);
            }
            ret = NEW_EXPR(TE_FUNCTION1 | TE_FLAG_PURE, inner);
            CHECK_NULL(ret, te_free(inner));
            ret->function = magnitude;
            next_token(s);
            break;
        }

        case TOK_VOPEN: {
            te_expr *x;
            te_expr *y;
            te_expr *z;
            next_token(s);
            x = expr(s);
            CHECK_NULL(x);
            if (s->type != TOK_SEP) {
                te_free(x);
                s->type = TOK_ERROR;
                return new_expr(0, 0);
            }
            next_token(s);
            y = expr(s);
            CHECK_NULL(y, te_free(x));
            if (s->type != TOK_SEP) {
                te_free(x);
                te_free(y);
                s->type = TOK_ERROR;
                return new_expr(0, 0);
            }
            next_token(s);
            z = expr(s);
            CHECK_NULL(z, te_free(x), te_free(y));
            if (s->type != TOK_VCLOSE) {
                te_free(x);
                te_free(y);
                te_free(z);
                s->type = TOK_ERROR;
                return new_expr(0, 0);
            }
            ret = NEW_EXPR(TE_FUNCTION3 | TE_FLAG_PURE, x, y, z);
            CHECK_NULL(ret, te_free(x), te_free(y), te_free(z));
            ret->function = vec3_literal;
            next_token(s);
            break;
        }

        default:
            ret = new_expr(0, 0);
            CHECK_NULL(ret);

            s->type = TOK_ERROR;
            ret->value = NAN;
            break;
    }

    return ret;
}


static te_expr *power(state *s) {
    /* <power>     =    {("-" | "+")} <base> */
    int sign = 1;
    while (s->type == TOK_INFIX && (s->op == OP_ADD || s->op == OP_SUB)) {
        if (s->op == OP_SUB) sign = -sign;
        next_token(s);
    }

    te_expr *ret;

    if (sign == 1) {
        ret = base(s);
    } else {
        te_expr *b = base(s);
        CHECK_NULL(b);

        ret = NEW_EXPR(TE_FUNCTION1 | TE_FLAG_PURE, b);
        CHECK_NULL(ret, te_free(b));

        ret->function = negate;
    }

    return ret;
}

#ifdef TE_POW_FROM_RIGHT
static te_expr *factor(state *s) {
    /* <factor>    =    <power> {"^" <power>} */
    te_expr *ret = power(s);
    CHECK_NULL(ret);

    int neg = 0;

    if (ret->type == (TE_FUNCTION1 | TE_FLAG_PURE) && ret->function == negate) {
        te_expr *se = ret->parameters[0];
        free(ret);
        ret = se;
        neg = 1;
    }

    te_expr *insertion = 0;

    while (s->type == TOK_INFIX && s->op == OP_POW) {
        te_fun2 t = s->function;
        next_token(s);

        if (insertion) {
            /* Make exponentiation go right-to-left. */
            te_expr *p = power(s);
            CHECK_NULL(p, te_free(ret));

            te_expr *insert = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, insertion->parameters[1], p);
            CHECK_NULL(insert, te_free(p), te_free(ret));

            insert->function = t;
            insertion->parameters[1] = insert;
            insertion = insert;
        } else {
            te_expr *p = power(s);
            CHECK_NULL(p, te_free(ret));

            te_expr *prev = ret;
            ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, p);
            CHECK_NULL(ret, te_free(p), te_free(prev));

            ret->function = t;
            insertion = ret;
        }
    }

    if (neg) {
        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION1 | TE_FLAG_PURE, ret);
        CHECK_NULL(ret, te_free(prev));

        ret->function = negate;
    }

    return ret;
}
#else
static te_expr *factor(state *s) {
    /* <factor>    =    <power> {"^" <power>} */
    te_expr *ret = power(s);
    CHECK_NULL(ret);

    while (s->type == TOK_INFIX && s->op == OP_POW) {
        te_fun2 t = s->function;
        next_token(s);
        te_expr *p = power(s);
        CHECK_NULL(p, te_free(ret));

        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, p);
        CHECK_NULL(ret, te_free(p), te_free(prev));

        ret->function = t;
    }

    return ret;
}
#endif

static te_expr *term(state *s) {
    /* <term>      =    <factor> {("*" | "/" | "%") <factor>} */
    te_expr *ret = factor(s);
    CHECK_NULL(ret);

    while (s->type == TOK_INFIX &&
           (s->op == OP_MUL || s->op == OP_DIV || s->op == OP_MOD)) {
        te_fun2 t = s->function;
        next_token(s);
        te_expr *f = factor(s);
        CHECK_NULL(f, te_free(ret));

        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, f);
        CHECK_NULL(ret, te_free(f), te_free(prev));

        ret->function = t;
    }

    return ret;
}


static te_expr *expr(state *s) {
    /* <expr>      =    <term> {("+" | "-") <term>} */
    te_expr *ret = term(s);
    CHECK_NULL(ret);

    while (s->type == TOK_INFIX && (s->op == OP_ADD || s->op == OP_SUB)) {
        te_fun2 t = s->function;
        next_token(s);
        te_expr *te = term(s);
        CHECK_NULL(te, te_free(ret));

        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, te);
        CHECK_NULL(ret, te_free(te), te_free(prev));

        ret->function = t;
    }

    return ret;
}


static te_expr *list(state *s) {
    /* <list>      =    <expr> {"," <expr>} */
    te_expr *ret = expr(s);
    CHECK_NULL(ret);

    while (s->type == TOK_SEP) {
        next_token(s);
        te_expr *e = expr(s);
        CHECK_NULL(e, te_free(ret));

        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, e);
        CHECK_NULL(ret, te_free(e), te_free(prev));

        ret->function = comma;
    }

    return ret;
}


static te_value make_scalar(double x) {
    te_value v;
    v.kind = TE_VAL_SCALAR;
    v.scalar = x;
    return v;
}

static te_value make_vec3(double x, double y, double z) {
    te_value v;
    v.kind = TE_VAL_VEC3;
    v.vec3.x = x;
    v.vec3.y = y;
    v.vec3.z = z;
    return v;
}

static te_value make_error(void) {
    te_value v;
    v.kind = TE_VAL_ERROR;
    v.scalar = NAN;
    return v;
}

static te_value eval_scalar_function(const te_expr *n, const te_value args[7]) {
#define TE_FUN(...) ((double(*)(__VA_ARGS__))n->function)
    switch(ARITY(n->type)) {
        case 0: return make_scalar(TE_FUN(void)());
        case 1: return make_scalar(TE_FUN(double)(args[0].scalar));
        case 2: return make_scalar(TE_FUN(double, double)(args[0].scalar, args[1].scalar));
        case 3: return make_scalar(TE_FUN(double, double, double)(args[0].scalar, args[1].scalar, args[2].scalar));
        case 4: return make_scalar(TE_FUN(double, double, double, double)(args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar));
        case 5: return make_scalar(TE_FUN(double, double, double, double, double)(args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar));
        case 6: return make_scalar(TE_FUN(double, double, double, double, double, double)(args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar, args[5].scalar));
        case 7: return make_scalar(TE_FUN(double, double, double, double, double, double, double)(args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar, args[5].scalar, args[6].scalar));
        default: return make_error();
    }
#undef TE_FUN
}

te_value te_eval_value(const te_expr *n) {
    int i;
    te_value args[7];
    if (!n) return make_error();

    switch(TYPE_MASK(n->type)) {
        case TE_CONSTANT:
            return make_scalar(n->value);
        case TE_VARIABLE:
            return make_scalar(*n->bound);
        case TE_VALUE_VARIABLE:
            return *n->value_bound;

        case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:
        case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
        case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:
        case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
            for (i = 0; i < ARITY(n->type); ++i) {
                args[i] = te_eval_value(n->parameters[i]);
                if (args[i].kind == TE_VAL_ERROR) return make_error();
            }

            if (n->function == vec3_literal) {
                if (ARITY(n->type) != 3 ||
                    args[0].kind != TE_VAL_SCALAR ||
                    args[1].kind != TE_VAL_SCALAR ||
                    args[2].kind != TE_VAL_SCALAR) {
                    return make_error();
                }
                return make_vec3(args[0].scalar, args[1].scalar, args[2].scalar);
            }

            if (n->function == comma) {
                if (ARITY(n->type) != 2) return make_error();
                return args[1];
            }

            if (n->function == negate) {
                if (ARITY(n->type) != 1 || args[0].kind != TE_VAL_SCALAR) return make_error();
                return make_scalar(-args[0].scalar);
            }

            if (n->function == magnitude) {
                if (ARITY(n->type) != 1) return make_error();
                if (args[0].kind == TE_VAL_SCALAR) {
                    return make_scalar(fabs(args[0].scalar));
                }
                if (args[0].kind == TE_VAL_VEC3) {
                    return make_scalar(sqrt(
                        args[0].vec3.x * args[0].vec3.x +
                        args[0].vec3.y * args[0].vec3.y +
                        args[0].vec3.z * args[0].vec3.z
                    ));
                }
                return make_error();
            }

            if (n->function == unit) {
                double len;
                if (ARITY(n->type) != 1 || args[0].kind != TE_VAL_VEC3) return make_error();
                len = sqrt(
                    args[0].vec3.x * args[0].vec3.x +
                    args[0].vec3.y * args[0].vec3.y +
                    args[0].vec3.z * args[0].vec3.z
                );
                if (len == 0.0) return make_error();
                return make_vec3(
                    args[0].vec3.x / len,
                    args[0].vec3.y / len,
                    args[0].vec3.z / len
                );
            }

            if (n->function == add || n->function == sub) {
                if (ARITY(n->type) != 2) return make_error();
                if (args[0].kind == TE_VAL_SCALAR && args[1].kind == TE_VAL_SCALAR) {
                    if (n->function == add) return make_scalar(args[0].scalar + args[1].scalar);
                    return make_scalar(args[0].scalar - args[1].scalar);
                }
                if (args[0].kind == TE_VAL_VEC3 && args[1].kind == TE_VAL_VEC3) {
                    if (n->function == add) {
                        return make_vec3(
                            args[0].vec3.x + args[1].vec3.x,
                            args[0].vec3.y + args[1].vec3.y,
                            args[0].vec3.z + args[1].vec3.z
                        );
                    }
                    return make_vec3(
                        args[0].vec3.x - args[1].vec3.x,
                        args[0].vec3.y - args[1].vec3.y,
                        args[0].vec3.z - args[1].vec3.z
                    );
                }
                return make_error();
            }

            if (n->function == fmod || n->function == pow) {
                double a;
                double b;
                if (ARITY(n->type) != 2 || args[0].kind != TE_VAL_SCALAR || args[1].kind != TE_VAL_SCALAR) {
                    return make_error();
                }
                a = args[0].scalar;
                b = args[1].scalar;
                if (n->function == fmod) return make_scalar(fmod(a, b));
                return make_scalar(pow(a, b));
            }

            if (n->function == divide) {
                if (ARITY(n->type) != 2) return make_error();
                if (args[0].kind == TE_VAL_SCALAR && args[1].kind == TE_VAL_SCALAR) {
                    return make_scalar(args[0].scalar / args[1].scalar);
                }
                if (args[0].kind == TE_VAL_VEC3 && args[1].kind == TE_VAL_SCALAR) {
                    return make_vec3(
                        args[0].vec3.x / args[1].scalar,
                        args[0].vec3.y / args[1].scalar,
                        args[0].vec3.z / args[1].scalar
                    );
                }
                return make_error();
            }

            if (n->function == mul) {
                if (ARITY(n->type) != 2) return make_error();
                if (args[0].kind == TE_VAL_SCALAR && args[1].kind == TE_VAL_SCALAR) {
                    return make_scalar(args[0].scalar * args[1].scalar);
                }
                if (args[0].kind == TE_VAL_SCALAR && args[1].kind == TE_VAL_VEC3) {
                    return make_vec3(
                        args[0].scalar * args[1].vec3.x,
                        args[0].scalar * args[1].vec3.y,
                        args[0].scalar * args[1].vec3.z
                    );
                }
                if (args[0].kind == TE_VAL_VEC3 && args[1].kind == TE_VAL_SCALAR) {
                    return make_vec3(
                        args[0].vec3.x * args[1].scalar,
                        args[0].vec3.y * args[1].scalar,
                        args[0].vec3.z * args[1].scalar
                    );
                }
                return make_error();
            }

            if (n->function == dot) {
                if (ARITY(n->type) != 2 || args[0].kind != TE_VAL_VEC3 || args[1].kind != TE_VAL_VEC3) {
                    return make_error();
                }
                return make_scalar(
                    args[0].vec3.x * args[1].vec3.x +
                    args[0].vec3.y * args[1].vec3.y +
                    args[0].vec3.z * args[1].vec3.z
                );
            }

            if (n->function == cross) {
                if (ARITY(n->type) != 2 || args[0].kind != TE_VAL_VEC3 || args[1].kind != TE_VAL_VEC3) {
                    return make_error();
                }
                return make_vec3(
                    args[0].vec3.y * args[1].vec3.z - args[0].vec3.z * args[1].vec3.y,
                    args[0].vec3.z * args[1].vec3.x - args[0].vec3.x * args[1].vec3.z,
                    args[0].vec3.x * args[1].vec3.y - args[0].vec3.y * args[1].vec3.x
                );
            }

            if (n->function == comp || n->function == proj ||
                n->function == ocomp || n->function == oproj) {
                double b_dot_b;
                double a_dot_b;
                double scale;
                te_vec3 b;
                te_vec3 a;
                te_vec3 p;
                te_vec3 o;

                if (ARITY(n->type) != 2 || args[0].kind != TE_VAL_VEC3 || args[1].kind != TE_VAL_VEC3) {
                    return make_error();
                }

                /* Argument order: function(B, A). */
                b = args[0].vec3;
                a = args[1].vec3;

                b_dot_b = b.x * b.x + b.y * b.y + b.z * b.z;
                if (b_dot_b == 0.0) {
                    return make_error();
                }

                a_dot_b = a.x * b.x + a.y * b.y + a.z * b.z;
                scale = a_dot_b / b_dot_b;

                p.x = scale * b.x;
                p.y = scale * b.y;
                p.z = scale * b.z;

                o.x = a.x - p.x;
                o.y = a.y - p.y;
                o.z = a.z - p.z;

                if (n->function == proj) {
                    return make_vec3(p.x, p.y, p.z);
                }
                if (n->function == oproj) {
                    return make_vec3(o.x, o.y, o.z);
                }
                if (n->function == comp) {
                    return make_scalar(a_dot_b / sqrt(b_dot_b));
                }
                return make_scalar(sqrt(o.x * o.x + o.y * o.y + o.z * o.z));
            }

            if (IS_CLOSURE(n->type)) {
#define TE_CLOSURE_FUN(...) ((double(*)(__VA_ARGS__))n->function)
                for (i = 0; i < ARITY(n->type); ++i) {
                    if (args[i].kind != TE_VAL_SCALAR) return make_error();
                }
                switch(ARITY(n->type)) {
                    case 0: return make_scalar(TE_CLOSURE_FUN(void*)(n->parameters[0]));
                    case 1: return make_scalar(TE_CLOSURE_FUN(void*, double)(n->parameters[1], args[0].scalar));
                    case 2: return make_scalar(TE_CLOSURE_FUN(void*, double, double)(n->parameters[2], args[0].scalar, args[1].scalar));
                    case 3: return make_scalar(TE_CLOSURE_FUN(void*, double, double, double)(n->parameters[3], args[0].scalar, args[1].scalar, args[2].scalar));
                    case 4: return make_scalar(TE_CLOSURE_FUN(void*, double, double, double, double)(n->parameters[4], args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar));
                    case 5: return make_scalar(TE_CLOSURE_FUN(void*, double, double, double, double, double)(n->parameters[5], args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar));
                    case 6: return make_scalar(TE_CLOSURE_FUN(void*, double, double, double, double, double, double)(n->parameters[6], args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar, args[5].scalar));
                    case 7: return make_scalar(TE_CLOSURE_FUN(void*, double, double, double, double, double, double, double)(n->parameters[7], args[0].scalar, args[1].scalar, args[2].scalar, args[3].scalar, args[4].scalar, args[5].scalar, args[6].scalar));
                    default: return make_error();
                }
#undef TE_CLOSURE_FUN
            }

            for (i = 0; i < ARITY(n->type); ++i) {
                if (args[i].kind != TE_VAL_SCALAR) return make_error();
            }
            return eval_scalar_function(n, args);

        default:
            return make_error();
    }
}

double te_eval(const te_expr *n) {
    te_value v = te_eval_value(n);
    if (v.kind == TE_VAL_SCALAR) return v.scalar;
    return NAN;
}

static void optimize(te_expr *n) {
    /* Evaluates as much as possible. */
    if (n->type == TE_CONSTANT) return;
    if (n->type == TE_VARIABLE) return;
    if (n->type == TE_VALUE_VARIABLE) return;

    /* Only optimize out functions flagged as pure. */
    if (IS_PURE(n->type)) {
        const int arity = ARITY(n->type);
        int known = 1;
        int i;
        for (i = 0; i < arity; ++i) {
            optimize(n->parameters[i]);
            if (((te_expr*)(n->parameters[i]))->type != TE_CONSTANT) {
                known = 0;
            }
        }
        if (known) {
            te_value value = te_eval_value(n);
            if (value.kind == TE_VAL_SCALAR) {
                te_free_parameters(n);
                n->type = TE_CONSTANT;
                n->value = value.scalar;
            }
        }
    }
}

int set_var(char var, te_value expr) {
    if (var < 'A' || var > 'Z') {
        return -1;
    }

    int index = var - 'A';
    expressions[index] = expr;
    expression_is_set[index] = 1;
    return 0;
}

te_value get_var(char var) {
    if (var < 'A' || var > 'Z') {
        return make_error();
    }
    
    int index = var - 'A';
    if (!expression_is_set[index]) {
        return make_error();
    }
    return expressions[index]; 
} 

te_expr *te_compile(const char *expression, const te_variable *variables, int var_count, int *error) {
    state s;
    memset(&s, 0, sizeof(state));
    s.start = s.next = expression;
    s.lookup = variables;
    s.lookup_len = var_count;
    s.value_lookup = 0;
    s.value_lookup_len = 0;

    next_token(&s);
    te_expr *root = list(&s);
    if (root == NULL) {
        if (error) *error = -1;
        return NULL;
    }

    if (s.type != TOK_END) {
        te_free(root);
        if (error) {
            *error = (s.next - s.start);
            if (*error == 0) *error = 1;
        }
        return 0;
    } else {
        optimize(root);
        if (error) *error = 0;
        return root;
    }
}

te_expr *te_compile_value(const char *expression, const te_binding *bindings, int bind_count, int *error) {
    state s;
    memset(&s, 0, sizeof(state));
    s.start = s.next = expression;
    s.lookup = 0;
    s.lookup_len = 0;
    s.value_lookup = bindings;
    s.value_lookup_len = bind_count;

    next_token(&s);
    te_expr *root = list(&s);
    if (root == NULL) {
        if (error) *error = -1;
        return NULL;
    }

    if (s.type != TOK_END) {
        te_free(root);
        if (error) {
            *error = (s.next - s.start);
            if (*error == 0) *error = 1;
        }
        return 0;
    }

    if (error) *error = 0;
    return root;
}


double te_interp(const char *expression, int *error) {
    te_expr *n = te_compile(expression, 0, 0, error);

    double ret;
    if (n) {
        te_value value = te_eval_value(n);
        if (value.kind == TE_VAL_SCALAR) {
            ret = value.scalar;
        } else {
            ret = NAN;
            if (error) *error = 1;
        }
        te_free(n);
    } else {
        ret = NAN;
    }
    return ret;
}

te_value te_interp_value(const char *expression, const te_binding *bindings, int bind_count, int *error) {
    te_value ret = make_error();
    te_expr* n = 0;
    int store_expr = 0;
    char variable;
    const char *actual_expression = expression;
    char *expanded_expression = 0;

    if (strncmp(expression, "STORE", 5) == 0) {
        store_expr = 1;
        int actual_expr_len;

        if (expression[5] != '(' || expression[7] != ')' || expression[8] != ':') {
            return make_error();
        }
        if (expression[6] < 'A' || expression[6] > 'Z') {
            return make_error();
        }

        actual_expr_len = (int)strlen(expression) - 9;

        if (actual_expr_len <= 0) {
            return make_error();
        }
        
        variable = expression[6];
        actual_expression = expression + 9; /* STORE(A):... */
    }

    expanded_expression = expand_calculus_calls(actual_expression, bindings, bind_count, error);
    if (!expanded_expression) {
        return make_error();
    }

    actual_expression = expanded_expression;

    if (evaluate_calculus_call(actual_expression, bindings, bind_count, &ret, error)) {
        if (store_expr && ret.kind != TE_VAL_ERROR) {
            set_var(variable, ret);
        }
        free(expanded_expression);
        return ret;
    }

    n = te_compile_value(actual_expression, bindings, bind_count, error);

    if (n) {
        ret = te_eval_value(n);
        if (store_expr) {
            set_var(variable, ret);
        }
        te_free(n);
    }
    free(expanded_expression);
    return ret;
}

static void pn (const te_expr *n, int depth) {
    int i, arity;
    printf("%*s", depth, "");

    switch(TYPE_MASK(n->type)) {
    case TE_CONSTANT: printf("%f\n", n->value); break;
    case TE_VARIABLE: printf("bound %p\n", n->bound); break;
    case TE_VALUE_VARIABLE: printf("value bound %p\n", (const void*)n->value_bound); break;

    case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:
    case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
    case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:
    case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
         arity = ARITY(n->type);
         printf("f%d", arity);
         for(i = 0; i < arity; i++) {
             printf(" %p", n->parameters[i]);
         }
         printf("\n");
         for(i = 0; i < arity; i++) {
             pn(n->parameters[i], depth + 1);
         }
         break;
    }
}


void te_print(const te_expr *n) {
    pn(n, 0);
}



