#include <stdio.h>
#include <tinyexpr.h>

void disp(te_value value) {
    switch (value.kind) {
        case TE_VAL_VEC3:
            printf("<%.6f, %.6f, %.6f>\n", value.vec3.x, value.vec3.y, value.vec3.z);
            break;
        case TE_VAL_SCALAR:
            printf("%.6f\n", value.scalar);
            break;
        case TE_VAL_ERROR:
            printf("TE_VAL_ERROR\n");
            break;
        default:
            printf("ERROR\n");
            break;
    }
}