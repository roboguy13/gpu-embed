#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef enum var_type_tag {
  EXPR_INT
, EXPR_FLOAT
, EXPR_DOUBLE
, EXPR_CHAR
, EXPR_CLOSURE
, EXPR_EITHER_LEFT
, EXPR_EITHER_RIGHT
, EXPR_PAIR
, EXPR_UNIT
, EXPR_UNBOXED
} var_type_tag;

typedef struct var_t {
  var_type_tag tag;
  void* value;
} var_t;

typedef struct closure_t {
  var_t* fv_env;
  var_t (*fn)(var_t, struct closure_t*);
} closure_t;

var_t vars[1];

#define MATH_OP(op, result, a, b)\
  do {\
    assert((a).tag == (b).tag);\
    (result).tag = (a).tag;\
    switch ((a).tag) {\
      case EXPR_INT:\
        (result).value = malloc(sizeof(int));\
        *((int*)(result).value) = *(int*)((a).value) op *(int*)((b).value);\
        break;\
      case EXPR_FLOAT:\
        (result).value = malloc(sizeof(float));\
        *((float*)(result).value) = *(float*)((a).value) op *(float*)((b).value);\
        break;\
      case EXPR_DOUBLE:\
        (result).value = malloc(sizeof(double));\
        *((double*)(result).value) = *(double*)((a).value) op *(double*)((b).value);\
        break;\
      default:\
       fprintf(stderr, "type tag = %d\n", a.tag);\
       assert(0 && "Attempting to perform arithmetic on non-numeric types");\
    }\
  } while (0);

var_t lam_1(var_t, struct closure_t*);
var_t lam_2(var_t, struct closure_t*);


var_t lam_1(var_t arg, struct closure_t* self) {
  var_t x1;
closure_t x2;
x2.fv_env = malloc(sizeof(var_t)*2);
x2.fn = &lam_2;
x2.fv_env[0] = vars[0];
x2.fv_env[1] = self->fv_env[0];


closure_t* x3 = malloc(sizeof(closure_t));
x3->fn = x2.fn;
x3->fv_env = x2.fv_env;

x1.tag = EXPR_CLOSURE;
x1.value = (void*)x3;

  return x1;
}

var_t lam_2(var_t arg, struct closure_t* self) {
  var_t x4;
var_t x5;
var_t x6;
x5 = self->fv_env[1];
x6 = self->fv_env[1];
MATH_OP(*, x4, x5, x6);

  return x4;
}


var_t top_level() {
  var_t x0;
var_t x7;
x7 = vars[0];
closure_t x8;
x8.fv_env = malloc(sizeof(var_t)*2);
x8.fn = &lam_2;
x8.fv_env[0] = vars[0];
x8.fv_env[1] = ((var_t*)x7.value)[0];


x0 = x8.fn(((var_t*)x7.value)[1], &x8);


  return x0;
}

int main() {
  vars[0].tag = EXPR_PAIR;
  vars[0].value = malloc(sizeof(var_t)*2);

  ((var_t*)(vars)[0].value)[0].tag = EXPR_INT;
  ((var_t*)(vars)[0].value)[0].value = malloc(sizeof(int));
  *(int*)((var_t*)(vars)[0].value)[0].value = 3;

  ((var_t*)(vars)[0].value)[1].tag = EXPR_INT;
  ((var_t*)(vars)[0].value)[1].value = malloc(sizeof(int));
  *(int*)((var_t*)(vars)[0].value)[1].value = 2;

  var_t r = top_level();

  printf("%d\n", *(int*)r.value);
}
