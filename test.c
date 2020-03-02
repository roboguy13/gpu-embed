#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

typedef enum var_type_tag {
  EXPR_INT
, EXPR_FLOAT
, EXPR_DOUBLE
, EXPR_CHAR
, EXPR_BOOL
, EXPR_CLOSURE
, EXPR_EITHER_LEFT
, EXPR_EITHER_RIGHT
, EXPR_PAIR
, EXPR_UNIT
, EXPR_STEP
, EXPR_DONE
, EXPR_UNBOXED
} var_type_tag;

struct closure_t;

typedef struct var_t {
  var_type_tag tag;
  void* value;
} var_t;

typedef struct closure_t {
  var_t* fv_env;
  var_t (*fn)(var_t, struct closure_t*);
} closure_t;

var_t vars[0];

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

bool isIterTag(var_type_tag tag) {
  return tag == EXPR_STEP || tag == EXPR_DONE;
}

var_t lam_0(var_t, struct closure_t*);


var_t lam_0(var_t arg, struct closure_t* self) {
  var_t x1;
x1.tag = EXPR_STEP;
x1.value = malloc(sizeof(var_t));
*(var_t*)(x1.value) = arg;
while (x1.tag != EXPR_DONE) {
var_t x2;
var_t x3;
var_t x4;

var_t x5;
var_t x6;

if (isIterTag(x1.tag)) {
x5 = *(var_t*)(x1.value);
} else {
x5 = x1;
}


x6.value = malloc(sizeof(int));
x6.tag = EXPR_INT;
*(int*)(x6.value) = 0;


x2.tag = EXPR_BOOL;
x2.value = malloc(sizeof(bool));
*(bool*)(x2.value) = *(int*)(x5.value) == *(int*)(x6.value);


if (*(bool*)(x2.value)) {
var_t x7;
x7.tag = EXPR_BOOL;
x7.value = malloc(sizeof(bool));
*(bool*)(x7.value) = true;

x1.tag = EXPR_DONE;
x1.value = malloc(sizeof(var_t));
*(var_t*)(x1.value) = x7;

} else {
var_t x8;
var_t x9;
var_t x10;

var_t x11;
var_t x12;

if (isIterTag(x1.tag)) {
x11 = *(var_t*)(x1.value);
} else {
x11 = x1;
}


x12.value = malloc(sizeof(int));
x12.tag = EXPR_INT;
*(int*)(x12.value) = 1;


x8.tag = EXPR_BOOL;
x8.value = malloc(sizeof(bool));
*(bool*)(x8.value) = *(int*)(x11.value) == *(int*)(x12.value);


if (*(bool*)(x8.value)) {
var_t x13;
x13.tag = EXPR_BOOL;
x13.value = malloc(sizeof(bool));
*(bool*)(x13.value) = false;

x1.tag = EXPR_DONE;
x1.value = malloc(sizeof(var_t));
*(var_t*)(x1.value) = x13;

} else {
var_t x14;
var_t x15;
var_t x16;
if (isIterTag(x1.tag)) {
x15 = *(var_t*)(x1.value);
} else {
x15 = x1;
}

x16.value = malloc(sizeof(int));
x16.tag = EXPR_INT;
*(int*)(x16.value) = 2;

MATH_OP(-, x14, x15, x16);

x1.tag = EXPR_STEP;
x1.value = malloc(sizeof(var_t));
*(var_t*)(x1.value) = x14;

}

}

}

var_t x17 = *(var_t*)(x1.value);
x1.tag = x17.tag;
x1.value = x17.value;

  return x1;
}


var_t top_level() {
  var_t x0;
var_t x18;
closure_t x19;
var_t x20;

x18.value = malloc(sizeof(int));
x18.tag = EXPR_INT;
*(int*)(x18.value) = 6;

closure_t x21;
x21.fv_env = malloc(sizeof(var_t)*2);
x21.fn = &lam_0;
x21.fv_env[0] = x18;
x21.fv_env[1] = x18;


closure_t* x22 = malloc(sizeof(closure_t));
x22->fn = x21.fn;
x22->fv_env = malloc(sizeof(var_t)*2);
memcpy(x22->fv_env, x21.fv_env, sizeof(var_t)*2);

x20.tag = EXPR_CLOSURE;
x20.value = (void*)x22;

memcpy(&x19, (closure_t*)(x20.value), sizeof(closure_t));
x0 = x19.fn(x18, &x19);

  return x0;
}

int main() {
  var_t r = top_level();

  printf("%d\n", r.tag);
  printf("%d\n", *(bool*)r.value);
}

