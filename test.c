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

var_t vars[2];

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
var_t lam_1(var_t, struct closure_t*);
var_t lam_2(var_t, struct closure_t*);


var_t lam_0(var_t arg, struct closure_t* self) {
  var_t x1;
x1.tag = EXPR_STEP;
x1.value = malloc(sizeof(var_t));
*(var_t*)(x1.value) = arg;
while (x1.tag != EXPR_DONE) {
var_t x2;
if (isIterTag(x1.tag)) {
x2 = *(var_t*)(x1.value);
} else {
x2 = x1;
}

closure_t x3;
x3.fv_env = malloc(sizeof(var_t)*1);
x3.fn = &lam_2;
x3.fv_env[0] = ((var_t*)x2.value)[0];


x1 = x3.fn(((var_t*)x2.value)[1], &x3);


}

var_t x4 = *(var_t*)(x1.value);
x1.tag = x4.tag;
x1.value = x4.value;

  return x1;
}

var_t lam_1(var_t arg, struct closure_t* self) {
  var_t x5;
closure_t x6;
x6.fv_env = malloc(sizeof(var_t)*1);
x6.fn = &lam_2;
x6.fv_env[0] = arg;


closure_t* x7 = malloc(sizeof(closure_t));
x7->fn = x6.fn;
x7->fv_env = malloc(sizeof(var_t)*1);
memcpy(x7->fv_env, x6.fv_env, sizeof(var_t)*1);

x5.tag = EXPR_CLOSURE;
x5.value = (void*)x7;

  return x5;
}

var_t lam_2(var_t arg, struct closure_t* self) {
  var_t x9;
var_t x10;
var_t x11;
var_t x12;

var_t x13;
var_t x14;

if (isIterTag(self->fv_env[0].tag)) {
x13 = *(var_t*)(self->fv_env[0].value);
} else {
x13 = self->fv_env[0];
}


x14.value = malloc(sizeof(int));
x14.tag = EXPR_INT;
*(int*)(x14.value) = 0;


x10.tag = EXPR_BOOL;
x10.value = malloc(sizeof(bool));
*(bool*)(x10.value) = *(int*)(x13.value) == *(int*)(x14.value);


if (*(bool*)(x10.value)) {
var_t x15;
if (isIterTag(arg.tag)) {
x15 = *(var_t*)(arg.value);
} else {
x15 = arg;
}

x9.tag = EXPR_DONE;
x9.value = malloc(sizeof(var_t));
*(var_t*)(x9.value) = x15;

} else {
var_t x16;
var_t x17;
var_t x18;
var_t x19;
var_t x20;
if (isIterTag(self->fv_env[0].tag)) {
x19 = *(var_t*)(self->fv_env[0].value);
} else {
x19 = self->fv_env[0];
}

x20.value = malloc(sizeof(int));
x20.tag = EXPR_INT;
*(int*)(x20.value) = 1;

MATH_OP(-, x17, x19, x20);

var_t x21;
var_t x22;
if (isIterTag(self->fv_env[0].tag)) {
x21 = *(var_t*)(self->fv_env[0].value);
} else {
x21 = self->fv_env[0];
}

if (isIterTag(arg.tag)) {
x22 = *(var_t*)(arg.value);
} else {
x22 = arg;
}

MATH_OP(*, x18, x21, x22);

x16.tag = EXPR_PAIR;
x16.value = malloc(sizeof(var_t)*2);
((var_t*)(x16.value))[0] = x17;
((var_t*)(x16.value))[1] = x18;

x9.tag = EXPR_STEP;
x9.value = malloc(sizeof(var_t));
*(var_t*)(x9.value) = x16;

}

  return x9;
}


var_t top_level() {
  var_t x0;
var_t x24;
closure_t x27;
var_t x28;

var_t x25;
var_t x26;
x25.value = malloc(sizeof(int));
x25.tag = EXPR_INT;
*(int*)(x25.value) = 5;

x26.value = malloc(sizeof(int));
x26.tag = EXPR_INT;
*(int*)(x26.value) = 1;

x24.tag = EXPR_PAIR;
x24.value = malloc(sizeof(var_t)*2);
((var_t*)(x24.value))[0] = x25;
((var_t*)(x24.value))[1] = x26;

closure_t x29;
x29.fv_env = malloc(sizeof(var_t)*0);
x29.fn = &lam_0;


closure_t* x30 = malloc(sizeof(closure_t));
x30->fn = x29.fn;
x30->fv_env = malloc(sizeof(var_t)*0);
memcpy(x30->fv_env, x29.fv_env, sizeof(var_t)*0);

x28.tag = EXPR_CLOSURE;
x28.value = (void*)x30;

memcpy(&x27, (closure_t*)(x28.value), sizeof(closure_t));
x0 = x27.fn(x24, &x27);

  return x0;
}
int main() {
  var_t v = top_level();

  printf("%d\n", *(int*)v.value);
}
