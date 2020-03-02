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
       fprintf(stderr, "type tag = %d\n", (a).tag);\
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

closure_t* x6 = malloc(sizeof(closure_t));
(*x6).fv_env = malloc(sizeof(var_t)*1);
(*x6).fn = &lam_2;
(*x6).fv_env[0] = arg;



x5.tag = EXPR_CLOSURE;
x5.value = (void*)x6;

  return x5;
}

var_t lam_2(var_t arg, struct closure_t* self) {
  var_t x8;
var_t x9;
var_t x10;
var_t x11;

var_t x12;
var_t x13;

if (isIterTag(self->fv_env[0].tag)) {
x12 = *(var_t*)(self->fv_env[0].value);
} else {
x12 = self->fv_env[0];
}


x13.value = malloc(sizeof(int));
x13.tag = EXPR_INT;
*(int*)(x13.value) = 0;


x9.tag = EXPR_BOOL;
x9.value = malloc(sizeof(bool));
*(bool*)(x9.value) = *(int*)(x12.value) == *(int*)(x13.value);


if (*(bool*)(x9.value)) {
var_t x14;
if (isIterTag(arg.tag)) {
x14 = *(var_t*)(arg.value);
} else {
x14 = arg;
}

x8.tag = EXPR_DONE;
x8.value = malloc(sizeof(var_t));
*(var_t*)(x8.value) = x14;

} else {
var_t x15;
var_t x16;
var_t x17;
var_t x18;
var_t x19;
if (isIterTag(self->fv_env[0].tag)) {
x18 = *(var_t*)(self->fv_env[0].value);
} else {
x18 = self->fv_env[0];
}

x19.value = malloc(sizeof(int));
x19.tag = EXPR_INT;
*(int*)(x19.value) = 1;

MATH_OP(-, x16, x18, x19);

var_t x20;
var_t x21;
if (isIterTag(self->fv_env[0].tag)) {
x20 = *(var_t*)(self->fv_env[0].value);
} else {
x20 = self->fv_env[0];
}

if (isIterTag(arg.tag)) {
x21 = *(var_t*)(arg.value);
} else {
x21 = arg;
}

MATH_OP(*, x17, x20, x21);

x15.tag = EXPR_PAIR;
x15.value = malloc(sizeof(var_t)*2);
((var_t*)(x15.value))[0] = x16;
((var_t*)(x15.value))[1] = x17;

x8.tag = EXPR_STEP;
x8.value = malloc(sizeof(var_t));
*(var_t*)(x8.value) = x15;

}

  return x8;
}


var_t top_level() {
  var_t x0;
var_t x23;
closure_t x26;
var_t x27;

var_t x24;
var_t x25;
x24.value = malloc(sizeof(int));
x24.tag = EXPR_INT;
*(int*)(x24.value) = 5;

x25.value = malloc(sizeof(int));
x25.tag = EXPR_INT;
*(int*)(x25.value) = 1;

x23.tag = EXPR_PAIR;
x23.value = malloc(sizeof(var_t)*2);
((var_t*)(x23.value))[0] = x24;
((var_t*)(x23.value))[1] = x25;


closure_t* x28 = malloc(sizeof(closure_t));
(*x28).fv_env = malloc(sizeof(var_t)*0);
(*x28).fn = &lam_0;



x27.tag = EXPR_CLOSURE;
x27.value = (void*)x28;

memcpy(&x26, (closure_t*)(x27.value), sizeof(closure_t));
x0 = x26.fn(x23, &x26);

  return x0;
}

int main() {
  var_t r = top_level();
  printf("%d\n", *(int*)r.value);
}

