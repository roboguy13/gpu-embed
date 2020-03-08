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
, EXPR_COMPLEX     // Complex numbers
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

var_t vars[23];

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

var_t lam_19(var_t, struct closure_t*);
var_t lam_21(var_t, struct closure_t*);
var_t lam_20(var_t, struct closure_t*);
var_t lam_23(var_t, struct closure_t*);
var_t lam_22(var_t, struct closure_t*);


var_t lam_19(var_t arg, struct closure_t* self) {
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
x3.fn = &lam_20;
x3.fv_env[0] = ((var_t*)x2.value)[0];


x1 = x3.fn(((var_t*)x2.value)[1], &x3);


}

var_t x4 = *(var_t*)(x1.value);
x1.tag = x4.tag;
x1.value = x4.value;

  return x1;
}

var_t lam_21(var_t arg, struct closure_t* self) {
  var_t x5;
closure_t* x6 = malloc(sizeof(closure_t));
(*x6).fv_env = malloc(sizeof(var_t)*1);
(*x6).fn = &lam_20;
(*x6).fv_env[0] = arg;



x5.tag = EXPR_CLOSURE;
x5.value = (void*)x6;

  return x5;
}

var_t lam_20(var_t arg, struct closure_t* self) {
  var_t x8;
var_t x9;
if (isIterTag(arg.tag)) {
x9 = *(var_t*)(arg.value);
} else {
x9 = arg;
}

assert(x9.tag == EXPR_EITHER_LEFT || x9.tag == EXPR_EITHER_RIGHT);
var_t x10 = *(var_t*)(x9.value);
if (x9.tag == EXPR_EITHER_LEFT) {
var_t x11;
if (isIterTag(self->fv_env[0].tag)) {
x11 = *(var_t*)(self->fv_env[0].value);
} else {
x11 = self->fv_env[0];
}

x8.tag = EXPR_DONE;
x8.value = malloc(sizeof(var_t));
*(var_t*)(x8.value) = x11;

} else if (x9.tag == EXPR_EITHER_RIGHT) {
closure_t x12;
x12.fv_env = malloc(sizeof(var_t)*2);
x12.fn = &lam_22;
x12.fv_env[0] = self->fv_env[0];
x12.fv_env[1] = ((var_t*)x10.value)[0];


x8 = x12.fn(((var_t*)x10.value)[1], &x12);

}


  return x8;
}

var_t lam_23(var_t arg, struct closure_t* self) {
  var_t x14;
closure_t* x15 = malloc(sizeof(closure_t));
(*x15).fv_env = malloc(sizeof(var_t)*2);
(*x15).fn = &lam_22;
(*x15).fv_env[0] = self->fv_env[0];
(*x15).fv_env[1] = arg;



x14.tag = EXPR_CLOSURE;
x14.value = (void*)x15;

  return x14;
}

var_t lam_22(var_t arg, struct closure_t* self) {
  var_t x17;
var_t x18;
var_t x19;
var_t x20;
var_t x21;
var_t x22;
if (isIterTag(self->fv_env[1].tag)) {
x21 = *(var_t*)(self->fv_env[1].value);
} else {
x21 = self->fv_env[1];
}

if (isIterTag(self->fv_env[0].tag)) {
x22 = *(var_t*)(self->fv_env[0].value);
} else {
x22 = self->fv_env[0];
}

MATH_OP(+, x19, x21, x22);

if (isIterTag(arg.tag)) {
x20 = *(var_t*)(arg.value);
} else {
x20 = arg;
}

x18.tag = EXPR_PAIR;
x18.value = malloc(sizeof(var_t)*2);
((var_t*)(x18.value))[0] = x19;
((var_t*)(x18.value))[1] = x20;

x17.tag = EXPR_STEP;
x17.value = malloc(sizeof(var_t));
*(var_t*)(x17.value) = x18;

  return x17;
}


var_t top_level() {
  var_t x0;
var_t x24;
closure_t x40;
var_t x41;

var_t x25;
var_t x26;
x25.value = malloc(sizeof(int));
x25.tag = EXPR_INT;
*(int*)(x25.value) = 0;

var_t x27;
var_t x28;
var_t x29;
x28.value = malloc(sizeof(int));
x28.tag = EXPR_INT;
*(int*)(x28.value) = 10;

var_t x30;
var_t x31;
var_t x32;
x31.value = malloc(sizeof(int));
x31.tag = EXPR_INT;
*(int*)(x31.value) = 100;

var_t x33;
var_t x34;
var_t x35;
x34.value = malloc(sizeof(int));
x34.tag = EXPR_INT;
*(int*)(x34.value) = 1000;

var_t x36;
var_t x37;
var_t x38;
x37.value = malloc(sizeof(int));
x37.tag = EXPR_INT;
*(int*)(x37.value) = 10000;

var_t x39;
x39.tag = EXPR_UNIT;
x39.value = 0;

x38.tag = EXPR_EITHER_LEFT;
x38.value = malloc(sizeof(var_t));
*(var_t*)(x38.value) = x39;

x36.tag = EXPR_PAIR;
x36.value = malloc(sizeof(var_t)*2);
((var_t*)(x36.value))[0] = x37;
((var_t*)(x36.value))[1] = x38;

x35.tag = EXPR_EITHER_RIGHT;
x35.value = malloc(sizeof(var_t));
*(var_t*)(x35.value) = x36;

x33.tag = EXPR_PAIR;
x33.value = malloc(sizeof(var_t)*2);
((var_t*)(x33.value))[0] = x34;
((var_t*)(x33.value))[1] = x35;

x32.tag = EXPR_EITHER_RIGHT;
x32.value = malloc(sizeof(var_t));
*(var_t*)(x32.value) = x33;

x30.tag = EXPR_PAIR;
x30.value = malloc(sizeof(var_t)*2);
((var_t*)(x30.value))[0] = x31;
((var_t*)(x30.value))[1] = x32;

x29.tag = EXPR_EITHER_RIGHT;
x29.value = malloc(sizeof(var_t));
*(var_t*)(x29.value) = x30;

x27.tag = EXPR_PAIR;
x27.value = malloc(sizeof(var_t)*2);
((var_t*)(x27.value))[0] = x28;
((var_t*)(x27.value))[1] = x29;

x26.tag = EXPR_EITHER_RIGHT;
x26.value = malloc(sizeof(var_t));
*(var_t*)(x26.value) = x27;

x24.tag = EXPR_PAIR;
x24.value = malloc(sizeof(var_t)*2);
((var_t*)(x24.value))[0] = x25;
((var_t*)(x24.value))[1] = x26;

closure_t* x42 = malloc(sizeof(closure_t));
(*x42).fv_env = malloc(sizeof(var_t)*0);
(*x42).fn = &lam_19;



x41.tag = EXPR_CLOSURE;
x41.value = (void*)x42;

memcpy(&x40, (closure_t*)(x41.value), sizeof(closure_t));
x0 = x40.fn(x24, &x40);

  return x0;
}

int main() {
  var_t r = top_level();
  printf("%d\n", *(int*)r.value);
}

