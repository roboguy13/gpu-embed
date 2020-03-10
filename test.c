#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <math.h>

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

var_t vars[69];

#define GET_MATH_OP_ADD +
#define GET_MATH_OP_MUL *
#define GET_MATH_OP_SUB -
#define GET_MATH_OP_DIV /

#define GET_COMPARE_OP_LTE <=
#define GET_COMPARE_OP_LT <
#define GET_COMPARE_OP_GTE >=
#define GET_COMPARE_OP_GT >
#define GET_COMPARE_OP_EQUAL ==

  // Remove any additional wrappers (for instance, a EXPR_COMPLEX wraps a EXPR_PAIR
#define UNWRAP(result, x)\
  do {\
    if ((x).tag == EXPR_COMPLEX) {\
      result = *((var_t*)((x).value));\
    } else {\
      result = x;\
    }\
  } while (0);

#define MATH_OP(op, result, a, b)\
  do {\
    assert((a).tag == (b).tag);\
    (result).tag = (a).tag;\
    switch ((a).tag) {\
      case EXPR_INT:\
        (result).value = malloc(sizeof(int));\
        *((int*)(result).value) = *(int*)((a).value) GET_MATH_OP_##op *(int*)((b).value);\
        break;\
      case EXPR_FLOAT:\
        (result).value = malloc(sizeof(float));\
        *((float*)(result).value) = *(float*)((a).value) GET_MATH_OP_##op *(float*)((b).value);\
        break;\
      case EXPR_DOUBLE:\
        (result).value = malloc(sizeof(double));\
        *((double*)(result).value) = *(double*)((a).value) GET_MATH_OP_##op *(double*)((b).value);\
        break;\
      default:\
        fprintf(stderr, "%s type tag = %d\n", #a, (a).tag);\
        assert(0 && "Attempting to perform arithmetic on non-numeric types");\
    }\
  } while (0);

#define COMPARE(op, result, a, b)\
  do {\
   assert((a).tag == (b).tag);\
    switch ((a).tag) {\
      case EXPR_INT:\
        *((int*)(result).value) = *(int*)((a).value) GET_COMPARE_OP_##op *(int*)((b).value);\
        break;\
      case EXPR_FLOAT:\
        *((float*)(result).value) = *(float*)((a).value) GET_COMPARE_OP_##op *(float*)((b).value);\
        break;\
      case EXPR_DOUBLE:\
        *((double*)(result).value) = *(double*)((a).value) GET_COMPARE_OP_##op *(double*)((b).value);\
        break;\
      case EXPR_BOOL:\
        *((bool*)(result).value) = *(bool*)((a).value) GET_COMPARE_OP_##op *(bool*)((b).value);\
        break;\
      case EXPR_CHAR:\
        *((char*)(result).value) = *(char*)((a).value) GET_COMPARE_OP_##op *(char*)((b).value);\
        break;\
      default:\
        fprintf(stderr, "%s type tag = %d\n", #a, (a).tag);\
        assert(0 && "Cannot compare given type for equality");\
    }\
  } while (0);

#define CAST_TO(result, r_type, a)\
  do {\
    switch ((a).tag) {\
      case EXPR_INT:\
        *((r_type*)(result).value) = (r_type) *(int*)((a).value);\
        break;\
      case EXPR_FLOAT:\
        *((r_type*)(result).value) = (r_type) *(float*)((a).value);\
        break;\
      case EXPR_DOUBLE:\
        *((r_type*)(result).value) = (r_type) *(double*)((a).value);\
        break;\
      default:\
        fprintf(stderr, "%s type tag = %d\n", #a, (a).tag);\
        assert(0 && "CAST_FROM: Invalid type tag");\
    }\
  } while (0);

#define MATH_SQRT(result, a)\
  do {\
      case EXPR_FLOAT:\
        *((float*)(result).value) = sqrt(*(float*)((a).value));\
        break;\
      case EXPR_DOUBLE:\
        *((double*)(result).value) = sqrt(*(double*)((a).value));\
        break;\
  } while(0);

#define INIT_COMPLEX(a, type, eTag)\
  do {\
    (a).tag = EXPR_COMPLEX;\
    (a).value = malloc(sizeof(var_t));\
    ((var_t*)((a).value))->tag = EXPR_PAIR;\
    ((var_t*)((a).value))->value = malloc(2*sizeof(var_t));\
    ((var_t*)(((var_t*)((a).value))->value))[0].tag = eTag;\
    ((var_t*)(((var_t*)((a).value))->value))[1].tag = eTag;\
    ((var_t*)(((var_t*)((a).value))->value))[0].value = malloc(sizeof(type));\
    ((var_t*)(((var_t*)((a).value))->value))[1].value = malloc(sizeof(type));\
  } while (0);

#define PAIR_FST(result, p)\
  do {\
    assert((p).tag == EXPR_PAIR);\
    (result) = ((var_t*)((p).value))[0];\
  } while(0);

#define PAIR_SND(result, p)\
  do {\
    assert((p).tag == EXPR_PAIR);\
    (result) = ((var_t*)((p).value))[1];\
  } while(0);

#define PAIR_ASSIGN_FST(result, x)\
  do {\
    ((var_t*)((result).value))[0] = (x);\
  } while(0);

#define PAIR_ASSIGN_SND(result, x)\
  do {\
    ((var_t*)((result).value))[1] = (x);\
  } while(0);

#define COMPLEX_REAL(result, c)\
  do {\
    assert((p).tag == EXPR_COMPLEX);\
    PAIR_FST(result, *((var_t*)((c).value)));\
  } while (0);

#define COMPLEX_IMAG(result, c)\
  do {\
    assert((c).tag == EXPR_COMPLEX);\
    PAIR_SND(result, *((var_t*)((c).value)));\
  } while (0);

#define COMPLEX_ASSIGN_REAL(result, x)\
  do {\
    PAIR_ASSIGN_FST(*((var_t*)((result).value)), x);\
  } while(0);

#define COMPLEX_ASSIGN_IMAG(result, x)\
  do {\
    PAIR_ASSIGN_SND(*((var_t*)((result).value)), x);\
  } while(0);

bool isIterTag(var_type_tag tag) {
  return tag == EXPR_STEP || tag == EXPR_DONE;
}

var_t lam_62(var_t, struct closure_t*);
var_t lam_65(var_t, struct closure_t*);
var_t lam_64(var_t, struct closure_t*);
var_t lam_63(var_t, struct closure_t*);
var_t lam_67(var_t, struct closure_t*);
var_t lam_66(var_t, struct closure_t*);
var_t lam_69(var_t, struct closure_t*);
var_t lam_68(var_t, struct closure_t*);


var_t lam_62(var_t arg, struct closure_t* self) {
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

var_t x3;
UNWRAP(x3, x2);
closure_t x4;
x4.fv_env = malloc(sizeof(var_t)*2);
x4.fn = &lam_63;
x4.fv_env[0] = ((var_t*)x3.value)[1];
x4.fv_env[1] = ((var_t*)x3.value)[0];


x1 = x4.fn(((var_t*)(((var_t*)x3.value)[1]).value)[1], &x4);



}

var_t x5 = *(var_t*)(x1.value);
x1.tag = x5.tag;
x1.value = x5.value;

  return x1;
}

var_t lam_65(var_t arg, struct closure_t* self) {
  var_t x6;
closure_t* x7 = malloc(sizeof(closure_t));
(*x7).fv_env = malloc(sizeof(var_t)*1);
(*x7).fn = &lam_64;
(*x7).fv_env[0] = arg;



x6.tag = EXPR_CLOSURE;
x6.value = (void*)x7;

  return x6;
}

var_t lam_64(var_t arg, struct closure_t* self) {
  var_t x9;
closure_t* x10 = malloc(sizeof(closure_t));
(*x10).fv_env = malloc(sizeof(var_t)*2);
(*x10).fn = &lam_63;
(*x10).fv_env[0] = arg;
(*x10).fv_env[1] = self->fv_env[0];



x9.tag = EXPR_CLOSURE;
x9.value = (void*)x10;

  return x9;
}

var_t lam_63(var_t arg, struct closure_t* self) {
  var_t x12;
var_t x13;
var_t x14;
var_t x15;

var_t x16;
var_t x17;
if (isIterTag(self->fv_env[1].tag)) {
x16 = *(var_t*)(self->fv_env[1].value);
} else {
x16 = self->fv_env[1];
}

// oneDimNumCode
x17.value = malloc(sizeof(int));
x17.tag = EXPR_INT;
*(int*)(x17.value) = 50;

assert(x16.tag == x17.tag);

x13.tag = EXPR_BOOL;
x13.value = malloc(sizeof(bool));
if (x13.tag == EXPR_COMPLEX) {
  COMPARE(EQUAL, x13, ((var_t*)(x16.value))[0], ((var_t*)(x17.value))[0]);
  COMPARE(EQUAL, x13, ((var_t*)(x16.value))[1], ((var_t*)(x17.value))[1]);
} else {
  COMPARE(EQUAL, x13, x16, x17);
}


if (*(bool*)(x13.value)) {
var_t x18;
// ConstructRep (Non-Complex)
var_t x19;
x19.tag = EXPR_UNIT;
x19.value = 0;

x18.tag = EXPR_EITHER_LEFT;
x18.value = malloc(sizeof(var_t));
*(var_t*)(x18.value) = x19;


x12.tag = EXPR_DONE;
x12.value = malloc(sizeof(var_t));
*(var_t*)(x12.value) = x18;

} else {
var_t x20;
if (isIterTag(arg.tag)) {
x20 = *(var_t*)(arg.value);
} else {
x20 = arg;
}

var_t x21;
UNWRAP(x21, x20);
closure_t x22;
x22.fv_env = malloc(sizeof(var_t)*4);
x22.fn = &lam_66;
x22.fv_env[0] = arg;
x22.fv_env[1] = self->fv_env[0];
x22.fv_env[2] = self->fv_env[1];
x22.fv_env[3] = ((var_t*)x21.value)[0];


x12 = x22.fn(((var_t*)x21.value)[1], &x22);



}

  return x12;
}

var_t lam_67(var_t arg, struct closure_t* self) {
  var_t x24;
closure_t* x25 = malloc(sizeof(closure_t));
(*x25).fv_env = malloc(sizeof(var_t)*4);
(*x25).fn = &lam_66;
(*x25).fv_env[0] = self->fv_env[0];
(*x25).fv_env[1] = self->fv_env[1];
(*x25).fv_env[2] = self->fv_env[2];
(*x25).fv_env[3] = arg;



x24.tag = EXPR_CLOSURE;
x24.value = (void*)x25;

  return x24;
}

var_t lam_66(var_t arg, struct closure_t* self) {
  var_t x27;
var_t x28;
var_t x29;
var_t x30;

var_t x31;
var_t x32;
// Add
var_t x33;
var_t x34;
// Mul
var_t x35;
var_t x36;
if (isIterTag(self->fv_env[3].tag)) {
x35 = *(var_t*)(self->fv_env[3].value);
} else {
x35 = self->fv_env[3];
}

if (isIterTag(self->fv_env[3].tag)) {
x36 = *(var_t*)(self->fv_env[3].value);
} else {
x36 = self->fv_env[3];
}

x33.tag = EXPR_COMPLEX;

if (x35.tag == EXPR_COMPLEX) {
  var_t x37;
  var_t x38;
  var_t x39;
  var_t x40;
  var_t x41;
  var_t x42;
  MATH_OP(MUL, x37, ((var_t*)(x35.value))[0], ((var_t*)(x36.value))[0]);
  MATH_OP(MUL, x38, ((var_t*)(x35.value))[0], ((var_t*)(x36.value))[1]);
  MATH_OP(MUL, x39, ((var_t*)(x35.value))[1], ((var_t*)(x36.value))[0]);
  MATH_OP(MUL, x40, ((var_t*)(x35.value))[1], ((var_t*)(x36.value))[1]);

  MATH_OP(SUB, x41, x37, x40);
  MATH_OP(ADD, x42, x38, x39);
  x33.tag = EXPR_COMPLEX;
  COMPLEX_ASSIGN_REAL(x33, x41);
  COMPLEX_ASSIGN_IMAG(x33, x42);
} else {
  MATH_OP(MUL, x33, x35, x36);
}

// Mul
var_t x43;
var_t x44;
if (isIterTag(arg.tag)) {
x43 = *(var_t*)(arg.value);
} else {
x43 = arg;
}

if (isIterTag(arg.tag)) {
x44 = *(var_t*)(arg.value);
} else {
x44 = arg;
}

x34.tag = EXPR_COMPLEX;

if (x43.tag == EXPR_COMPLEX) {
  var_t x45;
  var_t x46;
  var_t x47;
  var_t x48;
  var_t x49;
  var_t x50;
  MATH_OP(MUL, x45, ((var_t*)(x43.value))[0], ((var_t*)(x44.value))[0]);
  MATH_OP(MUL, x46, ((var_t*)(x43.value))[0], ((var_t*)(x44.value))[1]);
  MATH_OP(MUL, x47, ((var_t*)(x43.value))[1], ((var_t*)(x44.value))[0]);
  MATH_OP(MUL, x48, ((var_t*)(x43.value))[1], ((var_t*)(x44.value))[1]);

  MATH_OP(SUB, x49, x45, x48);
  MATH_OP(ADD, x50, x46, x47);
  x34.tag = EXPR_COMPLEX;
  COMPLEX_ASSIGN_REAL(x34, x49);
  COMPLEX_ASSIGN_IMAG(x34, x50);
} else {
  MATH_OP(MUL, x34, x43, x44);
}

assert(x33.tag == x34.tag);

if (x33.tag == EXPR_COMPLEX) {
  MATH_OP(ADD, ((var_t*)(x31.value))[0], ((var_t*)(x33.value))[0], ((var_t*)(x34.value))[0]); 
  MATH_OP(ADD, ((var_t*)(x31.value))[1], ((var_t*)(x33.value))[1], ((var_t*)(x34.value))[1]); 
} else {
  MATH_OP(ADD, x31, x33, x34);
}

// oneDimNumCode
x32.value = malloc(sizeof(double));
x32.tag = EXPR_DOUBLE;
*(double*)(x32.value) = 4.0;

assert(x31.tag == x32.tag);
COMPARE(GT, x28, x31, x32);


if (*(bool*)(x28.value)) {
var_t x51;
// ConstructRep (Non-Complex)
var_t x52;
if (isIterTag(self->fv_env[2].tag)) {
x52 = *(var_t*)(self->fv_env[2].value);
} else {
x52 = self->fv_env[2];
}

x51.tag = EXPR_EITHER_RIGHT;
x51.value = malloc(sizeof(var_t));
*(var_t*)(x51.value) = x52;


x27.tag = EXPR_DONE;
x27.value = malloc(sizeof(var_t));
*(var_t*)(x27.value) = x51;

} else {
var_t x53;
// ConstructRep (Non-Complex)
var_t x54;
var_t x55;
// Add
var_t x56;
var_t x57;
if (isIterTag(self->fv_env[2].tag)) {
x56 = *(var_t*)(self->fv_env[2].value);
} else {
x56 = self->fv_env[2];
}

// oneDimNumCode
x57.value = malloc(sizeof(int));
x57.tag = EXPR_INT;
*(int*)(x57.value) = 1;

assert(x56.tag == x57.tag);

if (x56.tag == EXPR_COMPLEX) {
  MATH_OP(ADD, ((var_t*)(x54.value))[0], ((var_t*)(x56.value))[0], ((var_t*)(x57.value))[0]); 
  MATH_OP(ADD, ((var_t*)(x54.value))[1], ((var_t*)(x56.value))[1], ((var_t*)(x57.value))[1]); 
} else {
  MATH_OP(ADD, x54, x56, x57);
}

var_t x58;
var_t x59;
if (isIterTag(self->fv_env[1].tag)) {
x58 = *(var_t*)(self->fv_env[1].value);
} else {
x58 = self->fv_env[1];
}

var_t x60;
var_t x61;
var_t x62;
if (isIterTag(self->fv_env[1].tag)) {
x61 = *(var_t*)(self->fv_env[1].value);
} else {
x61 = self->fv_env[1];
}

if (isIterTag(self->fv_env[0].tag)) {
x62 = *(var_t*)(self->fv_env[0].value);
} else {
x62 = self->fv_env[0];
}

x60.tag = EXPR_PAIR;
x60.value = malloc(sizeof(var_t)*2);
((var_t*)(x60.value))[0] = x61;
((var_t*)(x60.value))[1] = x62;

var_t x63;
UNWRAP(x63, x60);
closure_t x64;
x64.fv_env = malloc(sizeof(var_t)*1);
x64.fn = &lam_68;
x64.fv_env[0] = ((var_t*)x63.value)[0];


x59 = x64.fn(((var_t*)x63.value)[1], &x64);



x55.tag = EXPR_PAIR;
x55.value = malloc(sizeof(var_t)*2);
((var_t*)(x55.value))[0] = x58;
((var_t*)(x55.value))[1] = x59;

x53.tag = EXPR_PAIR;
x53.value = malloc(sizeof(var_t)*2);
((var_t*)(x53.value))[0] = x54;
((var_t*)(x53.value))[1] = x55;


x27.tag = EXPR_STEP;
x27.value = malloc(sizeof(var_t));
*(var_t*)(x27.value) = x53;

}

  return x27;
}

var_t lam_69(var_t arg, struct closure_t* self) {
  var_t x66;
closure_t* x67 = malloc(sizeof(closure_t));
(*x67).fv_env = malloc(sizeof(var_t)*1);
(*x67).fn = &lam_68;
(*x67).fv_env[0] = arg;



x66.tag = EXPR_CLOSURE;
x66.value = (void*)x67;

  return x66;
}

var_t lam_68(var_t arg, struct closure_t* self) {
  var_t x69;
// Add
var_t x70;
var_t x71;
// Mul
var_t x72;
var_t x73;
if (isIterTag(arg.tag)) {
x72 = *(var_t*)(arg.value);
} else {
x72 = arg;
}

if (isIterTag(arg.tag)) {
x73 = *(var_t*)(arg.value);
} else {
x73 = arg;
}

x70.tag = EXPR_COMPLEX;

if (x72.tag == EXPR_COMPLEX) {
  var_t x74;
  var_t x75;
  var_t x76;
  var_t x77;
  var_t x78;
  var_t x79;
  MATH_OP(MUL, x74, ((var_t*)(x72.value))[0], ((var_t*)(x73.value))[0]);
  MATH_OP(MUL, x75, ((var_t*)(x72.value))[0], ((var_t*)(x73.value))[1]);
  MATH_OP(MUL, x76, ((var_t*)(x72.value))[1], ((var_t*)(x73.value))[0]);
  MATH_OP(MUL, x77, ((var_t*)(x72.value))[1], ((var_t*)(x73.value))[1]);

  MATH_OP(SUB, x78, x74, x77);
  MATH_OP(ADD, x79, x75, x76);
  x70.tag = EXPR_COMPLEX;
  COMPLEX_ASSIGN_REAL(x70, x78);
  COMPLEX_ASSIGN_IMAG(x70, x79);
} else {
  MATH_OP(MUL, x70, x72, x73);
}

if (isIterTag(self->fv_env[0].tag)) {
x71 = *(var_t*)(self->fv_env[0].value);
} else {
x71 = self->fv_env[0];
}

assert(x70.tag == x71.tag);

if (x70.tag == EXPR_COMPLEX) {
  MATH_OP(ADD, ((var_t*)(x69.value))[0], ((var_t*)(x70.value))[0], ((var_t*)(x71.value))[0]); 
  MATH_OP(ADD, ((var_t*)(x69.value))[1], ((var_t*)(x70.value))[1], ((var_t*)(x71.value))[1]); 
} else {
  MATH_OP(ADD, x69, x70, x71);
}

  return x69;
}


var_t top_level() {
  var_t x0;
var_t x81;
closure_t x91;
var_t x92;

// ConstructRep (Non-Complex)
var_t x82;
var_t x83;
// oneDimNumCode
x82.value = malloc(sizeof(int));
x82.tag = EXPR_INT;
*(int*)(x82.value) = 0;

var_t x84;
var_t x85;
// Complex ConstructRep
var_t x86;
var_t x87;
var_t x88;
// oneDimNumCode
x87.value = malloc(sizeof(double));
x87.tag = EXPR_DOUBLE;
*(double*)(x87.value) = 1.0;

// oneDimNumCode
x88.value = malloc(sizeof(double));
x88.tag = EXPR_DOUBLE;
*(double*)(x88.value) = 0.0;

x86.tag = EXPR_PAIR;
x86.value = malloc(sizeof(var_t)*2);
((var_t*)(x86.value))[0] = x87;
((var_t*)(x86.value))[1] = x88;

x84.tag = EXPR_COMPLEX;
x84.value = malloc(sizeof(var_t));
*((var_t*)(x84.value)) = x86;

// Complex FromIntegral
var_t x89;
var_t x90;
x90.tag = EXPR_DOUBLE;
x90.value = malloc(sizeof(double));
*((double*)(x90.value)) = 0;
// oneDimNumCode
x89.value = malloc(sizeof(int));
x89.tag = EXPR_INT;
*(int*)(x89.value) = 0;

INIT_COMPLEX(x85, double, EXPR_DOUBLE);
COMPLEX_ASSIGN_REAL(x85, x89);
COMPLEX_ASSIGN_IMAG(x85, x90);

x83.tag = EXPR_PAIR;
x83.value = malloc(sizeof(var_t)*2);
((var_t*)(x83.value))[0] = x84;
((var_t*)(x83.value))[1] = x85;

x81.tag = EXPR_PAIR;
x81.value = malloc(sizeof(var_t)*2);
((var_t*)(x81.value))[0] = x82;
((var_t*)(x81.value))[1] = x83;


closure_t* x93 = malloc(sizeof(closure_t));
(*x93).fv_env = malloc(sizeof(var_t)*0);
(*x93).fn = &lam_62;



x92.tag = EXPR_CLOSURE;
x92.value = (void*)x93;

memcpy(&x91, (closure_t*)(x92.value), sizeof(closure_t));
x0 = x91.fn(x81, &x91);

  return x0;
}

