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
        *((bool*)(result).value) = *(int*)((a).value) GET_COMPARE_OP_##op *(int*)((b).value);\
        break;\
      case EXPR_FLOAT:\
        *((bool*)(result).value) = *(float*)((a).value) GET_COMPARE_OP_##op *(float*)((b).value);\
        break;\
      case EXPR_DOUBLE:\
        *((bool*)(result).value) = *(double*)((a).value) GET_COMPARE_OP_##op *(double*)((b).value);\
        break;\
      case EXPR_BOOL:\
        *((bool*)(result).value) = *(bool*)((a).value) GET_COMPARE_OP_##op *(bool*)((b).value);\
        break;\
      case EXPR_CHAR:\
        *((bool*)(result).value) = *(char*)((a).value) GET_COMPARE_OP_##op *(char*)((b).value);\
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

#define INIT_COMPLEX_PAIR(result)\
  do {\
    (result).tag = EXPR_COMPLEX;\
    (result).value = malloc(sizeof(var_t));\
    (*((var_t*)(result).value)).tag = EXPR_PAIR;\
    (*((var_t*)(result).value)).value = malloc(2*sizeof(var_t));\
  } while (0);

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
  // Var with Name id 62 and Haskell type (Int,(Complex Double),(Complex Double))
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
x4.fv_env[0] = ((var_t*)x3.value)[1];  // For FV with id 64 with Haskell type Complex Double
x4.fv_env[1] = ((var_t*)x3.value)[0];  // For FV with id 65 with Haskell type Int


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
(*x7).fv_env[0] = arg;  // For FV with id 65 with Haskell type Int



x6.tag = EXPR_CLOSURE;
x6.value = (void*)x7;

  return x6;
}

var_t lam_64(var_t arg, struct closure_t* self) {
  var_t x9;
closure_t* x10 = malloc(sizeof(closure_t));
(*x10).fv_env = malloc(sizeof(var_t)*2);
(*x10).fn = &lam_63;
(*x10).fv_env[0] = arg;  // For FV with id 64 with Haskell type Complex Double
(*x10).fv_env[1] = self->fv_env[0];  // For FV with id 65 with Haskell type Int



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
  // Var with Name id 65 and Haskell type Int
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
  // Var with Name id 63 and Haskell type Complex Double
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
x22.fv_env[0] = arg;  // For FV with id 63 with Haskell type Complex Double
x22.fv_env[1] = self->fv_env[0];  // For FV with id 64 with Haskell type Complex Double
x22.fv_env[2] = self->fv_env[1];  // For FV with id 65 with Haskell type Int
x22.fv_env[3] = ((var_t*)x21.value)[0];  // For FV with id 67 with Haskell type Double


x12 = x22.fn(((var_t*)x21.value)[1], &x22);



}

  return x12;
}

var_t lam_67(var_t arg, struct closure_t* self) {
  var_t x24;
closure_t* x25 = malloc(sizeof(closure_t));
(*x25).fv_env = malloc(sizeof(var_t)*4);
(*x25).fn = &lam_66;
(*x25).fv_env[0] = self->fv_env[0];  // For FV with id 63 with Haskell type Complex Double
(*x25).fv_env[1] = self->fv_env[1];  // For FV with id 64 with Haskell type Complex Double
(*x25).fv_env[2] = self->fv_env[2];  // For FV with id 65 with Haskell type Int
(*x25).fv_env[3] = arg;  // For FV with id 67 with Haskell type Double



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
var_t x35;
var_t x36;
var_t x37;
var_t x38;
// Mul
var_t x39;
var_t x40;
var_t x41;
var_t x42;
  // Var with Name id 67 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
x39 = *(var_t*)(self->fv_env[3].value);
} else {
x39 = self->fv_env[3];
}

  // Var with Name id 67 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
x40 = *(var_t*)(self->fv_env[3].value);
} else {
x40 = self->fv_env[3];
}


if (x39.tag == EXPR_COMPLEX) {
  var_t x43;
  var_t x44;
  var_t x45;
  var_t x46;
  var_t x47;
  var_t x48;

UNWRAP(x41, x39);
UNWRAP(x42, x40);

  MATH_OP(MUL, x43, ((var_t*)(x41.value))[0], ((var_t*)(x42.value))[0]);
  MATH_OP(MUL, x44, ((var_t*)(x41.value))[0], ((var_t*)(x42.value))[1]);
  MATH_OP(MUL, x45, ((var_t*)(x41.value))[1], ((var_t*)(x42.value))[0]);
  MATH_OP(MUL, x46, ((var_t*)(x41.value))[1], ((var_t*)(x42.value))[1]);

  MATH_OP(SUB, x47, x43, x46);
  MATH_OP(ADD, x48, x44, x45);
  INIT_COMPLEX_PAIR(x33);
  COMPLEX_ASSIGN_REAL(x33, x47);
  COMPLEX_ASSIGN_IMAG(x33, x48);
} else {
  MATH_OP(MUL, x33, x39, x40);
}

// Mul
var_t x49;
var_t x50;
var_t x51;
var_t x52;
  // Var with Name id 66 and Haskell type Double
if (isIterTag(arg.tag)) {
x49 = *(var_t*)(arg.value);
} else {
x49 = arg;
}

  // Var with Name id 66 and Haskell type Double
if (isIterTag(arg.tag)) {
x50 = *(var_t*)(arg.value);
} else {
x50 = arg;
}


if (x49.tag == EXPR_COMPLEX) {
  var_t x53;
  var_t x54;
  var_t x55;
  var_t x56;
  var_t x57;
  var_t x58;

UNWRAP(x51, x49);
UNWRAP(x52, x50);

  MATH_OP(MUL, x53, ((var_t*)(x51.value))[0], ((var_t*)(x52.value))[0]);
  MATH_OP(MUL, x54, ((var_t*)(x51.value))[0], ((var_t*)(x52.value))[1]);
  MATH_OP(MUL, x55, ((var_t*)(x51.value))[1], ((var_t*)(x52.value))[0]);
  MATH_OP(MUL, x56, ((var_t*)(x51.value))[1], ((var_t*)(x52.value))[1]);

  MATH_OP(SUB, x57, x53, x56);
  MATH_OP(ADD, x58, x54, x55);
  INIT_COMPLEX_PAIR(x34);
  COMPLEX_ASSIGN_REAL(x34, x57);
  COMPLEX_ASSIGN_IMAG(x34, x58);
} else {
  MATH_OP(MUL, x34, x49, x50);
}

assert(x33.tag == x34.tag);

if (x33.tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x31);
  UNWRAP(x35, x33);
  UNWRAP(x36, x34);

  MATH_OP(ADD, x37, ((var_t*)(x33.value))[0], ((var_t*)(x34.value))[0]); 
  MATH_OP(ADD, x38, ((var_t*)(x33.value))[1], ((var_t*)(x34.value))[1]); 

  COMPLEX_ASSIGN_REAL(x31, x37);
  COMPLEX_ASSIGN_IMAG(x31, x38);
} else {
  MATH_OP(ADD, x31, x33, x34);
}

// oneDimNumCode
x32.value = malloc(sizeof(double));
x32.tag = EXPR_DOUBLE;
*(double*)(x32.value) = 4.0;

assert(x31.tag == x32.tag);
x28.tag = EXPR_BOOL;
x28.value = malloc(sizeof(bool));
COMPARE(GT, x28, x31, x32);


if (*(bool*)(x28.value)) {
var_t x59;
// ConstructRep (Non-Complex)
var_t x60;
  // Var with Name id 65 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
x60 = *(var_t*)(self->fv_env[2].value);
} else {
x60 = self->fv_env[2];
}

x59.tag = EXPR_EITHER_RIGHT;
x59.value = malloc(sizeof(var_t));
*(var_t*)(x59.value) = x60;


x27.tag = EXPR_DONE;
x27.value = malloc(sizeof(var_t));
*(var_t*)(x27.value) = x59;

} else {
var_t x61;
// ConstructRep (Non-Complex)
var_t x62;
var_t x63;
// Add
var_t x64;
var_t x65;
var_t x66;
var_t x67;
var_t x68;
var_t x69;
  // Var with Name id 65 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
x64 = *(var_t*)(self->fv_env[2].value);
} else {
x64 = self->fv_env[2];
}

// oneDimNumCode
x65.value = malloc(sizeof(int));
x65.tag = EXPR_INT;
*(int*)(x65.value) = 1;

assert(x64.tag == x65.tag);

if (x64.tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x62);
  UNWRAP(x66, x64);
  UNWRAP(x67, x65);

  MATH_OP(ADD, x68, ((var_t*)(x64.value))[0], ((var_t*)(x65.value))[0]); 
  MATH_OP(ADD, x69, ((var_t*)(x64.value))[1], ((var_t*)(x65.value))[1]); 

  COMPLEX_ASSIGN_REAL(x62, x68);
  COMPLEX_ASSIGN_IMAG(x62, x69);
} else {
  MATH_OP(ADD, x62, x64, x65);
}

var_t x70;
var_t x71;
  // Var with Name id 64 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
x70 = *(var_t*)(self->fv_env[1].value);
} else {
x70 = self->fv_env[1];
}

var_t x72;
var_t x73;
var_t x74;
  // Var with Name id 64 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
x73 = *(var_t*)(self->fv_env[1].value);
} else {
x73 = self->fv_env[1];
}

  // Var with Name id 63 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
x74 = *(var_t*)(self->fv_env[0].value);
} else {
x74 = self->fv_env[0];
}

x72.tag = EXPR_PAIR;
x72.value = malloc(sizeof(var_t)*2);
((var_t*)(x72.value))[0] = x73;
((var_t*)(x72.value))[1] = x74;

var_t x75;
UNWRAP(x75, x72);
closure_t x76;
x76.fv_env = malloc(sizeof(var_t)*1);
x76.fn = &lam_68;
x76.fv_env[0] = ((var_t*)x75.value)[0];  // For FV with id 69 with Haskell type Complex Double


x71 = x76.fn(((var_t*)x75.value)[1], &x76);



x63.tag = EXPR_PAIR;
x63.value = malloc(sizeof(var_t)*2);
((var_t*)(x63.value))[0] = x70;
((var_t*)(x63.value))[1] = x71;

x61.tag = EXPR_PAIR;
x61.value = malloc(sizeof(var_t)*2);
((var_t*)(x61.value))[0] = x62;
((var_t*)(x61.value))[1] = x63;


x27.tag = EXPR_STEP;
x27.value = malloc(sizeof(var_t));
*(var_t*)(x27.value) = x61;

}

  return x27;
}

var_t lam_69(var_t arg, struct closure_t* self) {
  var_t x78;
closure_t* x79 = malloc(sizeof(closure_t));
(*x79).fv_env = malloc(sizeof(var_t)*1);
(*x79).fn = &lam_68;
(*x79).fv_env[0] = arg;  // For FV with id 69 with Haskell type Complex Double



x78.tag = EXPR_CLOSURE;
x78.value = (void*)x79;

  return x78;
}

var_t lam_68(var_t arg, struct closure_t* self) {
  var_t x81;
// Add
var_t x82;
var_t x83;
var_t x84;
var_t x85;
var_t x86;
var_t x87;
// Mul
var_t x88;
var_t x89;
var_t x90;
var_t x91;
  // Var with Name id 68 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
x88 = *(var_t*)(arg.value);
} else {
x88 = arg;
}

  // Var with Name id 68 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
x89 = *(var_t*)(arg.value);
} else {
x89 = arg;
}


if (x88.tag == EXPR_COMPLEX) {
  var_t x92;
  var_t x93;
  var_t x94;
  var_t x95;
  var_t x96;
  var_t x97;

UNWRAP(x90, x88);
UNWRAP(x91, x89);

  MATH_OP(MUL, x92, ((var_t*)(x90.value))[0], ((var_t*)(x91.value))[0]);
  MATH_OP(MUL, x93, ((var_t*)(x90.value))[0], ((var_t*)(x91.value))[1]);
  MATH_OP(MUL, x94, ((var_t*)(x90.value))[1], ((var_t*)(x91.value))[0]);
  MATH_OP(MUL, x95, ((var_t*)(x90.value))[1], ((var_t*)(x91.value))[1]);

  MATH_OP(SUB, x96, x92, x95);
  MATH_OP(ADD, x97, x93, x94);
  INIT_COMPLEX_PAIR(x82);
  COMPLEX_ASSIGN_REAL(x82, x96);
  COMPLEX_ASSIGN_IMAG(x82, x97);
} else {
  MATH_OP(MUL, x82, x88, x89);
}

  // Var with Name id 69 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
x83 = *(var_t*)(self->fv_env[0].value);
} else {
x83 = self->fv_env[0];
}

assert(x82.tag == x83.tag);

if (x82.tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x81);
  UNWRAP(x84, x82);
  UNWRAP(x85, x83);

  MATH_OP(ADD, x86, ((var_t*)(x82.value))[0], ((var_t*)(x83.value))[0]); 
  MATH_OP(ADD, x87, ((var_t*)(x82.value))[1], ((var_t*)(x83.value))[1]); 

  COMPLEX_ASSIGN_REAL(x81, x86);
  COMPLEX_ASSIGN_IMAG(x81, x87);
} else {
  MATH_OP(ADD, x81, x82, x83);
}

  return x81;
}


var_t top_level() {
  var_t x0;
var_t x99;
closure_t x110;
var_t x111;

// ConstructRep (Non-Complex)
var_t x100;
var_t x101;
// oneDimNumCode
x100.value = malloc(sizeof(int));
x100.tag = EXPR_INT;
*(int*)(x100.value) = 0;

var_t x102;
var_t x103;
// Complex ConstructRep
var_t x104;
var_t x105;
var_t x106;
// oneDimNumCode
x105.value = malloc(sizeof(double));
x105.tag = EXPR_DOUBLE;
*(double*)(x105.value) = 1.0;

// oneDimNumCode
x106.value = malloc(sizeof(double));
x106.tag = EXPR_DOUBLE;
*(double*)(x106.value) = 0.0;

x104.tag = EXPR_PAIR;
x104.value = malloc(sizeof(var_t)*2);
((var_t*)(x104.value))[0] = x105;
((var_t*)(x104.value))[1] = x106;

x102.tag = EXPR_COMPLEX;
x102.value = malloc(sizeof(var_t));
*((var_t*)(x102.value)) = x104;

// Complex FromIntegral with ty = double
var_t x107;
var_t x109;
var_t x108;
x108.tag = EXPR_DOUBLE;
x108.value = malloc(sizeof(double));
*((double*)(x108.value)) = 0;
// oneDimNumCode
x107.value = malloc(sizeof(int));
x107.tag = EXPR_INT;
*(int*)(x107.value) = 0;

x109.tag = EXPR_DOUBLE;
x109.value = malloc(sizeof(double));
*(double*)(x109.value) = *(double*)(x107.value);
INIT_COMPLEX(x103, double, EXPR_DOUBLE);
COMPLEX_ASSIGN_REAL(x103, x109);
COMPLEX_ASSIGN_IMAG(x103, x108);

x101.tag = EXPR_PAIR;
x101.value = malloc(sizeof(var_t)*2);
((var_t*)(x101.value))[0] = x102;
((var_t*)(x101.value))[1] = x103;

x99.tag = EXPR_PAIR;
x99.value = malloc(sizeof(var_t)*2);
((var_t*)(x99.value))[0] = x100;
((var_t*)(x99.value))[1] = x101;


closure_t* x112 = malloc(sizeof(closure_t));
(*x112).fv_env = malloc(sizeof(var_t)*0);
(*x112).fn = &lam_62;



x111.tag = EXPR_CLOSURE;
x111.value = (void*)x112;

memcpy(&x110, (closure_t*)(x111.value), sizeof(closure_t));
x0 = x110.fn(x99, &x110);

  return x0;
}

int main() {
  var_t r = top_level();
  printf("%d\n", *(int*)r.value);
}

