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
, EXPR_NIL
} var_type_tag;

typedef enum semantic_type_tag {
  NO_SEMANTIC_TAG
, EXPR_COMPLEX     // Complex numbers
} semantic_type_tag;

struct closure_t;

typedef struct var_t {
  var_type_tag tag;
  semantic_type_tag semantic_tag;  // For optional additional information about the "un-deconstructed" type (for instance, it could be the case that tag=EXPR_PAIR, but specific_tag=EXPR_COMPLEX)
  void* value;
} var_t;

typedef struct closure_t {
  var_t* fv_env;
  var_t (*fn)(var_t, struct closure_t*);
} closure_t;

var_t vars[87];

#define GET_MATH_OP_ADD +
#define GET_MATH_OP_MUL *
#define GET_MATH_OP_SUB -
#define GET_MATH_OP_DIV /

#define GET_COMPARE_OP_LTE <=
#define GET_COMPARE_OP_LT <
#define GET_COMPARE_OP_GTE >=
#define GET_COMPARE_OP_GT >
#define GET_COMPARE_OP_EQUAL ==

#define assert_msg(cond, msg) do { if (!(cond)) { printf msg; assert(0 && #cond); } } while(0)

#define MATH_OP(op, result, a, b)\
  do {\
    assert_msg((a).tag == (b).tag, ("(a,b).tag = (%i,%i)\n", (int)(a).tag, (int)(b).tag));\
    (result).semantic_tag = (a).semantic_tag;\
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
    (result).semantic_tag = EXPR_COMPLEX;\
    (result).tag = EXPR_PAIR;\
    (result).value = malloc(2*sizeof(var_t));\
    ((var_t*)(result).value)[0].value = malloc(sizeof(var_t));\
    ((var_t*)(result).value)[1].value = malloc(2*sizeof(var_t));\
  } while (0);

#define INIT_COMPLEX(a, type, eTag)\
  do {\
    (a).semantic_tag = EXPR_COMPLEX;\
    (a).tag = EXPR_PAIR;\
    (a).value = malloc(2*sizeof(var_t));\
    ((var_t*)((a).value))[0].tag = eTag;\
    ((var_t*)((a).value))[0].value = malloc(sizeof(var_t));\
    ((var_t*)((a).value))[1].tag = EXPR_PAIR;\
    ((var_t*)((a).value))[1].semantic_tag = NO_SEMANTIC_TAG;\
    ((var_t*)((a).value))[1].value = malloc(2*sizeof(var_t));\
    ((var_t*)((var_t*)((a).value))[1].value)[0].tag = eTag;\
    ((var_t*)((var_t*)((a).value))[1].value)[0].semantic_tag = NO_SEMANTIC_TAG;\
    ((var_t*)((var_t*)((a).value))[1].value)[0].value = malloc(sizeof(var_t));\
    ((var_t*)((var_t*)((a).value))[1].value)[1].tag = EXPR_NIL;\
    ((var_t*)((var_t*)((a).value))[1].value)[1].semantic_tag = NO_SEMANTIC_TAG;\
    ((var_t*)((var_t*)((a).value))[1].value)[1].value = NULL;\
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

// ((var_t*)((var_t*)x103.value)[1].value)[0]
#define PAIR_ASSIGN_SND(result, x)\
  do {\
    ((var_t*)((var_t*)(result).value)[1].value)[0] = (x);\
  } while(0);

#define COMPLEX_REAL(result, c)\
  do {\
    assert((p).semantic_tag == EXPR_COMPLEX);\
    PAIR_FST(result, c);\
  } while (0);

#define COMPLEX_IMAG(result, c)\
  do {\
    assert((c).semantic_tag == EXPR_COMPLEX);\
    PAIR_SND(result, c);\
  } while (0);

#define COMPLEX_ASSIGN_REAL(result, x)\
  do {\
    PAIR_ASSIGN_FST(result, x);\
  } while(0);

#define COMPLEX_ASSIGN_IMAG(result, x)\
  do {\
    PAIR_ASSIGN_SND(result, x);\
  } while(0);

bool isIterTag(var_type_tag tag) {
  return tag == EXPR_STEP || tag == EXPR_DONE;
}

var_t lam_79(var_t, struct closure_t*);
var_t lam_80(var_t, struct closure_t*);
var_t lam_83(var_t, struct closure_t*);
var_t lam_82(var_t, struct closure_t*);
var_t lam_81(var_t, struct closure_t*);
var_t lam_85(var_t, struct closure_t*);
var_t lam_84(var_t, struct closure_t*);
var_t lam_87(var_t, struct closure_t*);
var_t lam_86(var_t, struct closure_t*);


var_t lam_79(var_t arg, struct closure_t* self) {
  var_t x1;
var_t x2;
closure_t x3;
var_t x4;

  // Var with Name id 79 and Haskell type (Int,(Complex Double),(Complex Double))
if (isIterTag(arg.tag)) {
x2 = *(var_t*)(arg.value);
} else {
x2 = arg;
}

closure_t* x5 = malloc(sizeof(closure_t));
(*x5).fv_env = malloc(sizeof(var_t)*0);
(*x5).fn = &lam_80;



x4.tag = EXPR_CLOSURE;
x4.semantic_tag = NO_SEMANTIC_TAG;
x4.value = (void*)x5;

memcpy(&x3, (closure_t*)(x4.value), sizeof(closure_t));
x1 = x3.fn(x2, &x3);

  return x1;
}

var_t lam_80(var_t arg, struct closure_t* self) {
  var_t x7;
x7.tag = EXPR_STEP;
x7.semantic_tag = NO_SEMANTIC_TAG;
x7.value = malloc(sizeof(var_t));
*(var_t*)(x7.value) = arg;
while (x7.tag != EXPR_DONE) {
var_t x8;
  // Var with Name id 80 and Haskell type (Int,(Complex Double),(Complex Double))
if (isIterTag(x7.tag)) {
x8 = *(var_t*)(x7.value);
} else {
x8 = x7;
}

closure_t x9;
x9.fv_env = malloc(sizeof(var_t)*2);
x9.fn = &lam_81;
x9.fv_env[0] = ((var_t*)((var_t*)x8.value)[1].value)[0];  // For FV with id 82 with Haskell type Complex Double
x9.fv_env[1] = ((var_t*)x8.value)[0];  // For FV with id 83 with Haskell type Int


x7 = x9.fn(((var_t*)(((var_t*)((var_t*)x8.value)[1].value)[1]).value)[0], &x9);


}

var_t x10 = *(var_t*)(x7.value);
x7.tag = x10.tag;
x7.semantic_tag = x10.semantic_tag;
x7.value = x10.value;

  return x7;
}

var_t lam_83(var_t arg, struct closure_t* self) {
  var_t x11;
closure_t* x12 = malloc(sizeof(closure_t));
(*x12).fv_env = malloc(sizeof(var_t)*1);
(*x12).fn = &lam_82;
(*x12).fv_env[0] = arg;  // For FV with id 83 with Haskell type Int



x11.tag = EXPR_CLOSURE;
x11.semantic_tag = NO_SEMANTIC_TAG;
x11.value = (void*)x12;

  return x11;
}

var_t lam_82(var_t arg, struct closure_t* self) {
  var_t x14;
closure_t* x15 = malloc(sizeof(closure_t));
(*x15).fv_env = malloc(sizeof(var_t)*2);
(*x15).fn = &lam_81;
(*x15).fv_env[0] = arg;  // For FV with id 82 with Haskell type Complex Double
(*x15).fv_env[1] = self->fv_env[0];  // For FV with id 83 with Haskell type Int



x14.tag = EXPR_CLOSURE;
x14.semantic_tag = NO_SEMANTIC_TAG;
x14.value = (void*)x15;

  return x14;
}

var_t lam_81(var_t arg, struct closure_t* self) {
  var_t x17;
var_t x18;
var_t x19;
var_t x20;

var_t x21;
var_t x22;
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[1].tag)) {
x21 = *(var_t*)(self->fv_env[1].value);
} else {
x21 = self->fv_env[1];
}

// oneDimNumCode
x22.value = malloc(sizeof(int));
x22.tag = EXPR_INT;
x22.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x22.value) = 50;

assert(x21.tag == x22.tag);

x18.tag = EXPR_BOOL;
x18.semantic_tag = NO_SEMANTIC_TAG;
x18.value = malloc(sizeof(bool));
if (x18.tag == EXPR_COMPLEX) {
  COMPARE(EQUAL, x18, ((var_t*)(x21.value))[0], ((var_t*)(x22.value))[0]);
  COMPARE(EQUAL, x18, ((var_t*)(x21.value))[1], ((var_t*)(x22.value))[1]);
} else {
  COMPARE(EQUAL, x18, x21, x22);
}


if (*(bool*)(x18.value)) {
var_t x23;
// ConstructRep (Non-Complex)
var_t x24;
x24.tag = EXPR_UNIT;
x24.semantic_tag = NO_SEMANTIC_TAG;
x24.value = 0;

x23.tag = EXPR_EITHER_LEFT;
x23.semantic_tag = NO_SEMANTIC_TAG;
x23.value = malloc(sizeof(var_t));
*(var_t*)(x23.value) = x24;


x17.tag = EXPR_DONE;
x17.semantic_tag = NO_SEMANTIC_TAG;
x17.value = malloc(sizeof(var_t));
*(var_t*)(x17.value) = x23;

} else {
var_t x25;
  // Var with Name id 81 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
x25 = *(var_t*)(arg.value);
} else {
x25 = arg;
}

closure_t x26;
x26.fv_env = malloc(sizeof(var_t)*4);
x26.fn = &lam_84;
x26.fv_env[0] = arg;  // For FV with id 81 with Haskell type Complex Double
x26.fv_env[1] = self->fv_env[0];  // For FV with id 82 with Haskell type Complex Double
x26.fv_env[2] = self->fv_env[1];  // For FV with id 83 with Haskell type Int
x26.fv_env[3] = ((var_t*)x25.value)[0];  // For FV with id 85 with Haskell type Double


x17 = x26.fn(((var_t*)((var_t*)x25.value)[1].value)[0], &x26);


}

  return x17;
}

var_t lam_85(var_t arg, struct closure_t* self) {
  var_t x28;
closure_t* x29 = malloc(sizeof(closure_t));
(*x29).fv_env = malloc(sizeof(var_t)*4);
(*x29).fn = &lam_84;
(*x29).fv_env[0] = self->fv_env[0];  // For FV with id 81 with Haskell type Complex Double
(*x29).fv_env[1] = self->fv_env[1];  // For FV with id 82 with Haskell type Complex Double
(*x29).fv_env[2] = self->fv_env[2];  // For FV with id 83 with Haskell type Int
(*x29).fv_env[3] = arg;  // For FV with id 85 with Haskell type Double



x28.tag = EXPR_CLOSURE;
x28.semantic_tag = NO_SEMANTIC_TAG;
x28.value = (void*)x29;

  return x28;
}

var_t lam_84(var_t arg, struct closure_t* self) {
  var_t x31;
var_t x32;
var_t x33;
var_t x34;

var_t x35;
var_t x36;
// Add
var_t x37;
var_t x38;
var_t x39;
var_t x40;
var_t x41;
var_t x42;
// Mul
var_t x43;
var_t x44;
  // Var with Name id 85 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
x43 = *(var_t*)(self->fv_env[3].value);
} else {
x43 = self->fv_env[3];
}

  // Var with Name id 85 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
x44 = *(var_t*)(self->fv_env[3].value);
} else {
x44 = self->fv_env[3];
}


if (x43.semantic_tag == EXPR_COMPLEX) {
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
  INIT_COMPLEX_PAIR(x37);
  COMPLEX_ASSIGN_REAL(x37, x49);
  COMPLEX_ASSIGN_IMAG(x37, x50);
} else {
  MATH_OP(MUL, x37, x43, x44);
}

// Mul
var_t x51;
var_t x52;
  // Var with Name id 84 and Haskell type Double
if (isIterTag(arg.tag)) {
x51 = *(var_t*)(arg.value);
} else {
x51 = arg;
}

  // Var with Name id 84 and Haskell type Double
if (isIterTag(arg.tag)) {
x52 = *(var_t*)(arg.value);
} else {
x52 = arg;
}


if (x51.semantic_tag == EXPR_COMPLEX) {
  var_t x53;
  var_t x54;
  var_t x55;
  var_t x56;
  var_t x57;
  var_t x58;

  MATH_OP(MUL, x53, ((var_t*)(x51.value))[0], ((var_t*)(x52.value))[0]);
  MATH_OP(MUL, x54, ((var_t*)(x51.value))[0], ((var_t*)(x52.value))[1]);
  MATH_OP(MUL, x55, ((var_t*)(x51.value))[1], ((var_t*)(x52.value))[0]);
  MATH_OP(MUL, x56, ((var_t*)(x51.value))[1], ((var_t*)(x52.value))[1]);

  MATH_OP(SUB, x57, x53, x56);
  MATH_OP(ADD, x58, x54, x55);
  INIT_COMPLEX_PAIR(x38);
  COMPLEX_ASSIGN_REAL(x38, x57);
  COMPLEX_ASSIGN_IMAG(x38, x58);
} else {
  MATH_OP(MUL, x38, x51, x52);
}

assert(x37.tag == x38.tag);

if (x37.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x35);

  MATH_OP(ADD, x41, ((var_t*)(x37.value))[0], ((var_t*)(x38.value))[0]);
  MATH_OP(ADD, x42, ((var_t*)(x37.value))[1], ((var_t*)(x38.value))[1]);

  COMPLEX_ASSIGN_REAL(x35, x41);
  COMPLEX_ASSIGN_IMAG(x35, x42);
} else {
  MATH_OP(ADD, x35, x37, x38);
}

// oneDimNumCode
x36.value = malloc(sizeof(double));
x36.tag = EXPR_DOUBLE;
x36.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x36.value) = 4.0;

assert(x35.tag == x36.tag);
x32.tag = EXPR_BOOL;
x32.semantic_tag = NO_SEMANTIC_TAG;
x32.value = malloc(sizeof(bool));
COMPARE(GT, x32, x35, x36);


if (*(bool*)(x32.value)) {
var_t x59;
// ConstructRep (Non-Complex)
var_t x60;
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
x60 = *(var_t*)(self->fv_env[2].value);
} else {
x60 = self->fv_env[2];
}

x59.tag = EXPR_EITHER_RIGHT;
x59.semantic_tag = NO_SEMANTIC_TAG;
x59.value = malloc(sizeof(var_t));
*(var_t*)(x59.value) = x60;


x31.tag = EXPR_DONE;
x31.semantic_tag = NO_SEMANTIC_TAG;
x31.value = malloc(sizeof(var_t));
*(var_t*)(x31.value) = x59;

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
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
x64 = *(var_t*)(self->fv_env[2].value);
} else {
x64 = self->fv_env[2];
}

// oneDimNumCode
x65.value = malloc(sizeof(int));
x65.tag = EXPR_INT;
x65.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x65.value) = 1;

assert(x64.tag == x65.tag);

if (x64.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x62);

  MATH_OP(ADD, x68, ((var_t*)(x64.value))[0], ((var_t*)(x65.value))[0]);
  MATH_OP(ADD, x69, ((var_t*)(x64.value))[1], ((var_t*)(x65.value))[1]);

  COMPLEX_ASSIGN_REAL(x62, x68);
  COMPLEX_ASSIGN_IMAG(x62, x69);
} else {
  MATH_OP(ADD, x62, x64, x65);
}

var_t x70;
var_t x71;
  // Var with Name id 82 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
x70 = *(var_t*)(self->fv_env[1].value);
} else {
x70 = self->fv_env[1];
}

var_t x72;
var_t x73;
var_t x74;
var_t x75;
  // Var with Name id 82 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
x74 = *(var_t*)(self->fv_env[1].value);
} else {
x74 = self->fv_env[1];
}

var_t x76;
  // Var with Name id 81 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
x76 = *(var_t*)(self->fv_env[0].value);
} else {
x76 = self->fv_env[0];
}

x75.tag = EXPR_PAIR;
x75.semantic_tag = NO_SEMANTIC_TAG;
x75.value = malloc(sizeof(var_t)*2);
((var_t*)(x75.value))[0] = x76;
((var_t*)(x75.value))[1].tag = EXPR_NIL;
((var_t*)(x75.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x75.value))[1].value = NULL;

x73.tag = EXPR_PAIR;
x73.semantic_tag = NO_SEMANTIC_TAG;
x73.value = malloc(sizeof(var_t)*2);
((var_t*)(x73.value))[0] = x74;
((var_t*)(x73.value))[1] = x75;

closure_t x77;
x77.fv_env = malloc(sizeof(var_t)*1);
x77.fn = &lam_86;
x77.fv_env[0] = ((var_t*)x73.value)[0];  // For FV with id 87 with Haskell type Complex Double


x72 = x77.fn(((var_t*)((var_t*)x73.value)[1].value)[0], &x77);


x71.tag = EXPR_PAIR;
x71.semantic_tag = NO_SEMANTIC_TAG;
x71.value = malloc(sizeof(var_t)*2);
((var_t*)(x71.value))[0] = x72;
((var_t*)(x71.value))[1].tag = EXPR_NIL;
((var_t*)(x71.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x71.value))[1].value = NULL;

x63.tag = EXPR_PAIR;
x63.semantic_tag = NO_SEMANTIC_TAG;
x63.value = malloc(sizeof(var_t)*2);
((var_t*)(x63.value))[0] = x70;
((var_t*)(x63.value))[1] = x71;

x61.tag = EXPR_PAIR;
x61.semantic_tag = NO_SEMANTIC_TAG;
x61.value = malloc(sizeof(var_t)*2);
((var_t*)(x61.value))[0] = x62;
((var_t*)(x61.value))[1] = x63;


x31.tag = EXPR_STEP;
x31.semantic_tag = NO_SEMANTIC_TAG;
x31.value = malloc(sizeof(var_t));
*(var_t*)(x31.value) = x61;

}

  return x31;
}

var_t lam_87(var_t arg, struct closure_t* self) {
  var_t x79;
closure_t* x80 = malloc(sizeof(closure_t));
(*x80).fv_env = malloc(sizeof(var_t)*1);
(*x80).fn = &lam_86;
(*x80).fv_env[0] = arg;  // For FV with id 87 with Haskell type Complex Double



x79.tag = EXPR_CLOSURE;
x79.semantic_tag = NO_SEMANTIC_TAG;
x79.value = (void*)x80;

  return x79;
}

var_t lam_86(var_t arg, struct closure_t* self) {
  var_t x82;
// Add
var_t x83;
var_t x84;
var_t x85;
var_t x86;
var_t x87;
var_t x88;
// Mul
var_t x89;
var_t x90;
  // Var with Name id 86 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
x89 = *(var_t*)(arg.value);
} else {
x89 = arg;
}

  // Var with Name id 86 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
x90 = *(var_t*)(arg.value);
} else {
x90 = arg;
}


if (x89.semantic_tag == EXPR_COMPLEX) {
  var_t x91;
  var_t x92;
  var_t x93;
  var_t x94;
  var_t x95;
  var_t x96;

  MATH_OP(MUL, x91, ((var_t*)(x89.value))[0], ((var_t*)(x90.value))[0]);
  MATH_OP(MUL, x92, ((var_t*)(x89.value))[0], ((var_t*)(x90.value))[1]);
  MATH_OP(MUL, x93, ((var_t*)(x89.value))[1], ((var_t*)(x90.value))[0]);
  MATH_OP(MUL, x94, ((var_t*)(x89.value))[1], ((var_t*)(x90.value))[1]);

  MATH_OP(SUB, x95, x91, x94);
  MATH_OP(ADD, x96, x92, x93);
  INIT_COMPLEX_PAIR(x83);
  COMPLEX_ASSIGN_REAL(x83, x95);
  COMPLEX_ASSIGN_IMAG(x83, x96);
} else {
  MATH_OP(MUL, x83, x89, x90);
}

  // Var with Name id 87 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
x84 = *(var_t*)(self->fv_env[0].value);
} else {
x84 = self->fv_env[0];
}

assert(x83.tag == x84.tag);

if (x83.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x82);

  MATH_OP(ADD, x87, ((var_t*)(x83.value))[0], ((var_t*)(x84.value))[0]);
  MATH_OP(ADD, x88, ((var_t*)(x83.value))[1], ((var_t*)(x84.value))[1]);

  COMPLEX_ASSIGN_REAL(x82, x87);
  COMPLEX_ASSIGN_IMAG(x82, x88);
} else {
  MATH_OP(ADD, x82, x83, x84);
}

  return x82;
}


var_t top_level() {
  var_t x0;
var_t x98;
closure_t x111;
var_t x112;

// ConstructRep (Non-Complex)
var_t x99;
var_t x100;
// oneDimNumCode
x99.value = malloc(sizeof(int));
x99.tag = EXPR_INT;
x99.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x99.value) = 0;

var_t x101;
var_t x102;
// Complex ConstructRep
var_t x103;
var_t x104;
var_t x105;
// oneDimNumCode
x104.value = malloc(sizeof(double));
x104.tag = EXPR_DOUBLE;
x104.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x104.value) = 1.0;

var_t x106;
// oneDimNumCode
x106.value = malloc(sizeof(double));
x106.tag = EXPR_DOUBLE;
x106.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x106.value) = 0.0;

x105.tag = EXPR_PAIR;
x105.semantic_tag = NO_SEMANTIC_TAG;
x105.value = malloc(sizeof(var_t)*2);
((var_t*)(x105.value))[0] = x106;
((var_t*)(x105.value))[1].tag = EXPR_NIL;
((var_t*)(x105.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x105.value))[1].value = NULL;

x103.tag = EXPR_PAIR;
x103.semantic_tag = NO_SEMANTIC_TAG;
x103.value = malloc(sizeof(var_t)*2);
((var_t*)(x103.value))[0] = x104;
((var_t*)(x103.value))[1] = x105;

x101.value = malloc(2*sizeof(var_t));
x101.semantic_tag = EXPR_COMPLEX;
x101.tag = EXPR_PAIR;
COMPLEX_ASSIGN_REAL(x101, (((var_t*)x103.value))[0])
COMPLEX_ASSIGN_IMAG(x101, (((var_t*)x103.value))[1])
*((var_t*)(x101.value)) = x103;

var_t x107;
// Complex FromIntegral with ty = double
var_t x108;
var_t x110;
var_t x109;
x109.tag = EXPR_DOUBLE;
x109.semantic_tag = NO_SEMANTIC_TAG;
x109.value = malloc(sizeof(double));
*((double*)(x109.value)) = 0;
// oneDimNumCode
x108.value = malloc(sizeof(int));
x108.tag = EXPR_INT;
x108.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x108.value) = 0;

x110.tag = EXPR_DOUBLE;
x110.semantic_tag = NO_SEMANTIC_TAG;
x110.value = malloc(sizeof(double));
CAST_TO(x110, double, x108);
INIT_COMPLEX(x107, double, EXPR_DOUBLE);
COMPLEX_ASSIGN_REAL(x107, x110);
COMPLEX_ASSIGN_IMAG(x107, x109);

x102.tag = EXPR_PAIR;
x102.semantic_tag = NO_SEMANTIC_TAG;
x102.value = malloc(sizeof(var_t)*2);
((var_t*)(x102.value))[0] = x107;
((var_t*)(x102.value))[1].tag = EXPR_NIL;
((var_t*)(x102.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x102.value))[1].value = NULL;

x100.tag = EXPR_PAIR;
x100.semantic_tag = NO_SEMANTIC_TAG;
x100.value = malloc(sizeof(var_t)*2);
((var_t*)(x100.value))[0] = x101;
((var_t*)(x100.value))[1] = x102;

x98.tag = EXPR_PAIR;
x98.semantic_tag = NO_SEMANTIC_TAG;
x98.value = malloc(sizeof(var_t)*2);
((var_t*)(x98.value))[0] = x99;
((var_t*)(x98.value))[1] = x100;


closure_t* x113 = malloc(sizeof(closure_t));
(*x113).fv_env = malloc(sizeof(var_t)*0);
(*x113).fn = &lam_79;



x112.tag = EXPR_CLOSURE;
x112.semantic_tag = NO_SEMANTIC_TAG;
x112.value = (void*)x113;

memcpy(&x111, (closure_t*)(x112.value), sizeof(closure_t));
x0 = x111.fn(x98, &x111);

  return x0;
}

int main() {
  var_t r = top_level();
  printf("%d\n", *(int*)r.value);
}

