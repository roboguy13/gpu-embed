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
  int env_size;
  var_t* fv_env;
  var_t (*fn)(var_t, struct closure_t*);
} closure_t;

void copyClosure(closure_t*, closure_t*);

void copyVar(var_t* dest, var_t* src) {
  dest->tag = src->tag;
  dest->semantic_tag = src->semantic_tag;
  if (src->tag == EXPR_PAIR) {
    dest->value = malloc(2*sizeof(var_t));
    copyVar(&((var_t*)dest->value)[0], &((var_t*)src->value)[0]);
    copyVar(&((var_t*)dest->value)[1], &((var_t*)src->value)[1]);
  } else {
    switch (src->tag) {
      case EXPR_INT:
       dest->value = malloc(sizeof(int));
       *(int*)(dest->value) = *(int*)(src->value);
       break;
      case EXPR_FLOAT:
       dest->value = malloc(sizeof(float));
       *(float*)(dest->value) = *(float*)(src->value);
       break;
      case EXPR_DOUBLE:
       dest->value = malloc(sizeof(double));
       *(double*)(dest->value) = *(double*)(src->value);
       break;
      case EXPR_CHAR:
       dest->value = malloc(sizeof(char));
       *(char*)(dest->value) = *(char*)(src->value);
       break;
      case EXPR_CLOSURE:
       dest->value = malloc(sizeof(closure_t));
       copyClosure((closure_t*)dest->value, (closure_t*)src->value);
       // *(closure_t*)(dest->value) = *(closure_t*)(src->value);
       break;
      case EXPR_EITHER_LEFT:
      case EXPR_EITHER_RIGHT:
      case EXPR_STEP:
      case EXPR_DONE:
      case EXPR_UNIT:
       dest->value = malloc(sizeof(var_t));
       copyVar((var_t*)(dest->value), (var_t*)(src->value));
       break;
      case EXPR_NIL:
       dest->value = NULL;
       break;
      default:
        assert(0 && "invalid tag");
    }
  }
}

void copyClosure(closure_t* dest, closure_t* src) {
  dest->env_size = src->env_size;
  dest->fn = src->fn;
  dest->fv_env = malloc(src->env_size * sizeof(var_t));
  for (int i = 0; i < src->env_size; ++i) {
    copyVar(&(dest->fv_env[i]), &(src->fv_env[i]));
  }
}

var_t car(var_t v) {
  return ((var_t*)v.value)[0];
}
var_t cdr(var_t v) {
  return ((var_t*)v.value)[1];
}

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
    ((var_t*)((result).value))[1].value = malloc(2*sizeof(var_t));\
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
    copyVar(&(result), &((((var_t*)(p).value))[0]));\
  } while(0);

#define PAIR_SND(result, p)\
  do {\
    assert((p).tag == EXPR_PAIR);\
    copyVar(&(result), &((((var_t*)(((var_t*)(p).value))[1].value))[0]));\
  } while(0);

#define PAIR_ASSIGN_FST(result, x)\
  do {\
    copyVar(&((((var_t*)(result).value))[0]), &(x));\
  } while(0);

#define PAIR_ASSIGN_SND(result, x)\
  do {\
    copyVar(&((((var_t*)(((var_t*)(result).value))[1].value))[0]), &(x));\
  } while(0);

#define GET_COMPLEX_REAL(c) ((var_t*)((c).value))[0]
#define GET_COMPLEX_IMAG(c) ((var_t*)((var_t*)((c).value))[1].value)[0]

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
copyVar(&(x2), ((var_t*)arg.value));
} else {
copyVar(&(x2), &(arg));
}

closure_t* x5 = malloc(sizeof(closure_t));
(*x5).fv_env = malloc(sizeof(var_t)*0);
(*x5).env_size = 0;
(*x5).fn = &lam_80;



x4.tag = EXPR_CLOSURE;
x4.semantic_tag = NO_SEMANTIC_TAG;
x4.value = (void*)x5;

copyClosure(&x3, (closure_t*)(x4.value));
var_t x6 = x3.fn(x2, &x3);
copyVar(&(x1), &(x6));


  return x1;
}

var_t lam_80(var_t arg, struct closure_t* self) {
  var_t x8;
x8.tag = EXPR_STEP;
x8.semantic_tag = NO_SEMANTIC_TAG;
x8.value = malloc(sizeof(var_t));
copyVar(((var_t*)x8.value), &(arg));
while (x8.tag != EXPR_DONE) {
var_t x9;
  // Var with Name id 80 and Haskell type (Int,(Complex Double),(Complex Double))
if (isIterTag(x8.tag)) {
copyVar(&(x9), ((var_t*)x8.value));
} else {
copyVar(&(x9), &(x8));
}

closure_t x10;
x10.fv_env = malloc(sizeof(var_t)*2);
x10.env_size = 2;
x10.fn = &lam_81;
copyVar(&((x10.fv_env)[0]), &(((var_t*)((var_t*)x9.value)[1].value)[0]/* item #1 */));  // For FV with id 82 with Haskell type Complex Double
copyVar(&((x10.fv_env)[1]), &(((var_t*)x9.value)[0]/* item #0 */));  // For FV with id 83 with Haskell type Int


var_t x11 = x10.fn(((var_t*)(((var_t*)((var_t*)x9.value)[1].value)[1]).value)[0]/* item #2 */, &x10);
copyVar(&(x8), &(x11));



}

var_t x12;
copyVar(&(x12), ((var_t*)x8.value));
x8.tag = x12.tag;
x8.semantic_tag = x12.semantic_tag;
copyVar(((var_t*)x8.value), ((var_t*)x12.value));

  return x8;
}

var_t lam_83(var_t arg, struct closure_t* self) {
  var_t x13;
closure_t* x14 = malloc(sizeof(closure_t));
(*x14).fv_env = malloc(sizeof(var_t)*1);
(*x14).env_size = 1;
(*x14).fn = &lam_82;
copyVar(&(((*x14).fv_env)[0]), &(arg));  // For FV with id 83 with Haskell type Int



x13.tag = EXPR_CLOSURE;
x13.semantic_tag = NO_SEMANTIC_TAG;
x13.value = (void*)x14;

  return x13;
}

var_t lam_82(var_t arg, struct closure_t* self) {
  var_t x16;
closure_t* x17 = malloc(sizeof(closure_t));
(*x17).fv_env = malloc(sizeof(var_t)*2);
(*x17).env_size = 2;
(*x17).fn = &lam_81;
copyVar(&(((*x17).fv_env)[0]), &(arg));  // For FV with id 82 with Haskell type Complex Double
copyVar(&(((*x17).fv_env)[1]), &(self->fv_env[0]));  // For FV with id 83 with Haskell type Int



x16.tag = EXPR_CLOSURE;
x16.semantic_tag = NO_SEMANTIC_TAG;
x16.value = (void*)x17;

  return x16;
}

var_t lam_81(var_t arg, struct closure_t* self) {
  var_t x19;
var_t x20;
var_t x21;
var_t x22;

var_t x23;
var_t x24;
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[1].tag)) {
copyVar(&(x23), ((var_t*)self->fv_env[1].value));
} else {
copyVar(&(x23), &(self->fv_env[1]));
}

// oneDimNumCode
x24.value = malloc(sizeof(int));
x24.tag = EXPR_INT;
x24.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x24.value) = 50;

assert(x23.tag == x24.tag);

x20.tag = EXPR_BOOL;
x20.semantic_tag = NO_SEMANTIC_TAG;
x20.value = malloc(sizeof(bool));
if (x20.tag == EXPR_COMPLEX) {
  COMPARE(EQUAL, x20, ((var_t*)(x23.value))[0], ((var_t*)(x24.value))[0]);
  COMPARE(EQUAL, x20, ((var_t*)(x23.value))[1], ((var_t*)(x24.value))[1]);
} else {
  COMPARE(EQUAL, x20, x23, x24);
}


if (*(bool*)(x20.value)) {
var_t x25;
// ConstructRep (Non-Complex)
var_t x26;
x26.tag = EXPR_UNIT;
x26.semantic_tag = NO_SEMANTIC_TAG;
x26.value = 0;

x25.tag = EXPR_EITHER_LEFT;
x25.semantic_tag = NO_SEMANTIC_TAG;
x25.value = malloc(sizeof(var_t));
*(var_t*)(x25.value) = x26;


x19.tag = EXPR_DONE;
x19.semantic_tag = NO_SEMANTIC_TAG;
x19.value = malloc(sizeof(var_t));
copyVar(((var_t*)x19.value), &(x25));

} else {
var_t x27;
  // Var with Name id 81 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
copyVar(&(x27), ((var_t*)arg.value));
} else {
copyVar(&(x27), &(arg));
}

closure_t x28;
x28.fv_env = malloc(sizeof(var_t)*4);
x28.env_size = 4;
x28.fn = &lam_84;
copyVar(&((x28.fv_env)[0]), &(arg));  // For FV with id 81 with Haskell type Complex Double
copyVar(&((x28.fv_env)[1]), &(self->fv_env[0]));  // For FV with id 82 with Haskell type Complex Double
copyVar(&((x28.fv_env)[2]), &(self->fv_env[1]));  // For FV with id 83 with Haskell type Int
copyVar(&((x28.fv_env)[3]), &(((var_t*)x27.value)[0]/* item #0 */));  // For FV with id 85 with Haskell type Double


var_t x29 = x28.fn(((var_t*)((var_t*)x27.value)[1].value)[0]/* item #1 */, &x28);
copyVar(&(x19), &(x29));



}

  return x19;
}

var_t lam_85(var_t arg, struct closure_t* self) {
  var_t x31;
closure_t* x32 = malloc(sizeof(closure_t));
(*x32).fv_env = malloc(sizeof(var_t)*4);
(*x32).env_size = 4;
(*x32).fn = &lam_84;
copyVar(&(((*x32).fv_env)[0]), &(self->fv_env[0]));  // For FV with id 81 with Haskell type Complex Double
copyVar(&(((*x32).fv_env)[1]), &(self->fv_env[1]));  // For FV with id 82 with Haskell type Complex Double
copyVar(&(((*x32).fv_env)[2]), &(self->fv_env[2]));  // For FV with id 83 with Haskell type Int
copyVar(&(((*x32).fv_env)[3]), &(arg));  // For FV with id 85 with Haskell type Double



x31.tag = EXPR_CLOSURE;
x31.semantic_tag = NO_SEMANTIC_TAG;
x31.value = (void*)x32;

  return x31;
}

var_t lam_84(var_t arg, struct closure_t* self) {
  var_t x34;
var_t x35;
var_t x36;
var_t x37;

var_t x38;
var_t x39;
// Add
var_t x40;
var_t x41;
var_t x42;
var_t x43;
var_t x44;
var_t x45;
// Mul
var_t x46;
var_t x47;
  // Var with Name id 85 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
copyVar(&(x46), ((var_t*)self->fv_env[3].value));
} else {
copyVar(&(x46), &(self->fv_env[3]));
}

  // Var with Name id 85 and Haskell type Double
if (isIterTag(self->fv_env[3].tag)) {
copyVar(&(x47), ((var_t*)self->fv_env[3].value));
} else {
copyVar(&(x47), &(self->fv_env[3]));
}


if (x46.semantic_tag == EXPR_COMPLEX) {
  var_t x48;
  var_t x49;
  var_t x50;
  var_t x51;
  var_t x52;
  var_t x53;

  MATH_OP(MUL, x48, GET_COMPLEX_REAL(x46), GET_COMPLEX_REAL(x47));
  MATH_OP(MUL, x49, GET_COMPLEX_REAL(x46), GET_COMPLEX_IMAG(x47));
  MATH_OP(MUL, x50, GET_COMPLEX_IMAG(x46), GET_COMPLEX_REAL(x47));
  MATH_OP(MUL, x51, GET_COMPLEX_IMAG(x46), GET_COMPLEX_IMAG(x47));

  MATH_OP(SUB, x52, x48, x51);
  MATH_OP(ADD, x53, x49, x50);
  INIT_COMPLEX_PAIR(x40);
  COMPLEX_ASSIGN_REAL(x40, x52);
  COMPLEX_ASSIGN_IMAG(x40, x53);
} else {
  MATH_OP(MUL, x40, x46, x47);
}

// Mul
var_t x54;
var_t x55;
  // Var with Name id 84 and Haskell type Double
if (isIterTag(arg.tag)) {
copyVar(&(x54), ((var_t*)arg.value));
} else {
copyVar(&(x54), &(arg));
}

  // Var with Name id 84 and Haskell type Double
if (isIterTag(arg.tag)) {
copyVar(&(x55), ((var_t*)arg.value));
} else {
copyVar(&(x55), &(arg));
}


if (x54.semantic_tag == EXPR_COMPLEX) {
  var_t x56;
  var_t x57;
  var_t x58;
  var_t x59;
  var_t x60;
  var_t x61;

  MATH_OP(MUL, x56, GET_COMPLEX_REAL(x54), GET_COMPLEX_REAL(x55));
  MATH_OP(MUL, x57, GET_COMPLEX_REAL(x54), GET_COMPLEX_IMAG(x55));
  MATH_OP(MUL, x58, GET_COMPLEX_IMAG(x54), GET_COMPLEX_REAL(x55));
  MATH_OP(MUL, x59, GET_COMPLEX_IMAG(x54), GET_COMPLEX_IMAG(x55));

  MATH_OP(SUB, x60, x56, x59);
  MATH_OP(ADD, x61, x57, x58);
  INIT_COMPLEX_PAIR(x41);
  COMPLEX_ASSIGN_REAL(x41, x60);
  COMPLEX_ASSIGN_IMAG(x41, x61);
} else {
  MATH_OP(MUL, x41, x54, x55);
}

assert(x40.tag == x41.tag);

if (x40.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x38);

  MATH_OP(SUB, x44, GET_COMPLEX_REAL(x40), GET_COMPLEX_REAL(x41));
  MATH_OP(SUB, x45, GET_COMPLEX_IMAG(x40), GET_COMPLEX_IMAG(x41));

  COMPLEX_ASSIGN_REAL(x38, x44);
  COMPLEX_ASSIGN_IMAG(x38, x45);
} else {
  MATH_OP(ADD, x38, x40, x41);
}

// oneDimNumCode
x39.value = malloc(sizeof(double));
x39.tag = EXPR_DOUBLE;
x39.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x39.value) = 4.0;

assert(x38.tag == x39.tag);
x35.tag = EXPR_BOOL;
x35.semantic_tag = NO_SEMANTIC_TAG;
x35.value = malloc(sizeof(bool));
COMPARE(GT, x35, x38, x39);


if (*(bool*)(x35.value)) {
var_t x62;
// ConstructRep (Non-Complex)
var_t x63;
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
copyVar(&(x63), ((var_t*)self->fv_env[2].value));
} else {
copyVar(&(x63), &(self->fv_env[2]));
}

x62.tag = EXPR_EITHER_RIGHT;
x62.semantic_tag = NO_SEMANTIC_TAG;
x62.value = malloc(sizeof(var_t));
*(var_t*)(x62.value) = x63;


x34.tag = EXPR_DONE;
x34.semantic_tag = NO_SEMANTIC_TAG;
x34.value = malloc(sizeof(var_t));
copyVar(((var_t*)x34.value), &(x62));

} else {
var_t x64;
// ConstructRep (Non-Complex)
var_t x65;
var_t x66;
// Add
var_t x67;
var_t x68;
var_t x69;
var_t x70;
var_t x71;
var_t x72;
  // Var with Name id 83 and Haskell type Int
if (isIterTag(self->fv_env[2].tag)) {
copyVar(&(x67), ((var_t*)self->fv_env[2].value));
} else {
copyVar(&(x67), &(self->fv_env[2]));
}

// oneDimNumCode
x68.value = malloc(sizeof(int));
x68.tag = EXPR_INT;
x68.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x68.value) = 1;

assert(x67.tag == x68.tag);

if (x67.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x65);

  MATH_OP(SUB, x71, GET_COMPLEX_REAL(x67), GET_COMPLEX_REAL(x68));
  MATH_OP(SUB, x72, GET_COMPLEX_IMAG(x67), GET_COMPLEX_IMAG(x68));

  COMPLEX_ASSIGN_REAL(x65, x71);
  COMPLEX_ASSIGN_IMAG(x65, x72);
} else {
  MATH_OP(ADD, x65, x67, x68);
}

var_t x73;
var_t x74;
  // Var with Name id 82 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
copyVar(&(x73), ((var_t*)self->fv_env[1].value));
} else {
copyVar(&(x73), &(self->fv_env[1]));
}

var_t x75;
var_t x76;
var_t x77;
var_t x78;
  // Var with Name id 82 and Haskell type Complex Double
if (isIterTag(self->fv_env[1].tag)) {
copyVar(&(x77), ((var_t*)self->fv_env[1].value));
} else {
copyVar(&(x77), &(self->fv_env[1]));
}

var_t x79;
  // Var with Name id 81 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
copyVar(&(x79), ((var_t*)self->fv_env[0].value));
} else {
copyVar(&(x79), &(self->fv_env[0]));
}

x78.tag = EXPR_PAIR;
x78.semantic_tag = NO_SEMANTIC_TAG;
x78.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x78.value))[0]), &(x79));
((var_t*)(x78.value))[1].tag = EXPR_NIL;
((var_t*)(x78.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x78.value))[1].value = NULL;

x76.tag = EXPR_PAIR;
x76.semantic_tag = NO_SEMANTIC_TAG;
x76.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x76.value))[0]), &(x77));
copyVar(&((((var_t*)x76.value))[1]), &(x78));

closure_t x80;
x80.fv_env = malloc(sizeof(var_t)*1);
x80.env_size = 1;
x80.fn = &lam_86;
copyVar(&((x80.fv_env)[0]), &(((var_t*)x76.value)[0]/* item #0 */));  // For FV with id 87 with Haskell type Complex Double


var_t x81 = x80.fn(((var_t*)((var_t*)x76.value)[1].value)[0]/* item #1 */, &x80);
copyVar(&(x75), &(x81));



x74.tag = EXPR_PAIR;
x74.semantic_tag = NO_SEMANTIC_TAG;
x74.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x74.value))[0]), &(x75));
((var_t*)(x74.value))[1].tag = EXPR_NIL;
((var_t*)(x74.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x74.value))[1].value = NULL;

x66.tag = EXPR_PAIR;
x66.semantic_tag = NO_SEMANTIC_TAG;
x66.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x66.value))[0]), &(x73));
copyVar(&((((var_t*)x66.value))[1]), &(x74));

x64.tag = EXPR_PAIR;
x64.semantic_tag = NO_SEMANTIC_TAG;
x64.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x64.value))[0]), &(x65));
copyVar(&((((var_t*)x64.value))[1]), &(x66));


x34.tag = EXPR_STEP;
x34.semantic_tag = NO_SEMANTIC_TAG;
x34.value = malloc(sizeof(var_t));
copyVar(((var_t*)x34.value), &(x64));

}

  return x34;
}

var_t lam_87(var_t arg, struct closure_t* self) {
  var_t x83;
closure_t* x84 = malloc(sizeof(closure_t));
(*x84).fv_env = malloc(sizeof(var_t)*1);
(*x84).env_size = 1;
(*x84).fn = &lam_86;
copyVar(&(((*x84).fv_env)[0]), &(arg));  // For FV with id 87 with Haskell type Complex Double



x83.tag = EXPR_CLOSURE;
x83.semantic_tag = NO_SEMANTIC_TAG;
x83.value = (void*)x84;

  return x83;
}

var_t lam_86(var_t arg, struct closure_t* self) {
  var_t x86;
// Add
var_t x87;
var_t x88;
var_t x89;
var_t x90;
var_t x91;
var_t x92;
// Mul
var_t x93;
var_t x94;
  // Var with Name id 86 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
copyVar(&(x93), ((var_t*)arg.value));
} else {
copyVar(&(x93), &(arg));
}

  // Var with Name id 86 and Haskell type Complex Double
if (isIterTag(arg.tag)) {
copyVar(&(x94), ((var_t*)arg.value));
} else {
copyVar(&(x94), &(arg));
}


if (x93.semantic_tag == EXPR_COMPLEX) {
  var_t x95;
  var_t x96;
  var_t x97;
  var_t x98;
  var_t x99;
  var_t x100;

  MATH_OP(MUL, x95, GET_COMPLEX_REAL(x93), GET_COMPLEX_REAL(x94));
  MATH_OP(MUL, x96, GET_COMPLEX_REAL(x93), GET_COMPLEX_IMAG(x94));
  MATH_OP(MUL, x97, GET_COMPLEX_IMAG(x93), GET_COMPLEX_REAL(x94));
  MATH_OP(MUL, x98, GET_COMPLEX_IMAG(x93), GET_COMPLEX_IMAG(x94));

  MATH_OP(SUB, x99, x95, x98);
  MATH_OP(ADD, x100, x96, x97);
  INIT_COMPLEX_PAIR(x87);
  COMPLEX_ASSIGN_REAL(x87, x99);
  COMPLEX_ASSIGN_IMAG(x87, x100);
} else {
  MATH_OP(MUL, x87, x93, x94);
}

  // Var with Name id 87 and Haskell type Complex Double
if (isIterTag(self->fv_env[0].tag)) {
copyVar(&(x88), ((var_t*)self->fv_env[0].value));
} else {
copyVar(&(x88), &(self->fv_env[0]));
}

assert(x87.tag == x88.tag);

if (x87.semantic_tag == EXPR_COMPLEX) {
  INIT_COMPLEX_PAIR(x86);

  MATH_OP(SUB, x91, GET_COMPLEX_REAL(x87), GET_COMPLEX_REAL(x88));
  MATH_OP(SUB, x92, GET_COMPLEX_IMAG(x87), GET_COMPLEX_IMAG(x88));

  COMPLEX_ASSIGN_REAL(x86, x91);
  COMPLEX_ASSIGN_IMAG(x86, x92);
} else {
  MATH_OP(ADD, x86, x87, x88);
}

  return x86;
}


var_t top_level() {
  var_t x0;
var_t x102;
closure_t x115;
var_t x116;

// ConstructRep (Non-Complex)
var_t x103;
var_t x104;
// oneDimNumCode
x103.value = malloc(sizeof(int));
x103.tag = EXPR_INT;
x103.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x103.value) = 0;

var_t x105;
var_t x106;
// Complex ConstructRep
var_t x107;
var_t x108;
var_t x109;
// oneDimNumCode
x108.value = malloc(sizeof(double));
x108.tag = EXPR_DOUBLE;
x108.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x108.value) = 1.0;

var_t x110;
// oneDimNumCode
x110.value = malloc(sizeof(double));
x110.tag = EXPR_DOUBLE;
x110.semantic_tag = NO_SEMANTIC_TAG;
*(double*)(x110.value) = 0.0;

x109.tag = EXPR_PAIR;
x109.semantic_tag = NO_SEMANTIC_TAG;
x109.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x109.value))[0]), &(x110));
((var_t*)(x109.value))[1].tag = EXPR_NIL;
((var_t*)(x109.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x109.value))[1].value = NULL;

x107.tag = EXPR_PAIR;
x107.semantic_tag = NO_SEMANTIC_TAG;
x107.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x107.value))[0]), &(x108));
copyVar(&((((var_t*)x107.value))[1]), &(x109));

INIT_COMPLEX(x105, double, EXPR_DOUBLE)
x105.semantic_tag = EXPR_COMPLEX;
x105.tag = EXPR_PAIR;
COMPLEX_ASSIGN_REAL(x105, GET_COMPLEX_REAL(x107))
COMPLEX_ASSIGN_IMAG(x105, GET_COMPLEX_IMAG(x107))

var_t x111;
// Complex FromIntegral with ty = double
var_t x112;
var_t x114;
var_t x113;
x113.tag = EXPR_DOUBLE;
x113.semantic_tag = NO_SEMANTIC_TAG;
x113.value = malloc(sizeof(double));
*((double*)(x113.value)) = 0;
// oneDimNumCode
x112.value = malloc(sizeof(int));
x112.tag = EXPR_INT;
x112.semantic_tag = NO_SEMANTIC_TAG;
*(int*)(x112.value) = 0;

x114.tag = EXPR_DOUBLE;
x114.semantic_tag = NO_SEMANTIC_TAG;
x114.value = malloc(sizeof(double));
CAST_TO(x114, double, x112);
INIT_COMPLEX(x111, double, EXPR_DOUBLE);
COMPLEX_ASSIGN_REAL(x111, x114);
COMPLEX_ASSIGN_IMAG(x111, x113);

x106.tag = EXPR_PAIR;
x106.semantic_tag = NO_SEMANTIC_TAG;
x106.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x106.value))[0]), &(x111));
((var_t*)(x106.value))[1].tag = EXPR_NIL;
((var_t*)(x106.value))[1].semantic_tag = NO_SEMANTIC_TAG;
((var_t*)(x106.value))[1].value = NULL;

x104.tag = EXPR_PAIR;
x104.semantic_tag = NO_SEMANTIC_TAG;
x104.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x104.value))[0]), &(x105));
copyVar(&((((var_t*)x104.value))[1]), &(x106));

x102.tag = EXPR_PAIR;
x102.semantic_tag = NO_SEMANTIC_TAG;
x102.value = malloc(sizeof(var_t)*2);
copyVar(&((((var_t*)x102.value))[0]), &(x103));
copyVar(&((((var_t*)x102.value))[1]), &(x104));


closure_t* x117 = malloc(sizeof(closure_t));
(*x117).fv_env = malloc(sizeof(var_t)*0);
(*x117).env_size = 0;
(*x117).fn = &lam_79;



x116.tag = EXPR_CLOSURE;
x116.semantic_tag = NO_SEMANTIC_TAG;
x116.value = (void*)x117;

copyClosure(&x115, (closure_t*)(x116.value));
var_t x118 = x115.fn(x102, &x115);
copyVar(&(x0), &(x118));


  return x0;
}

int main() {
  var_t r = top_level();
  printf("%d\n", *(int*)r.value);
}

