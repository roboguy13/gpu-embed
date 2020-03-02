#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef enum var_type_tag {
  EXPR_INT
, EXPR_FLOAT
, EXPR_DOUBLE
, EXPR_CHAR
, EXPR_LAMBDA
, EXPR_EITHER_LEFT
, EXPR_EITHER_RIGHT
, EXPR_PAIR
, EXPR_UNBOXED
, EXPR_UNIT
} var_type_tag;

typedef struct var_t {
  var_type_tag tag;
  void* value;
} var_t;

typedef struct closure_t {
  var_t* fv_env;
  var_t (*fn)(var_t, struct closure_t*);
} closure_t;

var_t vars[3];

var_t lam_2(var_t arg, struct closure_t* self) {
  var_t x1;
x1 = arg;
  return x1;
}

var_t lam_3(var_t arg, struct closure_t* self) {
  var_t x2;
x2 = arg;
  return x2;
}


var_t top_level() {
  var_t x0;
var_t x3;
x3 = vars[0];
assert(x3.tag == EXPR_EITHER_LEFT || x3.tag == EXPR_EITHER_RIGHT);
var_t x4 = *(var_t*)(x3.value);
if (x3.tag == EXPR_EITHER_LEFT) {
closure_t x5;
x5.fv_env = malloc(sizeof(var_t)*0);
x5.fn = &lam_2;


x0 = x5.fn(((var_t*)x4.value)[0], &x5);

} else if (x3.tag == EXPR_EITHER_RIGHT) {
closure_t x6;
x6.fv_env = malloc(sizeof(var_t)*0);
x6.fn = &lam_3;


x0 = x6.fn(((var_t*)x4.value)[0], &x6);

}


  return x0;
}

int main() {
  vars[0].tag = EXPR_EITHER_LEFT;
  vars[0].value = malloc(sizeof(var_t));

  ((var_t*)vars[0].value)->tag = EXPR_INT;
  ((var_t*)vars[0].value)->value = malloc(sizeof(var_t));

  ((var_t*)((var_t*)vars[0].value)->value)->tag = EXPR_UNBOXED;
  ((var_t*)((var_t*)vars[0].value)->value)->value = (void*)7;

  var_t r = top_level();

  printf("%d\n", (int)r.value);
}

