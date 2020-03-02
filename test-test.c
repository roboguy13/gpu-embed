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

var_t lam_1(var_t, struct closure_t*);
var_t lam_2(var_t, struct closure_t*);


var_t lam_1(var_t arg, struct closure_t* self) {
  var_t x1;
x1.tag = arg.tag;
x1.value = arg.value;
  return x1;
}

var_t lam_2(var_t arg, struct closure_t* self) {
  var_t x2;
x2 = self->fv_env[0];
  return x2;
}


var_t top_level() {
  var_t x0;
var_t x3;
x3.tag = vars[0].tag;
x3.value = vars[0].value;
assert(x3.tag == EXPR_EITHER_LEFT || x3.tag == EXPR_EITHER_RIGHT);
var_t x4; // = *(var_t*)(x3.value);
x4.tag = ((var_t*)x3.value)->tag;
x4.value = ((var_t*)x3.value)->value;
if (x3.tag == EXPR_EITHER_LEFT) {
closure_t x5;
x5.fv_env = malloc(sizeof(var_t)*0);
x5.fn = &lam_1;

printf("x4.tag = %d\n", x4.tag);
printf("x4.value = %p\n", x4.value);
printf("*(int*)x4.value = %d\n", *(int*)x4.value);

x0 = x5.fn(*(var_t*)(x4.value), &x5);

} else if (x3.tag == EXPR_EITHER_RIGHT) {
closure_t x6;
x6.fv_env = malloc(sizeof(var_t)*1);
x6.fn = &lam_2;
x6.fv_env[0] = vars[0];


x0 = x6.fn(*(var_t*)(x4.value), &x6);

}


  return x0;
}

int main() {
  var_t* x = malloc(sizeof(var_t));
  x->tag = EXPR_INT;
  x->value = malloc(sizeof(int));
  *(int*)(x->value) = 20;

  vars[0].tag = EXPR_EITHER_LEFT;
  vars[0].value = x;

  /* ((var_t*)vars[0].value)->tag = EXPR_INT; */
  /* ((var_t*)vars[0].value)->value = malloc(sizeof(int)); */
  /* *(int*)(((var_t*)vars[0].value)->value) = 20; */


  /* ((var_t*)((var_t*)vars[0].value)->value)->tag = EXPR_UNBOXED; */
  /* ((var_t*)((var_t*)vars[0].value)->value)->value = (void*)7; */

  var_t r = top_level();

  printf("tag   = %d\n", (int)r.tag);
  printf("value = %d\n", *(int*)r.value);
}

/*

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
*/

