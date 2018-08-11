#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <editline/readline.h>
#include "mpc.h"
#include <errno.h>

#define ERRCHECK(args, cond, err, ...) \
  if (!(cond)) {return construct_lval_err(err, ##__VA_ARGS__);}

/* Forward Declaration of struct*/
struct lval; //Only declare
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

/*Enumeration for lval types*/
enum {
  //Struct is an error
  LVAL_ERR,
  //Struct is a number
  LVAL_NUM, 
  //Struct is symbol
  LVAL_SYM,
  //S-Expressions
  LVAL_SEXPR,
  //Q-Expressions
  LVAL_QEXPR,
  //Function
  LVAL_FUN
};

typedef lval* (*lbuiltin)(lenv*, lval*);
/*Lval struct*/
struct lval {
  int type;
  long num;
  /*Error and symbol types*/
  char* err;
  char* sym;
  /*Function*/
  lbuiltin builtin;
  lenv* env;
  lval* formals;
  lval* body;

  /*Count and pointer*/
  int count;
  lval** cell;
};

struct lenv {
  lenv* par;
  int count;
  char** syms;
  lval** vals;
};

/*Functions declaration*/
/*Constructor: lval number*/
lval* construct_lval_num(long num);
/*Constructor: lval error*/
lval* construct_lval_err(char* err, ...);
/*Constructor: lval symbol*/
lval* construct_lval_sym(char* sym);
/*Constructor: empty S-expr lval*/
lval* construct_lval_sexpr(void);
/*Constructor of Q-expr*/
lval* construct_lval_qexpr(void);
/*Constructor of Function*/
lval* construct_lval_fun(lbuiltin func);
/*Destructor of lval*/
void destruct_lval(lval* v);
/*Read function*/
lval* read_to_lval(mpc_ast_t* t);
/*Read number function */
lval* read_num_to_lval(mpc_ast_t* t);
/*Add cell x to lval v*/
void add_cell_to_lval(lval* v, lval* x);
/*This function alow printing lval s-expresion*/
void print_lval_expr(lval* l, char* open, char* close);
/*This function alow printing lval*/
void print_lval(lval* l);
/*Another function alow printing but with newline*/
void println_lval(lval* l);
/*Evaluation lval*/
lval* eval_lval(lenv* e, lval* v);
/*Evaluation lval s-expressions*/
lval* eval_lval_sexpr(lenv* e, lval* l);
/*Pop element from lval*/
lval* pop_lval(lval* l, int n);
/*Pop element and delete the lval*/
lval* take_lval(lval* l, int n);
/*Perform arthimetic operation*/
lval* builtin_arith(lval* l, char* op);
/*Perform head operator*/
lval* builtin_head(lenv* e, lval* v);
/*Perform tail operator*/
lval* builtin_tail(lenv* e, lval* v);
/*Perform list operator*/
lval* builtin_list(lenv* e, lval* v);
/*Perform evaluate Q-Expression*/
lval* builtin_eval(lenv* e, lval* v);
/*Join Q-Expression*/
lval* builtin_join(lenv* e, lval* v);
/*Lookup function for all builtin operator*/
//lval* builtin_op(lval* l, char* sym);
lval* copy_lval(lval* l);
lenv* construct_lenv(void);
void destruct_lenv(lenv* e);
lval* get_lval_from_lenv(lenv* e, lval* name);
void put_lval_to_lenv(lenv* e, lval* name, lval* content);
void add_fun_to_lenv(lenv* e, char* name, lbuiltin fun);
void add_builtin_to_lenv(lenv* e);
lval* builtin_arith_add(lenv* e, lval* v);
lval* builtin_arith_sub(lenv* e, lval* v);
lval* builtin_arith_div(lenv* e, lval* v);
lval* builtin_arith_mul(lenv* e, lval* v);
lval* builtin_def(lenv* e, lval* v);
char* ltype_name(int t);
lval* construct_lval_lambda(lval* formals, lval* body);
lenv* copy_lenv(lenv* e);
lval* builtin_lambda(lenv* e, lval* v);
void put_lval_to_glob(lenv* e, lval* name, lval* content);
lval* builtin_var(lenv* e, lval* v, char* sym);
lval* builtin_put(lenv* e, lval* v);
lval* call_lval(lenv* e, lval* func, lval* v);

int main(int argc, char** argv)
{
  // Create some parsers
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr = mpc_new("sexpr");
  mpc_parser_t* Qexpr = mpc_new("qexpr");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  //Define parsers
  mpca_lang(MPCA_LANG_DEFAULT,
    "                                                   \
    number   : /-?[0-9]+/ ;                             \
    symbol   : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;       \
    sexpr    : '(' <expr>* ')' ;                        \
    qexpr    : '{' <expr>* '}' ;                        \
    expr     : <number> | <symbol> | <sexpr> | <qexpr> ;\
    lispy    : /^/ <expr>* /$/ ;                        \
    ",
    Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

  //Main part of program
  printf("LISP\nAuthor: Nguyen Van Quan\n");
  printf("With the help of www.buildyourownlisp.com\n");
  printf("Press Ctrl + C to exit.\n\n");
  lenv* environment = construct_lenv();
  add_builtin_to_lenv(environment);
  while (1) {
    char* input = readline(">>>");
    //to use history function of the prompt
    add_history(input);
    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Lispy, &r)) {
      lval* lval_output = read_to_lval(r.output);
      lval* l = eval_lval(environment, lval_output); 
      println_lval(l);
      destruct_lval(l);
      destruct_lval(lval_output);
      mpc_ast_delete(r.output);
    } else {
      //Otherwise Print the error
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    free(input);
  }
  destruct_lenv(environment);

  //Underfine and Delete parsers
  mpc_cleanup(5, Number, Symbol, Sexpr, Qexpr ,Expr, Lispy);
}

lval* construct_lval_num(long num)
{
  lval* x = malloc(sizeof(lval));
  x->type = LVAL_NUM;
  x->num = num;
  return x;
}

lval* construct_lval_err(char* format_err, ...)
{
  lval* x = malloc(sizeof(lval));
  x->type = LVAL_ERR;
  va_list va;
  va_start(va, format_err);
  x->err = malloc(512);
  vsnprintf(x->err, 511, format_err, va);
  x->err = realloc(x->err, strlen(x->err) + 1);
  va_end(va);
  return x;
}

lval* construct_lval_sym(char* sym)
{
  lval* x = malloc(sizeof(lval));
  x->type = LVAL_SYM;
  x->sym = malloc(strlen(sym) + 1);
  strcpy(x->sym, sym);
  return x;
}

lval* construct_lval_sexpr(void)
{
  lval* x = malloc(sizeof(lval));
  x->type = LVAL_SEXPR;
  x->count = 0;
  x->cell = NULL;
  return x;
}

lval* construct_lval_qexpr(void)
{
  lval* l = malloc(sizeof(lval));
  l->type = LVAL_QEXPR;
  l->count = 0;
  l->cell = NULL;
  return l;
}

void destruct_lval(lval* v)
{
  int i = 0;
  switch (v->type) {
    case LVAL_NUM:
      break;
    case LVAL_ERR: 
      free(v->err);
      break;
    case LVAL_SYM: 
      free(v->sym);
      break;
    /*In case S-expr or Q-expr, delete all elements inside*/
    case LVAL_SEXPR:
    case LVAL_QEXPR:
      while (i < v->count) {
        destruct_lval(v->cell[i]);
        i++;
      }
      /*Also free the memmory allocated to contain the pointer*/
      free(v->cell);
      break;
    case LVAL_FUN:
      if (v->builtin == NULL) {
        destruct_lenv(v->env);
        destruct_lval(v->body);
        destruct_lval(v->formals);
      }
      break;   
    default:
      printf("Exception: Invalid lval type, cannot destruct. Program stop.");
      exit(0);
  }
  free(v);
}

lval* read_to_lval(mpc_ast_t* t)
{
  /*Number or symbol*/
  if (strstr(t->tag, "symbol")) return construct_lval_sym(t->contents);
  if (strstr(t->tag, "number")) return read_num_to_lval(t);
  /*Root (>) or S-expr*/
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) x = construct_lval_sexpr();
  else if (strstr(t->tag, "sexpr")) x = construct_lval_sexpr();
  else if (strstr(t->tag, "qexpr")) x = construct_lval_qexpr();
  /*Add cell to S-expr*/
  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) continue;
    if (strcmp(t->children[i]->contents, ")") == 0) continue;
    if (strcmp(t->children[i]->contents, "{") == 0) continue;
    if (strcmp(t->children[i]->contents, "}") == 0) continue;
    if (strcmp(t->children[i]->tag, "regex") == 0) continue;
    add_cell_to_lval(x, read_to_lval(t->children[i]));
  }
  return x;
}

lval* read_num_to_lval(mpc_ast_t* t)
{
  errno = 0;
  long x = strtol(t->contents, NULL, 10);
  if (errno != ERANGE) return construct_lval_num(x);
  else return construct_lval_err("Invalid number");
}

void add_cell_to_lval(lval* v, lval* x)
{
  v->count++;
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  v->cell[v->count - 1] = copy_lval(x);
}

void print_lval_expr(lval* l, char* open, char* close)
{
  printf("%s", open);
  for (int i = 0; i < l->count; i++) {
    //Print value contained within
    print_lval(l->cell[i]);
    //Print space
    if (i != l->count - 1) printf(" ");
  }
  printf("%s", close);
}

void print_lval(lval* l)
{
  switch (l->type) {
    case LVAL_ERR: 
    printf("Error: %s", l->err);
    break;
    case LVAL_SYM:
    printf("%s", l->sym);
    break;
    case LVAL_NUM:
    printf("%ld", l->num);
    break;
    case LVAL_SEXPR:
    print_lval_expr(l,"(",")");
    break;
    case LVAL_QEXPR:
    print_lval_expr(l,"{","}");
    break;
    case LVAL_FUN:
    if (l->builtin == NULL) {
      printf("(\\ ");
      print_lval(l->formals);
      putchar(' ');
      print_lval(l->body);
      putchar(')');
    } else
      printf("<builtin>");
    break;
    default: 
    printf("Exception: Invalid lval type. Cannot print. Program stop.");
    exit(0);
  }
}

void println_lval(lval* l)
{
  print_lval(l);
  printf("\n");
}

lval* pop_lval(lval* l, int n)
{
  lval* x;
  //Assign the popped element to x
  x = l->cell[n];
  //Move every other element up
  for (int i = n; i < l->count - 1; i++)
    l->cell[i] = l->cell[i + 1];
  //Adjust count and cell size
  l->count--;
  l->cell = realloc(l->cell, sizeof(lval*) * l->count);
  return x;
}

lval* take_lval(lval* l, int n)
{
  lval* x = pop_lval(l, n);
  destruct_lval(l);
  return x;
}

lval* builtin_arith(lval* l, char* op)
{
  /*Ensure all arguments are numbers*/
  for (int i = 0; i < l->count; i++)
    if (l->cell[i]->type != LVAL_NUM) {
      return construct_lval_err("Member [%d] is not number", i);
    }
  /*Pop the first element*/
  lval* x = pop_lval(l, 0);

  /*If no arguments and sub, perform unary negation*/
  if (strcmp("-", op) == 0 && l->count == 0)
    x->num = -x->num;

  /*Perfrom the operator*/
  while (l->count > 0) {
    lval* y = pop_lval(l, 0);

    if (strcmp(op, "+") == 0) x->num += y->num;
    else if (strcmp(op, "-") == 0) x->num -= y->num;
    else if (strcmp(op, "*") == 0) x->num *= y->num;
    else {
      if (y->num == 0) {
        destruct_lval(x);
        destruct_lval(y);
        return construct_lval_err("Division by zero");
      }
      else x->num /= y->num;
    }
    destruct_lval(y);
  }
  return x;
}

lval* eval_lval_sexpr(lenv* e, lval* l)
{
  /*Evaluate all children*/
  for (int i = 0; i < l->count; i++) {
    lval* x = eval_lval(e, l->cell[i]);
    destruct_lval(l->cell[i]);
    l->cell[i] = x;
  }

  /*Error checking*/
  for (int i = 0; i < l->count; i++) {
    if (l->cell[i]->type == LVAL_ERR)
      return pop_lval(l, i);
  }

  /*Empty Expression*/
  if (l->count == 0) return copy_lval(l);

  /*Single expression*/
  if (l->count == 1) return pop_lval(l, 0);

  /*Ensure first element is function*/
  lval* x = pop_lval(l, 0);
  if (x->type != LVAL_FUN) {
    int type = x->type;
    destruct_lval(x);
    return construct_lval_err("First element is not a function. Got %s", ltype_name(type));
  }

  lval* result = call_lval(e, x, l);
  destruct_lval(x);
  return result;
}

lval* eval_lval(lenv* e, lval* l)
{
  if (l->type == LVAL_SYM)
    return get_lval_from_lenv(e, l);
  if (l->type == LVAL_SEXPR)
    return eval_lval_sexpr(e, l);
  return copy_lval(l);
}

lval* builtin_head(lenv* e, lval* l)
{
  /*Check errors*/
  ERRCHECK(l, l->count == 1, 
    "Function 'head' passed too many arguments. Got %d, expected 1", l->count);
  ERRCHECK(l, l->cell[0]->type == LVAL_QEXPR, 
    "Function 'head' passed incorect type! Got %s, expected %s", ltype_name(l->cell[0]->type), ltype_name(LVAL_QEXPR));
  ERRCHECK(l, l->cell[0]->count > 0,
    "Function 'head' passed {}!");
  /*Otherwise take first argument*/
  lval* a;
  a = pop_lval(l, 0);
  for (int i = 1; i < a->count; i++)
    destruct_lval(a->cell[i]);
  a->count = 1;
  a->cell = realloc(a->cell, sizeof(lval*));
  return a;
}

lval* builtin_tail(lenv* e, lval* l)
{
  /*Check errors*/
  ERRCHECK(l, l->count == 1, 
    "Function 'tail' passed too many arguments. Got %d, expected 1", l->count);
  ERRCHECK(l, l->cell[0]->type == LVAL_QEXPR, 
    "Function 'tail' passed incorect type! Got %s, expected %s", ltype_name(l->cell[0]->type), ltype_name(LVAL_QEXPR));
  ERRCHECK(l, l->cell[0]->count > 0,
    "Function 'tail' passed {}!");
  /*Perform*/
  lval* x = pop_lval(l, 0);
  lval* y = pop_lval(x, 0);
  destruct_lval(y);
  return x;
}

lval* builtin_list(lenv* e, lval* l)
{
  lval* x = copy_lval(l);
  x->type = LVAL_QEXPR;
  return x;
}

lval* builtin_eval(lenv* e, lval* l)
{
  ERRCHECK(l, l->count == 1,
     "Function 'eval' passed too many arguments. Got %d, expected 1", l->count);
  ERRCHECK(l, l->cell[0]->type == LVAL_QEXPR,
     "Function 'eval' passed incorect type! Got %s, expected %s", ltype_name(l->cell[0]->type), ltype_name(LVAL_QEXPR));
  lval* x = pop_lval(l, 0);
  x->type = LVAL_SEXPR;
  lval* y = eval_lval(e, x);
  destruct_lval(x);
  return y;
}

lval* builtin_join(lenv* e, lval* l)
{
  for (int i = 0; i < l->count; i++)
    ERRCHECK(l->cell[i], l->cell[i]->type == LVAL_QEXPR,
      "Function 'join' passed incorect type in cell %d. Got %s, expected %s", i, ltype_name(l->cell[i]->type), ltype_name(LVAL_QEXPR));
  int total_space = 0;
  //Get the total number of elements in all q-expr
  for (int i = 0; i < l->count; i++) {
    total_space += l->cell[i]->count;
  }
  //Pop the first q-expr
  lval* x = pop_lval(l, 0);
  //Re allocate the cell to fit all elements
  x->cell = realloc(x->cell, sizeof(lval*) * total_space);
  //Start join
  for (int i = 0; i < l->count; i++) {
    int k = l->cell[i]->count;
    while (l->cell[i]->count > 0) {
      int j = l->cell[i]->count - 1;
      //Take the last element of l->cell[i] and put it into the correct position
      x->cell[x->count + j] = pop_lval(l->cell[i], j);
    } 
    x->count += k;
  }
  return x;
}

lval* construct_lval_fun(lbuiltin func) 
{
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = func;
  return v;
}

lval* copy_lval(lval* l)
{
  lval* x = malloc(sizeof(lval));
  x->type = l->type;
  switch(x->type) {
    case LVAL_ERR:
      x->err = malloc(strlen(l->err) + 1);
      strcpy(x->err, l->err);
      break;
    case LVAL_FUN:
      if (l->builtin == NULL) {
        x->builtin = NULL;
        x->body = copy_lval(l->body);
        x->env = copy_lenv(l->env);
        x->formals = copy_lval(l->formals);
      } else
        x->builtin = l->builtin;
      break;
    case LVAL_NUM:
      x->num = l->num;
      break;
    case LVAL_SYM:
      x->sym = malloc(strlen(l->sym) + 1);
      strcpy(x->sym, l->sym);
      break;
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      x->count = l->count;
      x->cell = malloc(sizeof(lval*) * x->count);
      for (int i = 0; i < x->count; i++) 
        x->cell[i] = copy_lval(l->cell[i]);
      break;
    default: 
      printf("Unknown type. Cannot copy.\n");
      exit(0);
  } 
  return x;
}

lenv* construct_lenv(void)
{
  lenv* e = malloc(sizeof(lenv));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}
  
void destruct_lenv(lenv* l)
{
  for (int i = 0; i < l->count; i++) {
    free(l->syms[i]);
    destruct_lval(l->vals[i]);
  }
  free(l->syms);
  free(l->vals);
  free(l);
}
lval* get_lval_from_lenv(lenv* e, lval* name)
{
  if (name->type != LVAL_SYM)
    return construct_lval_err("Error: function 'get_lval_from_lenv' passed incorrect type. Got %s, expected %s", 
        ltype_name(name->type), ltype_name(LVAL_SYM));
  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->syms[i], name->sym) == 0)
      return copy_lval(e->vals[i]);
  }
  if (e->par) 
    return get_lval_from_lenv(e->par, name);
  else
    return construct_lval_err("Symbol '%s' not found", name->sym);
}  
void put_lval_to_lenv(lenv* e, lval* name, lval* content)
{
  for (int i = 0; i < e->count; i++) 
    if (strcmp(name->sym, e->syms[i]) == 0) {
      destruct_lval(e->vals[i]);
      e->vals[i] = copy_lval(content);
      return;
    }
  e->count++;
  e->vals = realloc(e->vals, sizeof(lval*) * e->count);
  e->syms = realloc(e->syms, sizeof(char*) * e->count);
  e->vals[e->count - 1] = copy_lval(content);
  e->syms[e->count - 1] = malloc(strlen(name->sym) + 1);
  strcpy(e->syms[e->count - 1], name->sym);
}
void add_fun_to_lenv(lenv* e, char* sym, lbuiltin fun)
{
  lval* s = construct_lval_sym(sym);
  lval* f = construct_lval_fun(fun);
  put_lval_to_lenv(e, s, f);
  destruct_lval(s);
  destruct_lval(f);
}
void add_builtin_to_lenv(lenv* e)
{
  add_fun_to_lenv(e, "+", builtin_arith_add);
  add_fun_to_lenv(e, "-", builtin_arith_sub);
  add_fun_to_lenv(e, "*", builtin_arith_mul);
  add_fun_to_lenv(e, "/", builtin_arith_div);
  add_fun_to_lenv(e, "join", builtin_join);
  add_fun_to_lenv(e, "eval", builtin_eval); 
  add_fun_to_lenv(e, "head", builtin_head);
  add_fun_to_lenv(e, "list", builtin_list);
  add_fun_to_lenv(e, "tail", builtin_tail);
  add_fun_to_lenv(e, "def", builtin_def);
  add_fun_to_lenv(e, "\\", builtin_lambda);
  add_fun_to_lenv(e, "=", builtin_put);
}
lval* builtin_arith_add(lenv* e, lval* v)
{
  return builtin_arith(v, "+");
}
lval* builtin_arith_sub(lenv* e, lval* v)
{
  return builtin_arith(v, "-");
}
lval* builtin_arith_div(lenv* e, lval* v)
{
  return builtin_arith(v, "/");
}
lval* builtin_arith_mul(lenv* e, lval* v)
{
  return builtin_arith(v, "*");
}
lval* builtin_var(lenv* e, lval* v, char* sym)
{
  ERRCHECK(v, v->cell[0]->type == LVAL_QEXPR, "Function 'def' passed incorrect type, got %s, expected %s", ltype_name(v->cell[0]->type), ltype_name(LVAL_QEXPR));
  ERRCHECK(v, v->cell[0]->count == v->count - 1, "Function 'def' cannot define incorrect number of symbols. Got %d, expected %d", v->cell[0]->count, v->count - 1);
  for (int i = 0; i < v->cell[0]->count; i++)
    if (v->cell[0]->cell[i]->type != LVAL_SYM) return construct_lval_err("Function 'def' does not work with non-symbol"
        ", got %s, expected %s", ltype_name(v->cell[0]->cell[i]->type), ltype_name(LVAL_SYM));
  for (int i = 0; i < v->cell[0]->count; i++) {
    if (strcmp(sym, "=") == 0)
      put_lval_to_lenv(e, v->cell[0]->cell[i], v->cell[i + 1]);
    if (strcmp(sym, "def") == 0)
      put_lval_to_glob(e, v->cell[0]->cell[i], v->cell[i + 1]);
  }
  return construct_lval_sexpr();
}
char* ltype_name(int t)
{
  switch(t) {
    case LVAL_ERR:
      return "error";
      break;
    case LVAL_FUN:
      return "function";
      break;
    case LVAL_NUM:
      return "number";
      break;
    case LVAL_SYM:
      return "symbol";
      break;
    case LVAL_QEXPR:
      return "q-expression";
      break;
    case LVAL_SEXPR:
      return "s-expression";
      break;
    default:
      return "Unknown type";
  }
}
lval* construct_lval_lambda(lval* formals, lval* body)
{
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;

  v->builtin = NULL;
  v->env = construct_lenv();
  v->formals = copy_lval(formals);
  v->body = copy_lval(body);
  return v;
}
lenv* copy_lenv(lenv* e)
{
  lenv* x = construct_lenv();
  x->count = e->count;
  x->par = e->par;
  x->syms = malloc(sizeof(char*) * e->count);
  x->vals = malloc(sizeof(lval*) * e->count);
  for (int i = 0; i < x->count; i++) {
    x->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(x->syms[i], e->syms[i]);
    x->vals[i] = copy_lval(e->vals[i]);
  }
  return x;
}

lval* builtin_lambda(lenv* e, lval* v)
{
  if (v->count != 2)
    return construct_lval_err("Wrong number of arguments."
      " Got %d, expected %d.", v->count, 2);
  for (int i = 0; i < 2; i++)
    if (v->cell[i]->type != LVAL_QEXPR)
      return construct_lval_err("Wrong type of arguments [%d]."
        " Got %s, expected %s.", i, ltype_name(v->cell[i]->type), ltype_name(LVAL_QEXPR));
  for (int i = 0; i < v->cell[0]->count; i++)
    if (v->cell[0]->cell[i]->type != LVAL_SYM)
      return construct_lval_err("Cannot define non-symbol [%d],"
        " got %s", i, ltype_name(v->cell[0]->cell[i]->type));
  lval* formal = pop_lval(v, 0); 
  lval* body = pop_lval(v, 0);
  lval* result = construct_lval_lambda(formal, body);
  destruct_lval(formal);
  destruct_lval(body);
  return result;
}
void put_lval_to_glob(lenv* e, lval* name, lval* content)
{
  while (e->par) e = e->par;
  put_lval_to_lenv(e, name, content);
}
lval* builtin_put(lenv* e, lval* v)
{
  return builtin_var(e, v, "=");
}
lval* builtin_def(lenv* e, lval* v) {
  return builtin_var(e, v, "def");
}

lval* call_lval(lenv* e, lval* func, lval* v)
{
  if (func->type != LVAL_FUN)
    return construct_lval_err("Cannot call non-function.");
  if (v->type != LVAL_SEXPR)
    return construct_lval_err("Function cannot operate on non-S-expression");
  if (func->builtin)
    return func->builtin(e, v);
  lval* x = copy_lval(func);
  int given = x->formals->count;
  int total = v->count;
  while (v->count > 0) {
    if (x->formals->count <= 0) {
      destruct_lval(x);
      return construct_lval_err("Function passed too many arguments. Got %d, expected %d", total, given);
    }
    lval* content = pop_lval(v, 0);
    lval* name  = pop_lval(x->formals, 0);
    put_lval_to_lenv(x->env, name, content);
    destruct_lval(content);
    destruct_lval(name);
  } 
  x->env->par = e;
  if (given == total) {
    lval* temp = construct_lval_sexpr();
    add_cell_to_lval(temp, x->body);
    lval* result = builtin_eval(x->env, temp);
    destruct_lval(x);
    destruct_lval(temp);
    return result;
  } else
    return x;
}
