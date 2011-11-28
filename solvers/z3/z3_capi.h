/*******************************************************************\

Module:

Author:

\*******************************************************************/

#ifndef CPROVER_PROP_Z3_CAPI_H
#define CPROVER_PROP_Z3_CAPI_H

#include <config.h>

#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include <z3.h>

class z3_capi {

  public:

    z3_capi(){};
    ~z3_capi(){}; // destructor
    void set_ctx(Z3_context ctx)
    {
      z3_ctx = ctx;
      // Common sorts and constants that we re-use to save on memory
      z3_int_sort = Z3_mk_int_type(z3_ctx);
      z3_real_sort = Z3_mk_real_type(z3_ctx);
      z3_bool_sort = Z3_mk_bool_type(z3_ctx);
      z3_true = Z3_mk_true(z3_ctx);
      z3_false = Z3_mk_false(z3_ctx);
      z3_intwidth_bv_sort = Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width);
      z3_bvsort_8 = Z3_mk_bv_type(z3_ctx, 8);
      z3_bvsort_16 = Z3_mk_bv_type(z3_ctx, 16);
      z3_bvsort_32 = Z3_mk_bv_type(z3_ctx, 32);
      z3_bvsort_64 = Z3_mk_bv_type(z3_ctx, 64);
      memset(z3_bvsort_array, 0, sizeof(z3_bvsort_array));
      z3_bvsort_array[8] = z3_bvsort_8;
      z3_bvsort_array[16] = z3_bvsort_16;
      z3_bvsort_array[32] = z3_bvsort_32;
      z3_bvsort_array[64] = z3_bvsort_64;
    }

    static Z3_context mk_context(char *solver);
    static Z3_context mk_proof_context(bool solver, unsigned int is_uw);

    Z3_ast mk_var(Z3_context ctx, const char * name, Z3_type_ast ty);
    Z3_ast mk_bool_var(Z3_context ctx, const char * name);
    Z3_ast mk_int_var(Z3_context ctx, const char * name);
    Z3_ast mk_int(Z3_context ctx, int v);
    Z3_ast mk_unsigned_int(Z3_context ctx, unsigned int v);
    Z3_ast mk_real_var(Z3_context ctx, const char * name);
    Z3_sort mk_bv_sort(Z3_context, unsigned int width);
    Z3_ast mk_unary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x);
    Z3_ast mk_binary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x, Z3_ast y);
    Z3_lbool check(Z3_context ctx, Z3_lbool expected_result);
    Z3_lbool check2(Z3_context ctx, Z3_lbool expected_result);
    void prove(Z3_context ctx, Z3_ast f, Z3_bool is_valid);
    void assert_inj_axiom(Z3_context ctx, Z3_const_decl_ast f, unsigned i);
    void display_sort(Z3_context c, FILE * out, Z3_sort ty);
    void assert_comm_axiom(Z3_context ctx, Z3_const_decl_ast f);
    void display_ast(Z3_context c, FILE * out, Z3_ast v);
    Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val);
    Z3_ast mk_tuple_select(Z3_context c, Z3_ast t, unsigned i);
    void display_symbol(Z3_context c, FILE * out, Z3_symbol s);
    void display_type(Z3_context c, FILE * out, Z3_type_ast ty);
    void display_function_interpretations(Z3_context c, FILE * out, Z3_model m);
    void display_model(Z3_context c, FILE * out, Z3_model m);
    void display_version();

  public:
    Z3_sort z3_int_sort;
    Z3_sort z3_real_sort;
    Z3_sort z3_bool_sort;
    Z3_ast z3_true;
    Z3_ast z3_false;
    Z3_sort z3_intwidth_bv_sort;
    Z3_sort z3_bvsort_8, z3_bvsort_16, z3_bvsort_32, z3_bvsort_64;
    Z3_sort z3_bvsort_array[64];

  private:
    static Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err);
    Z3_context z3_ctx;
};

#endif
