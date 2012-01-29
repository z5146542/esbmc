/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

#include <std_types.h>
#include <goto-programs/goto_functions.h>

#include <i2string.h>
#include "basic_symex.h"
#include "reachability_tree.h"

class goto_symext:
  public basic_symext
{
public:
  goto_symext(
    const namespacet &_ns,
    contextt &_new_context,
    symex_targett &_target):
    basic_symext(_ns, _new_context, _target),
    total_claims(0),
    remaining_claims(0),
    guard_identifier_s("goto_symex::\\guard")
  {
    options.set_option("no-assertions", false);
    art1 = NULL;
  }

  ~goto_symext() {
    if (art1 != NULL)
      delete art1;
  }

    irep_idt get_symbol(const exprt & expr);

  // all at once
  virtual void operator()(
    const goto_functionst &goto_functions);

  virtual void operator()();

    bool restore_from_dfs_state(const reachability_treet::dfs_position &dfs);
    symex_target_equationt *multi_formulas_get_next_formula();
    bool multi_formulas_setup_next();
    void multi_formulas_init(const goto_functionst &goto_functions);
    void save_checkpoint(const std::string fname) const;

  void symex_step(
  const goto_functionst &goto_functions,
  reachability_treet & art);

  // these bypass the target maps
  virtual void symex_step_return(statet &state, execution_statet &ex_state, unsigned node_id);
  virtual void symex_step_goto(statet &state, bool taken, unsigned node_id);

protected:
  friend class symex_dereference_statet;
  reachability_treet *art1;

  void new_name(symbolt &symbol);

  // statistics
  unsigned total_claims, remaining_claims;

  void dereference(
    exprt &expr,
    statet &state,
    const bool write, unsigned node_id);

  void dereference_rec(
    exprt &expr,
    guardt &guard,
    class dereferencet &dereference,
    const bool write);

  // guards

  //irep_idt guard_identifier;
  irep_idt guard_identifier_s;

  irep_idt guard_identifier(statet &state)
  {
	  return irep_idt(id2string(guard_identifier_s) + "!" + i2string(state.top().level1._thread_id));
  };

  // symex

  virtual void symex_goto(statet &state, execution_statet &ex_state, unsigned node_id);

  virtual void symex_return(statet &state, execution_statet &ex_state, unsigned node_id);

  virtual void symex_other(
    const goto_functionst &goto_functions,
    statet &state,
    execution_statet &ex_state,
    unsigned node_id);

  virtual void claim(
    const exprt &expr,
    const std::string &msg,
    statet &state, unsigned node_id);

  // gotos
  void merge_gotos(statet &state, execution_statet &ex_state, unsigned node_id);

  void merge_value_sets(
    const statet::goto_statet &goto_state,
    statet &dest);

  void phi_function(
    const statet::goto_statet &goto_state,
    statet &state, execution_statet &ex_state, unsigned node_id);

  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);

  virtual void loop_bound_exceeded(statet &state, const exprt &guard,unsigned node_id);

  // function calls

  void pop_frame(statet &state);
  void return_assignment(statet &state, execution_statet &ex_state, unsigned node_id);

  virtual void no_body(const irep_idt &identifier __attribute__((unused)))
  {
  }

  virtual void symex_function_call(
    const goto_functionst &goto_functions,
    execution_statet &state,
    const code_function_callt &call);

  virtual void symex_end_of_function(statet &state);

  virtual void symex_function_call_symbol(
    const goto_functionst &goto_functions,
    execution_statet &state,
    const code_function_callt &call);

  virtual void symex_function_call_code(
    const goto_functionst &goto_functions,
    execution_statet &state,
    const code_function_callt &call);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    unsigned unwind);

  void argument_assignments(
    const code_typet &function_type,
    execution_statet &state,
    const exprt::operandst &arguments);

  void locality(
    unsigned frame_counter,
    statet &state,
    const goto_functionst::goto_functiont &goto_function,
    unsigned exec_node_id);

  void add_end_of_function(
    exprt &code,
    const irep_idt &identifier);

  void run_intrinsic(code_function_callt &call, reachability_treet &art,
                     const std::string symname);
  void intrinsic_yield(reachability_treet &arg);
  void intrinsic_switch_to(code_function_callt call, reachability_treet &art);

  // dynamic stuff
  virtual void replace_dynamic_allocation(const statet &state, exprt &expr);
  bool is_valid_object(const statet &state, const symbolt &symbol);
};

#endif
