#include <goto-programs/goto_program.h>
#include <iomanip>
#include <langapi/language_util.h>
#include <util/message/default_message.h>

std::string get_last_tmp2(const std::string lines) {
  // step 1: get the last line
  std::string delim1 = "\n        ";
  size_t last = 0;
  size_t next = 0;
  
  while((next = lines.find(delim1, last)) != std::string::npos)
    last = next + delim1.length();
  std::string line = lines.substr(last);

  // step 2: get the lhs of the last line
  std::string delim2 = " := ";
  std::string token = line.substr(0, line.find(delim2));
  return token;
}

void goto_programt::instructiont::dump() const
{
  default_message msg;
  std::ostringstream oss;
  output_instruction(*migrate_namespace_lookup, "", oss, msg);
  msg.debug(oss.str());
}

void goto_programt::instructiont::output_instruction(
  const class namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out,
  const messaget &msg,
  bool show_location) const
{
  show_location = false;
  if(show_location)
  {
    out << "        (* " << location_number << " ";

    if(!location.is_nil())
      out << location.as_string();
    else
      out << "no location";

    out << " *)\n";
  }

  if(!labels.empty())
  {
    out << "        (* Labels:";
    for(const auto &label : labels)
    {
      out << " " << label;
    }

    out << "*) \n";
  }

  if(is_target())
    out << std::setw(5) << "t" << target_number << ": ";
  else
    out << "        ";

  switch(type)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET"
        << "\n";
    break;

  case GOTO:
    if(!is_true(guard))
    {
      std::string lines = from_expr(ns, identifier, guard, msg);
      std::string token = get_last_tmp2(lines);
      out << lines << "\n";
      out << "        " << "vtb := \"i__bool_of_value\"(" << token << ");\n";
      out << "        " << "goto [vtb] ";
    }
    else {
      out << "goto ";
    }
    
    for(instructiont::targetst::const_iterator gt_it = targets.begin();
        gt_it != targets.end();
        gt_it++)
    {
      if(gt_it != targets.begin())
        out << ", ";
      out << "t" <<(*gt_it)->target_number;
      if(!is_true(guard)) {
        out << " ";
        out << "s" << (*gt_it)->target_number;
        out << ";\n";
        out << std::setw(5) << "s" << (*gt_it)->target_number << ": ";
        out << "skip;";
      }
      else {
        out << ";";
      }
    }

    out << "\n";
    break;

  case FUNCTION_CALL:
  {
    std::string output = from_expr(ns, "", migrate_expr_back(code), msg);
    if(output.find("\"pthread_start_main_hook\"(") != std::string::npos
    || output.find("\"pthread_end_main_hook\"(") != std::string::npos
    || output.find("\"main\"(") != std::string::npos) {
      out << "skip;" << "\n";
      break;
    }
    out << output << ";\n";
    break;
  }
  case RETURN:
  {
    std::string arg;
    const code_return2t &ref = to_code_return2t(code);
    if(!is_nil_expr(ref.operand))
      arg = from_expr(ns, "", ref.operand, msg);
    if(arg.find(" := ") != std::string::npos) {
      std::string token = get_last_tmp2(arg);
      out << arg << "\n";
      out << "        ";
      out << "ret := " << token << ";\n";
    } else {
      out << "ret := " << arg << ";\n";
    }
      out << "        " << "return;\n";
  }
  break;

  case DECL:
  case DEAD:
  case OTHER:
  case ASSIGN:
  {

    std::string output = from_expr(ns, identifier, code, msg);
    if(output.find("__ESBMC") != std::string::npos) {
      out << "skip;" << "\n";
      break;
    }

    // If "i__storegv" is called within "genv_init", the variable must be initialised with "i__set_glob_var".
    if (identifier.as_string().find("__ESBMC_main") != std::string::npos && output.find("store") != std::string::npos) {
      std::string glovar_info = output.substr(output.find("i__storegv")+13);
      std::string glovar_ident_string = glovar_info.substr(0,glovar_info.find("\""));
      std::string glovar_size_string = glovar_info.substr(glovar_info.find("{{")+4);
      glovar_size_string = glovar_size_string.substr(0, glovar_size_string.find("\""));
      std::string size_bytes;
      if (glovar_size_string=="uint8"||glovar_size_string=="int8") size_bytes = "1";
      else if (glovar_size_string=="uint16"||glovar_size_string=="int16") size_bytes = "2";
      else if (glovar_size_string=="uint32"||glovar_size_string=="int32") size_bytes = "4";
      else if (glovar_size_string=="uint64"||glovar_size_string=="int64") size_bytes = "8";
      else if (output.find("NULL") != std::string::npos) size_bytes = "32";
      else throw("type not recognised");
      out << "tmp := \"i__set_glob_var\"(\"" + glovar_ident_string + "\", " + size_bytes + "i);\n        ";
    }

    // If an assignment does not have " := ", this means this
    // is a nop operation. Semantically, this is equivalent to skip.
    if(output.find(" := ") == std::string::npos || output.find("NULL") != std::string::npos) {
      out << "skip;" << "\n";
      break;
    }
    out << output << "\n";
    break;
  }
  case ASSUME:
  case ASSERT:
    // out << "skip;" << "\n";
    // break;
    {
      std::string dest_t;
      if(is_assume())
        dest_t = "assume (";
      else
        dest_t = "assert (";

    
      std::string arg = from_expr(ns, identifier, guard, msg);
      if(arg.find(" := ") != std::string::npos) {
        std::string token = get_last_tmp2(arg);
        out << arg
            << "\n        ";
        dest_t += token;
      } else
        dest_t += arg;

      // const irep_idt &comment = location.comment();
      // if(comment != "")
      //   out << " (* " << comment << " *)";
    

      dest_t += " == {{ \"int32\", 1i }});\n";
      out << dest_t;
    }
    break;

  case SKIP:
    out << "skip;"
        << "\n";
    break;

  case END_FUNCTION:
    {
      const symbolt *symbol = NULL;
      ns.lookup(identifier, symbol);
      if(from_type(ns, symbol->id, symbol->type, msg).find("void") != std::string::npos)
        out << "ret := undefined;" << "\n        ";
    }
    out << "return\n};";
    if(show_location) {
      const irep_idt &function = location.function();
      if(function != "")
        out << " (* " << function << " *)";
    }
    out << "\n";
    break;

  case LOCATION:
    //out << "LOCATION"
    //    << "\n";
    break;

  case THROW:
    out << "THROW";

    {
      const code_cpp_throw2t &throw_ref = to_code_cpp_throw2t(code);
      for(auto const &it : throw_ref.exception_list)
      {
        if(it != *throw_ref.exception_list.begin())
          out << ",";
        out << " " << it;
      }

      if(!is_nil_expr(throw_ref.operand))
        out << ": " << from_expr(ns, identifier, throw_ref.operand, msg);
    }

    out << "\n";
    break;

  case CATCH:
    out << "CATCH ";

    {
      unsigned i = 0;
      const code_cpp_catch2t &catch_ref = to_code_cpp_catch2t(code);
      assert(targets.size() == catch_ref.exception_list.size());

      for(instructiont::targetst::const_iterator gt_it = targets.begin();
          gt_it != targets.end();
          gt_it++, i++)
      {
        if(gt_it != targets.begin())
          out << ", ";
        out << catch_ref.exception_list[i] << "->" << (*gt_it)->target_number;
      }
    }

    out << "\n";
    break;

  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN"
        << "\n";
    break;

  case ATOMIC_END:
    out << "ATOMIC_END"
        << "\n";
    break;

  case THROW_DECL:
    out << "THROW_DECL (";

    {
      const code_cpp_throw_decl2t &ref = to_code_cpp_throw_decl2t(code);

      for(unsigned int i = 0; i < ref.exception_list.size(); ++i)
      {
        if(i)
          out << ", ";
        out << ref.exception_list[i];
      }
      out << ")";
    }

    out << "\n";
    break;

  case THROW_DECL_END:
    out << "THROW_DECL_END (";

    if(!is_nil_expr(code))
    {
      const code_cpp_throw_decl_end2t &decl_end =
        to_code_cpp_throw_decl_end2t(code);

      for(auto const &it : decl_end.exception_list)
      {
        if(it != *decl_end.exception_list.begin())
          out << ", ";
        out << it;
      }
    }

    out << ")";

    out << "\n";
    break;

  default:
    throw "unknown statement";
  }
}

bool operator<(
  const goto_programt::const_targett i1,
  const goto_programt::const_targett i2)
{
  const goto_programt::instructiont &_i1 = *i1;
  const goto_programt::instructiont &_i2 = *i2;
  return &_i1 < &_i2;
}

void goto_programt::compute_loop_numbers(unsigned int &num)
{
  for(auto &instruction : instructions)
    if(instruction.is_backwards_goto())
    {
      (*instruction.targets.begin())->loop_number = num;
      instruction.loop_number = num++;
    }
}

void goto_programt::get_successors(targett target, targetst &successors)
{
  successors.clear();
  if(target == instructions.end())
    return;

  targett next = target;
  next++;

  const instructiont &i = *target;

  if(i.is_goto())
  {
    for(auto target : i.targets)
      successors.push_back(target);

    if(!is_true(i.guard))
      successors.push_back(next);
  }
  else if(i.is_throw())
  {
    // the successors are non-obvious
  }
  else if(i.is_return())
  {
    // the successor is the end_function at the end of the function
    successors.push_back(--instructions.end());
  }
  else if(i.is_assume())
  {
    if(!is_false(i.guard))
      successors.push_back(next);
  }
  else
    successors.push_back(next);
}

void goto_programt::get_successors(
  const_targett target,
  const_targetst &successors) const
{
  successors.clear();
  if(target == instructions.end())
    return;

  const auto next = std::next(target);

  const instructiont &i = *target;

  if(i.is_goto())
  {
    for(auto target : i.targets)
      successors.emplace_back(target);

    if(!is_true(i.guard) && next != instructions.end())
      successors.push_back(next);
  }
  else if(i.is_return())
  {
    // the successor is the end_function at the end
    successors.push_back(--instructions.end());
  }
  else if(i.is_assume())
  {
    if(!is_false(i.guard))
      successors.push_back(next);
  }
  else
    successors.push_back(next);
}

void goto_programt::update()
{
  compute_target_numbers();
  compute_location_numbers();
}

std::ostream &goto_programt::output(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out) const
{
  // output program

  for(const auto &instruction : instructions)
    instruction.output_instruction(ns, identifier, out, msg);

  return out;
}

void goto_programt::compute_target_numbers()
{
  // reset marking

  for(auto &instruction : instructions)
    instruction.target_number = -1;

  // mark the goto targets

  for(instructionst::const_iterator it = instructions.begin();
      it != instructions.end();
      it++)
  {
    for(auto t : it->targets)
    {
      if(t != instructions.end())
        t->target_number = 0;
    }
  }

  // number the targets properly
  unsigned cnt = 0;

  for(instructionst::iterator it = instructions.begin();
      it != instructions.end();
      it++)
  {
    if(it->is_target())
    {
      it->target_number = ++cnt;
      assert(it->target_number != 0);
    }
  }

  // check the targets!
  // (this is a consistency check only)

  for(instructionst::const_iterator it = instructions.begin();
      it != instructions.end();
      it++)
  {
    for(auto t : it->targets)
    {
      if(t != instructions.end())
      {
        assert(t->target_number != 0);
        assert(t->target_number != unsigned(-1));
      }
    }
  }
}

void goto_programt::copy_from(const goto_programt &src)
{
  // Definitions for mapping between the two programs
  typedef std::map<const_targett, targett> targets_mappingt;
  targets_mappingt targets_mapping;

  clear();

  // Copy hide flag
  hide = src.hide;

  // Loop over program - 1st time collects targets and copy

  for(instructionst::const_iterator it = src.instructions.begin();
      it != src.instructions.end();
      it++)
  {
    targett new_instruction = add_instruction();
    targets_mapping[it] = new_instruction;
    *new_instruction = *it;
  }

  // Loop over program - 2nd time updates targets

  for(auto &instruction : instructions)
  {
    for(auto &target : instruction.targets)
    {
      targets_mappingt::iterator m_target_it = targets_mapping.find(target);

      if(m_target_it == targets_mapping.end())
        throw "copy_from: target not found";

      target = m_target_it->second;
    }
  }

  compute_target_numbers();
}

std::ostream &operator<<(std::ostream &out, goto_program_instruction_typet t)
{
  switch(t)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO_INSTRUCTION_TYPE";
    break;
  case GOTO:
    out << "GOTO";
    break;
  case ASSUME:
    out << "ASSUME";
    break;
  case ASSERT:
    out << "ASSERT";
    break;
  case OTHER:
    out << "OTHER";
    break;
  case SKIP:
    out << "SKIP";
    break;
  case LOCATION:
    out << "LOCATION";
    break;
  case END_FUNCTION:
    out << "END_FUNCTION";
    break;
  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN";
    break;
  case ATOMIC_END:
    out << "ATOMIC_END";
    break;
  case RETURN:
    out << "RETURN";
    break;
  case ASSIGN:
    out << "ASSIGN";
    break;
  case FUNCTION_CALL:
    out << "FUNCTION_CALL";
    break;
  case THROW:
    out << "THROW";
    break;
  case CATCH:
    out << "CATCH";
    break;
  case THROW_DECL:
    out << "THROW_DECL";
    break;
  default:
    out << "? (number: " << t << ")";
  }

  return out;
}

void goto_programt::dump() const
{
  default_message msg;
  std::ostringstream oss;
  output(*migrate_namespace_lookup, "", oss);
  msg.debug(oss.str());
}

void goto_programt::get_decl_identifiers(
  decl_identifierst &decl_identifiers) const
{
  forall_goto_program_instructions(it, (*this))
  {
    if(it->is_decl())
      decl_identifiers.insert(to_code_decl2t(it->code).value);
  }
}
