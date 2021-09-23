//
// Created by rafaelsamenezes on 23/09/2021.
//

#include <jimple-frontend/jimple-language.h>
#include <jimple-frontend/jimple-converter.h>
#include <util/message/format.h>


bool jimple_languaget::typecheck(contextt &context, const std::string &, const messaget &msg)
{
  msg.debug(fmt::format("Converting Jimple module {} to GOTO", root.getClassName()));

  contextt new_context(msg);
  jimple_converter converter(context, root, msg);
  if(converter.convert()) {
    msg.error(fmt::format("Failed to convert module {}", root.getClassName()));
    return true;
  }

  return true;
}