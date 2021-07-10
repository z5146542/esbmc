/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_LINK_H
#define CPROVER_C_LINK_H

#include <util/context.h>

bool c_link(
  contextt &context,
  contextt &new_context,
  const std::string &module);

#endif
