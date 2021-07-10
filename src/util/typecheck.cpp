/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/message.h>
#include <util/typecheck.h>

bool typecheckt::typecheck_main()
{
  try
  {
    typecheck();
  }

  catch(const char *e)
  {
    log_error(e);
    return true;
  }

  catch(const std::string &e)
  {
    log_error(e);
    return true;
  }

  return false;
}
