/*******************************************************************\

Module: 

Author: Rafael Menezes, rafael.sa.menezes@outlook.com

Maintainers:
\*******************************************************************/

#include <fmt/core.h>
#include <util/message.h>

void log_print(VerbosityLevel v, const std::string &message)
{
  switch(v)
  {
  case VerbosityLevel::Error:
    fmt::print(stderr, "{} ", message);
    break;

  case VerbosityLevel::Warning:
  case VerbosityLevel::Result:
  case VerbosityLevel::Progress:
  case VerbosityLevel::Status:
  case VerbosityLevel::Debug:
    fmt::print(stdout, "{} ", message);
    break;

  case VerbosityLevel::None:;
  }
  __builtin_unreachable();
}

void log_println(VerbosityLevel v)
{
  switch(v)
  {
  case VerbosityLevel::Error:
    fmt::print(stderr, "\n");
    break;

  case VerbosityLevel::Warning:
  case VerbosityLevel::Result:
  case VerbosityLevel::Progress:
  case VerbosityLevel::Status:
  case VerbosityLevel::Debug:
    fmt::print(stdout, "\n");
    break;

  case VerbosityLevel::None:;
  }
  __builtin_unreachable();
}
