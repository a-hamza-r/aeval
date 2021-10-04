#include "deep/Equivalence.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      char* p;
      int num = strtol(argv[i+1], &p, 10);
      if (*p) return 1;      // if used w/o arg, return boolean
      else return num;
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
	const char *OPT_BASE = "--base";
	const char *OPT_ALIGNED = "--aligned";
  

	bool base = getBoolValue(OPT_BASE, false, argc, argv);
	bool aligned = getBoolValue(OPT_ALIGNED, false, argc, argv);
  int debug = getIntValue("--debug", 0, argc, argv);

	if (base + aligned > 1)
	{
		outs() << "Only one type of alignment can be chosen\n";
		return 0;
	}

	if (!base && !aligned) aligned = true; // default

	if (base)
 		checkEquivalenceWithoutAligning(argv[argc-2], argv[argc-1], debug);
 	else
 		checkEquivalenceWithAligning(argv[argc-2], argv[argc-1], debug);

	return 0;
}
