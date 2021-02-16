#include "deep/Product.hpp"

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

int main (int argc, char ** argv)
{
	const char *OPT_BASE = "--base";
	const char *OPT_ALIGNED = "--aligned";

	bool base = getBoolValue(OPT_BASE, false, argc, argv);
	bool aligned = getBoolValue(OPT_ALIGNED, false, argc, argv);

	if (base + aligned > 1)
	{
		outs() << "Only one type of alignment can be chosen\n";
		return 0;
	}

	if (!base && !aligned) aligned = true; // default

	if (base)
 		createProductBase(argv[argc-2], argv[argc-1]);
 	else
 		createProductAligned(argv[argc-2], argv[argc-1]);

	return 0;
}
