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

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
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

void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      values.push_back(string(argv[i+1]));
    }
  }
}

int main (int argc, char ** argv)
{
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_TO = "--to";
  const char *OPT_ELIM = "--skip-elim";
  const char *OPT_ARITHM = "--skip-arithm";
  const char *OPT_SEED = "--skip-syntax";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_AGG_PRUNING = "--aggp";
  const char *OPT_DATA_LEARNING = "--data";
  const char *OPT_MUT = "--mut";
  const char *OPT_PROP = "--prop";
  const char *OPT_DISJ = "--disj";
  const char *OPT_D1 = "--all-mbp";
  const char *OPT_D2 = "--phase-prop";
  const char *OPT_D3 = "--phase-data";
  const char *OPT_D4 = "--stren-mbp";
  const char *OPT_D5 = "--fwd";
  const char *OPT_D6 = "--prune";
  const char *OPT_REC = "--re";
  const char *OPT_MBP = "--eqs-mbp";
  const char *OPT_DEBUG = "--debug";
  const char *OPT_BASE = "--base";
  const char *OPT_ALIGNED = "--aligned";

  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  // bool d_se = !getBoolValue(OPT_SEED, false, argc, argv);
  // by default, turning this option true so that we skip processing of seeds
  bool d_se = !getBoolValue(OPT_SEED, true, argc, argv); 
  int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  int do_dl = getIntValue(OPT_DATA_LEARNING, 0, argc, argv);
  int do_mu = getIntValue(OPT_MUT, 1, argc, argv);
  int mbp_eqs = getIntValue(OPT_MBP, 1, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  int d_f = getIntValue(OPT_D5, 1, argc, argv);
  bool d_g = !getBoolValue(OPT_D6, false, argc, argv);
  bool d_r = getBoolValue(OPT_REC, false, argc, argv);
  bool base = getBoolValue(OPT_BASE, false, argc, argv);
  bool aligned = getBoolValue(OPT_ALIGNED, false, argc, argv);
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);

  if (d_m || d_p || d_d || d_s) do_disj = true;
  if (do_disj)
  {
    if (!d_p && !d_d)
    {
      if (debug) errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled. "
                        << "Enabling \"" << OPT_D3 << "\"\n";
      d_d = true;
    }
    if (!d_se)
    {
      if (debug) errs() << "WARNING: \"" << OPT_SEED << "\" and \"" << OPT_DISJ << "\" are incompatible. "
                        << "Ignoring \"" << OPT_SEED << "\"\n";
      d_se = true;
    }
    if (do_prop == 0) do_prop = 1;
    if (do_dl == 0) do_dl = 1;
  }
  
	if (base + aligned > 1)
	{
		outs() << "Only one type of alignment can be chosen\n";
		return 0;
	}

	if (!base && !aligned) aligned = true; // default

  checkEquivalence(argv[argc-2], argv[argc-1], aligned, max_attempts, to, densecode, aggressivepruning,
                     do_dl, do_mu, do_elim, do_arithm, do_disj, do_prop, mbp_eqs,
                     d_m, d_p, d_d, d_s, d_f, d_r, d_g, d_se, debug);

	return 0;
}
