#include "equiv/Equivalence.hpp"

using namespace ufo;

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
  const char *OPT_HELP = "--help";
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
  const char *OPT_INEQUALITY = "--allow-ineq";

  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                                  ALIEN - Equivalence Checker                                 * * *\n" <<
        "                                       Ameer Hamza et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " equiv-check [--help]               show help\n" <<
        " equiv-check [options] <file1.smt2> <file2.smt2>  Check equivalence betweeen two programs\n\n" <<
        "Options:\n" <<
        " " << OPT_ELIM << "                     do not minimize CHC rules (and do not slice)\n" <<
        " " << OPT_ARITHM << "                   do not apply arithmetic constant propagation during parsing\n" <<
        " " << OPT_TO << "                            timeout for each Z3 run in ms (default: 1000)\n" <<
        " " << OPT_DEBUG << " <LVL>                   print debugging information during run (default level: 0)\n\n" <<
        " " << OPT_DATA_LEARNING << " <N>                      bootstrap candidates from behaviors (0: no, NUM: rounds)\n" <<
        " " << OPT_MUT << "                           level of mutation for bootstrapped candidates (0: no, 1: (default), 2: full)\n" <<
        " " << OPT_SEED << "                   do not analyze syntax for seeds mining, except of the query\n" <<
        " " << OPT_PROP << " <N>                      rounds of candidate propagation before bootstrapping\n" << 
        " " << OPT_INEQUALITY << "                   allow inequality candidates while generating them\n";

    return 0;
  }

  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  int to = getIntValue(OPT_TO, 10000, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  bool d_se = !getBoolValue(OPT_SEED, false, argc, argv);
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
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);
  bool eq = getBoolValue(OPT_INEQUALITY, false, argc, argv);

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

  checkEquivalenceOfPrograms(argv[argc-2], argv[argc-1], max_attempts, to, densecode, aggressivepruning,
      do_dl, do_mu, do_elim, do_arithm, do_disj, do_prop, mbp_eqs,
      d_m, d_p, d_d, d_s, d_f, d_r, d_g, d_se, eq, debug);

  return 0;
}
