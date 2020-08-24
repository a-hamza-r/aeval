#include "deep/BndExpl.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc != 5){
    outs() << "Please specify two cost variable names, the file name and number of unrolling level required\n";
    return 0;
  }

  getCost(string(argv[argc-2]), string(argv[argc-3]), string(argv[argc-4]), atoi(argv[argc-1]));

  return 0;
}
