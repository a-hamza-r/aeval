#include "deep/BndExpl.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc != 4){
    outs() << "Please specify two cost variable names and the file name\n";
    return 0;
  }

  getCost(string(argv[argc-1]), string(argv[argc-2]), string(argv[argc-3]));

  return 0;
}
