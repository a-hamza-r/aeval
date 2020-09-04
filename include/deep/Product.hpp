#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  inline void createProduct(const char * chcfileSrc, const char * chcfileDst)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManagerSrc(m_efac, z3, "_v1_");
    ruleManagerSrc.parse(string(chcfileSrc));

    CHCs ruleManagerDst(m_efac, z3, "_v2_");
    ruleManagerDst.parse(string(chcfileDst));

  };
}

#endif
