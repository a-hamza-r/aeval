#ifndef EXTENDED_HORN__HPP__
#define EXTENDED_HORN__HPP__

#include "deep/Horn.hpp"

namespace ufo
{
  template <typename T>
    void concatenateVectors(vector<T> &result, const vector<T>& vec1, const vector<T>& vec2)
    {
      result.reserve(result.size()+vec1.size()+vec2.size());
      result.insert(result.end(), vec1.begin(), vec1.end());
      result.insert(result.end(), vec2.begin(), vec2.end());
    }


  /** 
   * Class adds extended functionality to Horn class
   * that is required for Equivalence Checking of Programs
   */
  class ExtendedCHCs : public CHCs
  {
    public:
      Expr loopRel;
      vector<int> varsInt;
      vector<int> varsBool;
      vector<int> varsArray;

      ExtendedCHCs(ExprFactory &efac, EZ3 &z3, string n, int d = false) : CHCs(efac, z3, n, d) {}
      ExtendedCHCs(const ExtendedCHCs &oldCHC, bool shallowCopy=false)
        : CHCs(oldCHC, shallowCopy) {};

      void categorizeVars() {
        for (int i = 0; i < invVars[loopRel].size(); i++) {
          Expr var = invVars[loopRel][i];
          if (bind::isIntConst(var)) varsInt.push_back(i);
          else if (bind::isBoolConst(var)) varsBool.push_back(i);
          else if (isOpX<ARRAY_TY>(bind::typeOf(var))) varsArray.push_back(i);
        }
      }

      HornRuleExt *getFact()
      {
        for (auto &chc : chcs)
        {
          if (chc.isFact) return &chc;
        }
        return NULL;
      }

      HornRuleExt *getQuery()
      {
        if (!hasQuery) return NULL;
        for (auto &chc : chcs)
        {
          if (chc.isQuery) return &chc;
        }
        return NULL;
      }

      void rulesOfPredicate(Expr decl, vector<HornRuleExt*> &rulesOfP)
      {
        for (auto& chc : chcs)
          if (decl == chc.dstRelation)
            rulesOfP.push_back(&chc);
      }
  };
}

#endif
