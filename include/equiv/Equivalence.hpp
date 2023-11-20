#ifndef EQUIVALENCE__HPP__
#define EQUIVALENCE__HPP__

#include "Product.hpp"
#include "deep/RndLearnerV3.hpp"

namespace ufo
{
  /** 
   * Class defines the Equivalence Checking of Programs
   */
  class Equivalence
  {
    ExprFactory &m_efac;
    EZ3 &m_z3;
    SMTUtils u;
    unsigned to;
    bool freqs;
    bool aggp;
    int dat;
    int mut;
    bool doElim;
    bool doArithm;
    bool doDisj;
    int doProp;
    int mbpEqs;
    bool dAllMbp;
    bool dAddProp;
    bool dAddDat;
    bool dStrenMbp;
    int dFwd;
    bool dRec;
    bool dGenerous;
    int debug;
    bool dSee;
    ExprSet mapping;
    vector<pair<int, int>> pairings;
    ExtendedCHCs &source;
    ExtendedCHCs &target;

    public:
    Equivalence(ExtendedCHCs &r1, ExtendedCHCs &r2,
        unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut, bool _doElim,
        bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp,
        bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int _dFwd, bool _dRec,
        bool _dGenerous, bool _dSee, int _debug) :
      m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to),
      source(r1), target(r2), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
      doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp),
      mbpEqs(_mbpEqs), dAllMbp(_dAllMbp), dAddProp(_dAddProp), dAddDat(_dAddDat),
      dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec), dGenerous(_dGenerous),
      dSee(_dSee), debug(_debug) {}

    void setVariableCombs(std::vector<pair<int, int>>& _pairings) {
      pairings = _pairings;
    }

    void createVariableMapping(ProductCHCs &product) {
      ExprVector combinedVars;
      Expr dcl = product.chcs[product.cycles[product.loopRel][0][0]].srcRelation;
      concatenateVectors(combinedVars,
          source.invVars[source.loopRel], target.invVars[target.loopRel]);

      for (const auto &pr : pairings) {
        Expr e = mk<EQ>(source.invVars[source.loopRel][pr.first],
            target.invVars[target.loopRel][pr.second]);
        mapping.insert(replaceAll(e, combinedVars, product.invVars[dcl]));
      }
    }

    Expr getRelationalPrecondition(ProductCHCs &product) {
      Expr pre = conjoin(mapping, m_efac);
      return replaceAll(pre,
          product.invVars[product.loopRel], product.invVarsPrime[product.loopRel]);
    }

    bool factSanityCheck(Expr &factBody) {
      return bool(u.isSat(factBody));
    }

    bool checkLockstepComposability(ProductCHCs &product) {
      /* WARNING: this method has not been implemented yet */
      return true;
    }

    bool findIterators() {
      /* WARNING: this method has not been implemented yet */
      return true;
    }

    bool alignPrograms() {
      /* WARNING: this method has not been implemented yet */
      return true;
    }

    bool checkEquivalence(ProductCHCs &product) {
      /* WARNING: this method has not been implemented yet */
      return true;
    }

    bool refine(bool target = false) {
      /* WARNING: this method has not been implemented yet */
      return true;
    }
  };

  void combinations(vector<int> &vars1, vector<int> &vars2, vector<pair<int, int>> c,
      vector<int> vars2Used, vector<vector<pair<int, int>>> &combs, int pos)
  {
    if (c.size() >= vars1.size())
    {
      combs.push_back(c);
      return;
    }
    for (int i = 0; i < vars2.size(); i++)
    {
      if (find(vars2Used.begin(), vars2Used.end(), i) == vars2Used.end())
      {
        vars2Used.push_back(i);
        c.push_back({vars1[pos], vars2[i]});
        combinations(vars1, vars2, c, vars2Used, combs, pos+1);
        c.pop_back();
        vars2Used.pop_back();
      }
    }
  }


  void combinationsOfVars(vector<int> &vars1, vector<int> &vars2,
      vector<vector<pair<int, int>>> &combs)
  {
    for (int i = 0; i < vars2.size(); i++)
    {
      vector<int> vars2Used{i};
      pair<int, int> v{vars1[0], vars2[i]};
      vector<pair<int, int>> c{v};
      combinations(vars1, vars2, c, vars2Used, combs, 1);
    }
  }

  void joinVars(vector<vector<pair<int, int>>> &vec1, vector<vector<pair<int, int>>> &vec2,
      vector<vector<pair<int, int>>> &combs)
  {
    if (vec1.empty() || vec2.empty())
    {
      concatenateVectors(combs, vec1, vec2);
    }
    else
    {
      for (auto &it : vec1)
      {
        for (auto &it2 : vec2)
        {
          vector<pair<int, int>> v;
          concatenateVectors(v, it, it2);
          combs.push_back(v);
        }
      }
    }
  }

  void createVariableCombs(ExtendedCHCs &ruleManager1, ExtendedCHCs &ruleManager2,
      vector<vector<pair<int, int>>> &variableCombs)
  {

    vector<vector<pair<int, int>>> combsArray, combsInt, combsBool, combs1;
    combinationsOfVars(ruleManager1.varsArray, ruleManager2.varsArray, combsArray);
    combinationsOfVars(ruleManager1.varsInt, ruleManager2.varsInt, combsInt);
    combinationsOfVars(ruleManager1.varsBool, ruleManager2.varsBool, combsBool);

    joinVars(combsArray, combsInt, combs1);
    joinVars(combs1, combsBool, variableCombs);
  }

  void decomposeSource(ExtendedCHCs& source, ExtendedCHCs& target, ExtendedCHCs& SDecomposed)
  {
    /* WARNING: this method has not been implemented yet */
  }

  void projection(ExtendedCHCs& projRm, int i, ExtendedCHCs &origRm, bool multipleProjections)
  {
    /* WARNING: this method has not been implemented yet */
  }

  /**
   * check equivalence of two programs given as rule managers
   */
  bool checkEquivalenceOfRMs(ExtendedCHCs &source, ExtendedCHCs &target,
      unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
      bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
      bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
  {
    auto cycleSizeSrc = source.cycles.size();
    auto cycleSizeTgt = target.cycles.size();
    const auto& efac = source.m_efac;
    const auto& z3 = source.m_z3;

    assert(cycleSizeSrc == 1 && cycleSizeTgt >= 1);

    // shallow copy of source
    ExtendedCHCs decomposedSource(source, cycleSizeTgt > 1);
    if (cycleSizeTgt > 1)
      decomposeSource(source, target, decomposedSource);

    auto numProjections = decomposedSource.cycles.size();
    //assert(cycleSizeTgt == numProjections);
    //assert(target.chcs.size() == decomposedSource.chcs.size());

    for (int i = 0; i < numProjections; i++) {
      // TODO: Use move semantics for better performance
      ExtendedCHCs projectionSource(decomposedSource, numProjections > 1);
      projection(projectionSource, i, decomposedSource, numProjections > 1);

      ExtendedCHCs projectionTarget(target, numProjections > 1);
      projection(projectionTarget, i, target, numProjections > 1);

      // One possibility is to move the variable combinations related code outside the loop
      // but then it will need to copy multiple times for each projection
      // so it is better to keep it here
      projectionSource.categorizeVars();
      projectionTarget.categorizeVars();

      vector<vector<pair<int, int>>> variableCombs;
      createVariableCombs(projectionSource, projectionTarget, variableCombs);

      Equivalence equiv(projectionSource, projectionTarget, to, freqs, aggp,
          dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp,
          dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, debug);

      int j = 0;
      do {
        auto comb = variableCombs.empty() ? std::vector<pair<int, int>>{} : variableCombs[j];
        equiv.setVariableCombs(comb);

        bool equivalenceCheck = false;
        while (true) {
          // cex loop
          bool aligned = false;
          bool refined = false;

          // create product of source and target projections
          ProductCHCs product(projectionSource, projectionTarget, "_pr_", debug-2);
          product.createProduct();
          equiv.createVariableMapping(product);

          // fact sanity check
          auto fact = product.getFact();
          fact->body = mk<AND>(fact->body, equiv.getRelationalPrecondition(product));
          bool factSanity = equiv.factSanityCheck(fact->body);

          bool lockstepCheck = false;
          if (factSanity) {
            lockstepCheck = equiv.checkLockstepComposability(product);
          }
          if (!factSanity || !lockstepCheck) {
            // align the programs
            auto itersFound = equiv.findIterators();
            if (itersFound) aligned = equiv.alignPrograms();
            //return false;
            if (aligned) continue;
          }
          else {
            // check equivalence
            equivalenceCheck = equiv.checkEquivalence(product);
            if (equivalenceCheck) {
              break;
            }
          }
          bool refinedSource = equiv.refine();
          bool refinedTarget = equiv.refine(true);
          break;
        }
        if (equivalenceCheck) break;
        j++;
      } while (j < variableCombs.size());
    }
    return true;
  }

  /**
   * check equivalence of two programs given as filenames
   */
  inline void checkEquivalenceOfPrograms(const char *chcfileSrc, const char *chcfileDst,
      unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim, 
      bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
      bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, bool allowEq,
      int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    ExtendedCHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-2);
    ExtendedCHCs ruleManagerDst(m_efac, z3, "_v2_", debug-2);

    if (!ruleManagerSrc.parse(string(chcfileSrc), doElim, doArithm)) return;
    if (!ruleManagerDst.parse(string(chcfileDst), doElim, doArithm)) return;

    if (checkEquivalenceOfRMs(ruleManagerSrc, ruleManagerDst, to, freqs, aggp, dat, mut, doElim,
          doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, debug))
      outs() << "\nprograms are equivalent\n";
    else
      outs() << "\nprogram equivalence is unknown\n";
  };
}

#endif
