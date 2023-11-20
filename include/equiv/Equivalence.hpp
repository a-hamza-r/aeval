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
    unsigned maxAttempts;
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
    Equivalence(ExtendedCHCs &r1, ExtendedCHCs &r2, unsigned _maxAttempts,
        unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut, bool _doElim,
        bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp,
        bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int _dFwd, bool _dRec,
        bool _dGenerous, bool _dSee, int _debug) :
      m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to),
      source(r1), target(r2), maxAttempts(_maxAttempts), to(_to), freqs(_freqs), aggp(_aggp),
      dat(_dat), mut(_mut), doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp),
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

    bool learnInvariantsPr(ProductCHCs &product, bool lockstepCheck = false)
    {
      if (product.hasBV)
      {
        outs() << "Bitvectors currently not supported. Try `bnd/expl`.\n";
        return false;
      }

      BndExpl bnd(product, to, debug);

      RndLearnerV3 ds(m_efac, m_z3, product, to, freqs, aggp, mut, dat, debug);

      map<Expr, ExprSet> cands;

      auto cycle = product.cycles[product.loopRel];
      for (int i = 0; i < cycle.size(); i++)
      {
        Expr dcl = product.chcs[cycle[i][0]].srcRelation;
        if (ds.initializedDecl(dcl)) continue;
        ds.initializeDecl(dcl);
        // adding the matching explicitly
        cands[dcl].insert(mapping.begin(), mapping.end());

        if (dSee || lockstepCheck) {
          Expr pref = bnd.compactPrefix(product.loopRel, i);
          ExprSet tmp;
          getConj(pref, tmp);
          for (auto & t : tmp)
            if (hasOnlyVars(t, product.invVars[dcl]))
              cands[dcl].insert(t);

          if (mut > 0) ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
          ds.initializeAux(cands[dcl], bnd, product.loopRel, i, pref);
        }
      }
      if (dat > 0) ds.getDataCandidates(cands);

      for (int i = 0; i < doProp; i++)
        for (auto & a : cands[product.loopRel]) ds.propagate(product.loopRel, a, true);
      ds.addCandidates(product.loopRel, cands[product.loopRel]);
      ds.prepareSeeds(product.loopRel, cands[product.loopRel]);

      bool check = ds.bootstrap();
      if (check || lockstepCheck) return check;

      ds.calculateStatistics();
      ds.deferredPriorities();
      std::srand(std::time(0));
      return ds.synthesize(maxAttempts);
    }

    bool checkLockstepComposability(ProductCHCs &product) {
      auto query = product.getQuery();
      auto &originalQuery = query->body;
      auto loopGuard1 = std::move(simplifyArithm(
            source.getPrecondition(&source.chcs[source.cycles[source.loopRel][0][0]])));
      auto loopGuard2 = std::move(simplifyArithm(
            target.getPrecondition(&target.chcs[target.cycles[target.loopRel][0][0]])));
      auto lockstepCheckPredicate = std::move(mk<NEQ>(loopGuard2, loopGuard1));
      query->body = std::move(mk<AND>(lockstepCheckPredicate, originalQuery));
      // TODO: according to paper, we need to return <inv, cex>
      bool lockstepCheck = learnInvariantsPr(product, true);
      query->body = originalQuery;
      return lockstepCheck;
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
    auto& efac = source.m_efac;
    const auto& TCycles = target.cycles[target.loopRel];
    auto TCyclesSize = TCycles.size();

    // Assuming that source only has one cycle
    int SPrefix = source.prefixes[source.loopRel][0].back();
    int SCycle = source.cycles[source.loopRel][0][0];
    const auto& SCycleCHC = source.chcs[SCycle];

    Expr SLoopRel = SCycleCHC.srcRelation;
    Expr SInductiveCHCRel_i_minus_1 = mk<TRUE>(efac);
    Expr SCycleDecl = source.getDeclByName(SLoopRel);
    ExprVector SLoopVars(SCycleDecl->args_begin()+1, SCycleDecl->args_end());
    const ExprVector& SLoopSrcVars = SCycleCHC.srcVars;
    Expr negSGuard;
    ExprVector& invVars = source.invVars[SLoopRel];
    ExprVector& invVarsPrime = source.invVarsPrime[SLoopRel];

    for (int cycleNum = 0; cycleNum < TCyclesSize; cycleNum++) {
      const auto& cycleList = TCycles[cycleNum];
      auto& cycleCHC = target.chcs[cycleList.back()];

      auto SNonInductiveCHC = source.chcs[SPrefix];
      auto SInductiveCHC = source.chcs[SCycle];

      // if-condition is required according to the paper implementation
      if (cycleNum < TCyclesSize-1) {
        // a better way would be to use precondition and eliminateQuantifiers
        auto TGuard = std::move(target.getPrecondition(&cycleCHC));
        auto P_i = replaceAll(TGuard, cycleCHC.srcVars, SInductiveCHC.srcVars);
        SInductiveCHC.body = mk<AND>(SInductiveCHC.body, P_i);
      }

      Expr SInductiveCHCRel_i = mkTerm<string>(lexical_cast<string>(SLoopRel)+
          "_"+to_string(cycleNum), efac);
      SDecomposed.invVars[SInductiveCHCRel_i] = invVars;
      SDecomposed.invVarsPrime[SInductiveCHCRel_i] = invVarsPrime;
      SDecomposed.decls.insert(bind::fdecl(SInductiveCHCRel_i, SLoopVars));

      SNonInductiveCHC.srcRelation = SInductiveCHCRel_i_minus_1;
      if (!isOpX<TRUE>(SInductiveCHCRel_i_minus_1)) {
        SNonInductiveCHC.srcVars = SLoopSrcVars;
        SNonInductiveCHC.body = negSGuard;
        SNonInductiveCHC.isFact = false;
      }
      SNonInductiveCHC.dstRelation = SInductiveCHCRel_i;
      SInductiveCHC.srcRelation = SInductiveCHC.dstRelation = SInductiveCHCRel_i;
      SInductiveCHCRel_i_minus_1 = SInductiveCHCRel_i;

      SDecomposed.chcs.push_back(SNonInductiveCHC);
      SDecomposed.chcs.push_back(SInductiveCHC);

      auto SGuard = SDecomposed.getPrecondition(&SDecomposed.chcs.back());
      negSGuard = mkNeg(replaceAll(SGuard, invVars, invVarsPrime));
    }

    auto SQuery = source.getQuery();
    SQuery->srcRelation = SInductiveCHCRel_i_minus_1;
    SDecomposed.chcs.push_back(*SQuery);
    SDecomposed.findCycles();
  }

  void projection(ExtendedCHCs& projRm, int i, ExtendedCHCs &origRm, bool multipleProjections)
  {
    auto loopRel = origRm.wtoDecls[i];
    const auto cycle = origRm.chcs[origRm.cycles[loopRel][0][0]];
    projRm.loopRel = loopRel;
    if (!multipleProjections) {
      auto query = projRm.getQuery();
      query->body = mk<TRUE>(origRm.m_efac);
      return;
    }

    auto prefix = origRm.chcs[origRm.prefixes[loopRel][0].back()];
    if (!prefix.isFact) {
      prefix.srcRelation = mk<TRUE>(origRm.m_efac);
      prefix.srcVars.clear();
      prefix.isFact = true;
    }
    projRm.chcs.push_back(std::move(prefix));
    projRm.chcs.push_back(std::move(cycle));

    projRm.decls.insert(origRm.getDeclByName(loopRel));
    projRm.invVars[loopRel] = origRm.invVars[loopRel];
    projRm.invVarsPrime[loopRel] = origRm.invVarsPrime[loopRel];

    projRm.chcs.push_back(HornRuleExt());
    projRm.hasQuery = true;
    HornRuleExt& hr = projRm.chcs.back();
    hr.srcRelation = loopRel;
    hr.dstRelation = mk<FALSE>(origRm.m_efac);
    hr.isQuery = true;
    hr.isFact = false;
    hr.isInductive = false;
    hr.srcVars = cycle.srcVars;
    hr.dstVars = ExprVector{};
    hr.body = mk<TRUE>(origRm.m_efac);

    projRm.findCycles();
  }

  /**
   * check equivalence of two programs given as rule managers
   */
  bool checkEquivalenceOfRMs(ExtendedCHCs &source, ExtendedCHCs &target, unsigned maxAttempts,
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

    if (debug >= 1) {
      outs () << "\n\n      ** Decomposed Source **     \n";
      decomposedSource.print(debug >= 3);
    }

    auto numProjections = decomposedSource.cycles.size();
    assert(cycleSizeTgt == numProjections);
    assert(target.chcs.size() == decomposedSource.chcs.size());

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

      Equivalence equiv(projectionSource, projectionTarget, maxAttempts, to, freqs, aggp,
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

    ExtendedCHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-1);
    ExtendedCHCs ruleManagerDst(m_efac, z3, "_v2_", debug-1);

    if (debug >= 1) outs() << "Checking equivalence of Source and Target:\n";
    if (debug >= 1) outs() << "\n\n     ** Source **        ";
    if (!ruleManagerSrc.parse(string(chcfileSrc), doElim, doArithm)) return;
    if (debug >= 1) outs() << "\n\n     ** Target **        ";
    if (!ruleManagerDst.parse(string(chcfileDst), doElim, doArithm)) return;

    if (checkEquivalenceOfRMs(ruleManagerSrc, ruleManagerDst, maxAttempts, to, freqs, aggp, dat,
          mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
          dFwd, dRec, dGenerous, dSee, debug))
      outs() << "\nprograms are equivalent\n";
    else
      outs() << "\nprogram equivalence is unknown\n";
  };
}

#endif
