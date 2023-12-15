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
      Expr dcl = product.chcs[product.cycles[product.loopheads[0]][0][0]].srcRelation;
      concatenateVectors(combinedVars,
          source.invVars[source.loopheads[0]], target.invVars[target.loopheads[0]]);

      for (const auto &pr : pairings) {
        Expr e = mk<EQ>(source.invVars[source.loopheads[0]][pr.first],
            target.invVars[target.loopheads[0]][pr.second]);
        mapping.insert(replaceAll(e, combinedVars, product.invVars[dcl]));
      }
    }

    Expr getRelationalPrecondition(ProductCHCs &product) {
      Expr pre = conjoin(mapping, m_efac);
      return replaceAll(pre,
          product.invVars[product.loopheads[0]], product.invVarsPrime[product.loopheads[0]]);
    }

    bool factSanityCheck(Expr &factBody) {
      return bool(u.isSat(factBody));
    }

    bool learnInvariants(ExtendedCHCs &ruleManager, bool lockstepCheck = false)
    {
      if (ruleManager.hasBV)
      {
        outs() << "Bitvectors currently not supported. Try `bnd/expl`.\n";
        return false;
      }

      BndExpl bnd(ruleManager, to, debug);

      RndLearnerV3 ds(m_efac, m_z3, ruleManager, to, freqs, aggp, mut, dat, debug);

      map<Expr, ExprSet> cands;

      for (auto& cyc : ruleManager.cycles) {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++)
        {
          Expr dcl = ruleManager.chcs[cyc.second[i][0]].srcRelation;
          if (ds.initializedDecl(dcl)) continue;
          ds.initializeDecl(dcl);
          // adding the matching explicitly
          cands[dcl].insert(mapping.begin(), mapping.end());

          if (dSee || lockstepCheck) {
            Expr pref = bnd.compactPrefix(rel, i);
            ExprSet tmp;
            getConj(pref, tmp);
            for (auto & t : tmp)
              if (hasOnlyVars(t, ruleManager.invVars[dcl]))
                cands[dcl].insert(t);

            if (mut > 0) ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
            ds.initializeAux(cands[dcl], bnd, rel, i, pref);
          }
        }
      }
      if (dat > 0) ds.getDataCandidates(cands);

      for (auto & dcl: ruleManager.wtoDecls)
      {
        for (int i = 0; i < doProp; i++)
          for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
        ds.addCandidates(dcl, cands[dcl]);
        ds.prepareSeeds(dcl, cands[dcl]);
      }

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
            source.getPrecondition(&source.chcs[source.cycles[source.loopheads[0]][0][0]])));
      auto loopGuard2 = std::move(simplifyArithm(
            target.getPrecondition(&target.chcs[target.cycles[target.loopheads[0]][0][0]])));
      auto lockstepCheckPredicate = std::move(mk<NEQ>(loopGuard2, loopGuard1));
      query->body = std::move(mk<AND>(lockstepCheckPredicate, originalQuery));
      // TODO: according to paper, we need to return <inv, cex>
      bool lockstepCheck = learnInvariants(product, true);
      query->body = originalQuery;
      return lockstepCheck;
    }

    bool findIterators() {
      //source.preprocessing();
      //target.preprocessing();
      return source.findIterators() && target.findIterators();
    }

    bool getAlignmentVals(ExprSet& pre, AlignmentParams& params)
    {
      Expr numItersS = source.iter->numOfIters;
      Expr numItersT = target.iter->numOfIters;

      // variables required for the quantified formula for optimization query
      Expr coef1 = bind::intConst(mkTerm<string>("coef1", m_efac));
      Expr coef2 = bind::intConst(mkTerm<string>("coef2", m_efac));
      Expr const1 = bind::intConst(mkTerm<string>("const1", m_efac));
      Expr const2 = bind::intConst(mkTerm<string>("const2", m_efac));
      Expr numIters1 = bind::intConst(mkTerm<string>("numIters1", m_efac));
      Expr numIters2 = bind::intConst(mkTerm<string>("numIters2", m_efac));

      // remove redundant clauses in precondition
      for (auto it = pre.begin(); it != pre.end(); )
        if (emptyIntersect(*it, numItersS) &&
            emptyIntersect(*it, numItersT)) it = pre.erase(it);
        else ++it;

      // add exact value for numIters to precondition
      pre.insert(mk<EQ>(numIters1, numItersS));
      pre.insert(mk<EQ>(numIters2, numItersT));
      Expr exprPre = conjoin(pre, m_efac);

      // get all variables in the precondition
      ExprVector varsIters;
      filter(exprPre, IsConst(), inserter(varsIters, varsIters.begin()));

      auto zero = mkMPZ(0, m_efac);
      // coef1 > 0 && coef2 > 0
      Expr coefs = mk<AND>(mk<GT>(coef1, zero), mk<GT>(coef2, zero));
      // const1 >= 0 && const2 >= 0
      Expr consts = mk<AND>(mk<GEQ>(const1, zero), mk<GEQ>(const2, zero));
      // coef2 * (numIters1 - const1) = coef1 * (numIters2 - const2)
      Expr constraint = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters1, const1)),
          mk<MULT>(coef1, mk<MINUS>(numIters2, const2)));
      // pre => constraint
      Expr preImpliesCst = mk<IMPL>(exprPre, constraint);
      Expr quantifiedPreImpliesCst = mkQFla(preImpliesCst, varsIters, true);
      // exists coef1, coef2, const1, const2 . forall varsIters . pre => constraint
      Expr quantifiedFla = mk<AND>(mk<AND>(consts, coefs), quantifiedPreImpliesCst);

      ExprMap c1, c2, c12;
      c12[const1] = zero;     c12[const2] = zero;
      c1[const1] = zero;      c2[const2] = zero;

      Expr model = nullptr;
      if (bool(u.isSat(replaceAll(quantifiedFla, c12)))) model = u.getModel();
      else if (bool(u.isSat(replaceAll(quantifiedFla, c1)))) model = u.getModel();
      else if (bool(u.isSat(replaceAll(quantifiedFla, c2)))) model = u.getModel();
      else if (bool(u.isSat(quantifiedFla))) model = u.getModel();
      if (model == nullptr)
      {
        outs() << "No satisfying assignment for quantified formula was found\n";
        return false;
      }

      // iterative solving optimization query to get all minModels
      ExprMap mp;
      ExprSet s{coef1, coef2, const1, const2};
      Expr minCoef1, minCoef2, minConst1, minConst2;

      // Solve for min coef1
      u.getOptModel<LT>(s, mp, coef1);
      minCoef1 = mp[coef1];
      quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef1, minCoef1));
      u.isSat(quantifiedFla);

      // Solve for min coef2
      u.getOptModel<LT>(s, mp, coef2);
      minCoef2 = mp[coef2];
      quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef2, minCoef2));
      u.isSat(quantifiedFla);

      // Solve for min const1
      u.getOptModel<LT>(s, mp, const1);
      minConst1 = mp[const1];
      quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(const1, minConst1));
      u.isSat(quantifiedFla);

      // Solve for min const2
      u.getOptModel<LT>(s, mp, const2);
      minConst2 = mp[const2];

      params.itersInLoopS = (int)lexical_cast<cpp_int>(minCoef1);
      params.itersOutLoopS = (int)lexical_cast<cpp_int>(minConst1);
      params.itersInLoopT = (int)lexical_cast<cpp_int>(minCoef2);
      params.itersOutLoopT = (int)lexical_cast<cpp_int>(minConst2);

      outs() << "copy "
        << params.itersOutLoopS << " iterations of loop 1 to fact and query combined\n";
      outs() << "copy "
        << params.itersOutLoopT << " iterations of loop 2 to fact and query combined\n";
      outs() << "we need " << params.itersInLoopS << " iterations of loop 1 to align\n";
      outs() << "we need " << params.itersInLoopT << " iterations of loop 2 to align\n";

      return true;
    }

    bool alignPrograms()
    {
      HornRuleExt &cycleS = source.chcs[source.cycles[source.loopheads[0]][0][0]];
      HornRuleExt &prefixS = source.chcs[source.prefixes[source.loopheads[0]][0][0]];

      HornRuleExt &cycleT = target.chcs[target.cycles[target.loopheads[0]][0][0]];
      HornRuleExt &prefixT = target.chcs[target.prefixes[target.loopheads[0]][0][0]];

      BndExpl bnd1(source, debug);
      BndExpl bnd2(target, debug);
      Expr pref1 = bnd1.compactPrefix(source.loopheads[0], 0);
      Expr pref2 = bnd2.compactPrefix(target.loopheads[0], 0);
      auto iterStructS = source.iter;
      auto iterStructT = target.iter;
      ExprSet equalityChecks, preForQuantifiedFla;

      for (const auto &pair : pairings)
      {
        auto &p1 = pair.first, &p2 = pair.second;
        Expr var1Src = cycleS.srcVars[p1];
        Expr var2Src = cycleT.srcVars[p2];
        Expr var1Dst = cycleS.dstVars[p1];
        Expr var2Dst = cycleT.dstVars[p2];

        // we create here the pre required for quantified formula
        // and pre to check equality of iters later
        // we do not want to add arrays to any of the pre version
        if (!isOpX<ARRAY_TY>(bind::typeOf(var1Src)))
        {
          equalityChecks.insert(mk<EQ>(var1Dst, var1Dst));
          preForQuantifiedFla.insert(mk<EQ>(var1Src, var2Src));
        }
      }

      AlignmentParams params;
      if (!getAlignmentVals(preForQuantifiedFla, params)) return false;

      // Currently, it does all combinations to check the number of iterations
      // to be added to fact and query
      vector<int> combsS, combsT;
      for (int i = 0; i <= params.itersOutLoopS; i++) combsS.push_back(i);
      for (int i = 0; i <= params.itersOutLoopT; i++) combsT.push_back(i);

      vector<pair<int, int>> possibleFactAligns;
      for (auto &it : combsS)
        for (auto &it2 : combsT)
          possibleFactAligns.push_back({it, it2});

      Expr eq = mk<EQ>(cycleS.dstVars[iterStructS->var], cycleT.dstVars[iterStructT->var]);
      for (const auto &possibleAlign : possibleFactAligns)
      {
        Expr prefixBody1 = prefixS.body, prefixBody2 = prefixT.body;
        int toFactS = possibleAlign.first, toFactT = possibleAlign.second;
        int toQueryS = params.itersOutLoopS - toFactS, toQueryT = params.itersOutLoopT - toFactT;

        // check if adding certain iterations to fact will make
        // the initial values of iterators equal
        // it is not greedy approach currently
        source.createAlignment(0, toFactS, 0, bnd1, prefixBody1, false);
        target.createAlignment(0, toFactT, 0, bnd2, prefixBody2, false);
        equalityChecks.insert(prefixBody1);
        equalityChecks.insert(prefixBody2);

        if (bool(u.implies(conjoin(equalityChecks, m_efac), eq)))
        {
          Expr prefixBody1 = prefixS.body, prefixBody2 = prefixT.body;
          // actual alignment created here
          source.createAlignment(params.itersInLoopS, toFactS, toQueryS, bnd1, prefixBody1);
          prefixS.body = prefixBody1;

          target.createAlignment(params.itersInLoopT, toFactT, toQueryT, bnd2, prefixBody2);
          prefixT.body = prefixBody2;

          for (auto &chc : source.chcs)
          {
            chc.body = simplifyArithm(eliminateQuantifiers(chc.body, chc.locVars, true, false));
            chc.locVars.clear();
          }

          for (auto &chc : target.chcs)
          {
            chc.body = simplifyArithm(eliminateQuantifiers(chc.body, chc.locVars, true, false));
            chc.locVars.clear();
          }
          return true;
        }
      }
      return false;
    }

    bool checkEquivalence(ProductCHCs &product) {
      auto query = product.getQuery();
      auto &originalQuery = query->body;
      auto loopGuardS = std::move(
          source.getPrecondition(&source.chcs[source.cycles[source.loopheads[0]][0][0]]));
      Expr negationLoopGuardS = std::move(mkNeg(loopGuardS));
      Expr post = std::move(simplifyBool(mkNeg(conjoin(mapping, m_efac))));
      // we only add negation of loop guard of source because we have verified,
      // using lockstep check, that loop guards of source and target are always equal
      query->body = std::move(mk<AND>(originalQuery, mk<AND>(negationLoopGuardS, post)));
      bool equivalenceCheck = learnInvariants(product);
      query->body = originalQuery;
      return equivalenceCheck;
    }

    bool refine() {
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
    auto TCyclesSize = target.cycles.size();

    // Assuming that source only has one cycle
    Expr SLoopRel = source.loopheads[0];
    auto SPrefix = source.prefixes[SLoopRel][0].back();
    auto SCycle = source.cycles[SLoopRel][0][0];
    const HornRuleExt& SCycleCHC = source.chcs[SCycle];

    Expr SInductiveCHCRel_i_minus_1 = mk<TRUE>(efac);
    Expr SCycleDecl = source.getDeclByName(SLoopRel);
    ExprVector SLoopVars(SCycleDecl->args_begin()+1, SCycleDecl->args_end());
    const ExprVector& SLoopSrcVars = SCycleCHC.srcVars;
    Expr negSGuard;
    ExprVector& invVars = source.invVars[SLoopRel];
    ExprVector& invVarsPrime = source.invVarsPrime[SLoopRel];

    for (int cycleNum = 0; cycleNum < TCyclesSize; cycleNum++) {
      Expr TLoopRel = target.loopheads[cycleNum];
      int cycle = target.cycles[TLoopRel][0][0];
      HornRuleExt& cycleCHC = target.chcs[cycle];

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

      // create non-inductive CHC
      SNonInductiveCHC.srcRelation = SInductiveCHCRel_i_minus_1;
      if (!isOpX<TRUE>(SInductiveCHCRel_i_minus_1)) {
        SNonInductiveCHC.srcVars = SLoopSrcVars;
        SNonInductiveCHC.body = negSGuard;
        SNonInductiveCHC.isFact = false;
      }
      SNonInductiveCHC.dstRelation = SInductiveCHCRel_i;
      SDecomposed.chcs.push_back(SNonInductiveCHC);

      // create inductive CHC
      SInductiveCHC.srcRelation = SInductiveCHC.dstRelation = SInductiveCHCRel_i;
      SInductiveCHCRel_i_minus_1 = SInductiveCHCRel_i;
      SDecomposed.chcs.push_back(SInductiveCHC);

      auto SGuard = SDecomposed.getPrecondition(&SDecomposed.chcs.back());
      negSGuard = mkNeg(replaceAll(SGuard, invVars, invVarsPrime));
    }

    // create query
    auto SQuery = source.getQuery();
    SQuery->srcRelation = SInductiveCHCRel_i_minus_1;
    SDecomposed.chcs.push_back(*SQuery);

    SDecomposed.findCycles();
    // prepare a version of wtoCHCs w/o queries
    SDecomposed.dwtoCHCs = SDecomposed.wtoCHCs;
    for (auto it = SDecomposed.dwtoCHCs.begin(); it != SDecomposed.dwtoCHCs.end();)
      if ((*it)->isQuery) it = SDecomposed.dwtoCHCs.erase(it);
      else ++it;
  }

  void projection(ExtendedCHCs& projRm, int i, ExtendedCHCs &origRm, bool multipleProjections)
  {
    if (!multipleProjections) {
      auto query = projRm.getQuery();
      query->body = mk<TRUE>(origRm.m_efac);
      return;
    }

    auto loopRel = origRm.loopheads[i];
    const HornRuleExt& cycle = origRm.chcs[origRm.cycles[loopRel][0][0]];
    HornRuleExt prefix = origRm.chcs[origRm.prefixes[loopRel][0].back()];
    if (!prefix.isFact) {
      // for all cycles except the first
      prefix.srcRelation = mk<TRUE>(origRm.m_efac);
      prefix.srcVars.clear();
      prefix.isFact = true;
    }
    projRm.chcs.push_back(std::move(prefix));
    projRm.chcs.push_back(std::move(cycle));

    projRm.decls.insert(origRm.getDeclByName(loopRel));
    projRm.invVars[loopRel] = origRm.invVars[loopRel];
    projRm.invVarsPrime[loopRel] = origRm.invVarsPrime[loopRel];

    // create query
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
    // prepare a version of wtoCHCs w/o queries
    projRm.dwtoCHCs = projRm.wtoCHCs;
    for (auto it = projRm.dwtoCHCs.begin(); it != projRm.dwtoCHCs.end();)
      if ((*it)->isQuery) it = projRm.dwtoCHCs.erase(it);
      else ++it;
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
    auto& efac = source.m_efac;
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
          bool refinedTarget = equiv.refine();
          if (!refinedSource && !refinedTarget) return false;
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
