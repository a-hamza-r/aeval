#ifndef EXTENDED_HORN__HPP__
#define EXTENDED_HORN__HPP__

#include "deep/Horn.hpp"
#include "deep/BndExpl.hpp"

namespace ufo
{
  template <typename T>
    void concatenateVectors(vector<T> &result, const vector<T>& vec1, const vector<T>& vec2)
    {
      result.reserve(result.size()+vec1.size()+vec2.size());
      result.insert(result.end(), vec1.begin(), vec1.end());
      result.insert(result.end(), vec2.begin(), vec2.end());
    }

  template <typename T>
    void findExpr(Expr, Expr, Expr&, bool = false);

  template <typename T, typename Op>
    static void lookIntoConj(Expr toFind, Expr conj, Expr &result, bool skipArray) {
      for (auto it = conj->args_begin(); it != conj->args_end(); it++)
      {
        Expr res = NULL;
        findExpr<T>(toFind, *it, res, skipArray);
        if (res)
        {
          if (result)
            result = mk<Op>(result, res);
          else
            result = res;
        }
      }
    }

  template <typename T>
    static void findExpr(Expr toFind, Expr conj, Expr &result, bool skipArray)
    {
      if (isOpX<AND>(conj)) lookIntoConj<T, AND>(toFind, conj, result, skipArray);
      else if (isOpX<OR>(conj)) lookIntoConj<T, OR>(toFind, conj, result, skipArray);
      else if (isOpX<T>(conj))
      {
        if (skipArray && containsOp<ARRAY_TY>(conj)) return;
        if (contains(conj, toFind)) result = conj;
      }
    }

  void getConjAndDisj(Expr e, ExprSet& allExprs)
  {
    if (isOpX<AND>(e) || isOpX<OR>(e))
    {
      for (auto it = e->args_begin(); it != e->args_end(); it++)
        getConjAndDisj(*it, allExprs);
    }
    else
      allExprs.insert(e);
  }

  struct Iterator {
    int var;
    bool grows;
    Expr numOfIters;
  };

  struct AlignmentParams {
    int itersOutLoopS;
    int itersOutLoopT;
    int itersInLoopS;
    int itersInLoopT;
  };

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
      Iterator* iter = NULL;
      ExprVector factSrcVars;
      ExprVector queryDstVars;

      ExtendedCHCs(ExprFactory &efac, EZ3 &z3, string n, int d = false) : CHCs(efac, z3, n, d) {}
      ExtendedCHCs(const ExtendedCHCs &oldCHC, bool shallowCopy=false)
        : loopRel(oldCHC.loopRel), CHCs(oldCHC, shallowCopy) {};

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

      Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
      {
        if (!(init && transition && final)) return mkMPZ(-1, m_efac);
        Expr numer = mk<MINUS>(final, init);

        if (add) numer = mk<PLUS>(numer, add);
        Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, m_efac));

        Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, m_efac),
              mkMPZ(1, m_efac)));
        return simplifyArithm(numIters);
      }

      Expr findFinalValue(int i, Expr body, Expr& add, bool iterIncreases)
      {
        Expr iter = invVars[loopRel][i];
        auto &cycle = chcs[cycles[loopRel][0][0]];
        auto precondition = std::move(getPrecondition(&cycle));

        if (!precondition || isOpX<AND>(precondition) || isOpX<OR>(precondition)) {
          // TODO: support more
          return NULL;
        }
        precondition = ineqSimplifier(iter, precondition);

        if (containsOp<LEQ>(precondition)) add = mkMPZ(1, m_efac);
        else if (containsOp<GEQ>(precondition)) add = mkMPZ(-1, m_efac);
        else if (!containsOp<LT>(precondition) && !containsOp<GT>(precondition))
          return NULL;

        Expr limitVal = precondition->arg(1);

        // check if limit value is constant; Eq. 8, section 4
        Expr replacedLimit = replaceAll(limitVal, invVars[loopRel], invVarsPrime[loopRel]);
        bool constLimitValCheck = bool(u.implies(body, mk<EQ>(limitVal, replacedLimit)));

        // check the case that iter does not exceed limit value during transition;
        // Eq. 7, section 4
        bool loopEndCheck = precondition && !u.isSat(mk<AND>(mkNeg(precondition), body));

        if (!constLimitValCheck || !loopEndCheck) return NULL;
        return limitVal;
      }

      Expr findTransitionValue(int i, Expr body)
      {
        Expr a = invVars[loopRel][i];
        Expr b = invVarsPrime[loopRel][i];

        Expr allTransitions = NULL;
        findExpr<EQ>(b, body, allTransitions, true);
        if (!allTransitions) return NULL;

        bool multipleTransVal = false;
        Expr transition = NULL;
        ExprSet allExprsSet;
        getConjAndDisj(allTransitions, allExprsSet);
        for (const auto &it : allExprsSet)
        {
          Expr normalized = ineqSimplifier(b, simplifyArithm(it));
          if (contains(normalized, a) && isOpX<EQ>(normalized)
              && normalized->left() == b)
          {
            if (transition) multipleTransVal = true;
            else transition = normalized;
          }
        }

        // Cases when transition can't be found:
        // multiple transition rels,
        // no transition rel,
        // contains an ITE
        if (multipleTransVal || !transition || transition->right()->arity() <= 1
            || containsOp<ITE>(transition))
          return NULL;

        Expr rightOfTransition = transition->right();

        Expr transitionVal = NULL;
        // assuming no local vars
        if (rightOfTransition->arg(0) == a)
          transitionVal = rightOfTransition->arg(1);
        else
          transitionVal = rightOfTransition->arg(0);

        // check if delta value is constant; Eq. 10, section 4 in paper
        Expr replacedTrans
          = replaceAll(transitionVal, invVars[loopRel], invVarsPrime[loopRel]);
        return u.implies(body, mk<EQ>(transitionVal, replacedTrans))
          ? transitionVal : NULL;
      }

      Expr findInitialValue(int i, Expr init)
      {
        Expr equalities = NULL;
        Expr iter = invVars[loopRel][i];

        findExpr<EQ>(iter, init, equalities, true);
        if (equalities)
        {
          Expr initVal = NULL;
          ExprSet equalitiesSet;
          getConj(equalities, equalitiesSet);
          for (const auto &it : equalitiesSet)
          {
            Expr normalized = ineqSimplifier(iter, simplifyArithm(it));
            if (isOpX<EQ>(normalized) && normalized->left() == iter)
            {
              // if multiple equalities are found, just return; support more
              if (initVal) return NULL;
              else initVal = normalized;
            }
          }
          if (initVal)
          {
            Expr normalized = ineqSimplifier(iter, simplifyArithm(initVal));
            initVal = normalized->right();
            // assigns non-primed variables
            initVal = replaceAll(initVal, invVarsPrime[loopRel], invVars[loopRel]);
            return initVal;
          }
        }
        return NULL;
      }

      bool findIterators()
      {
        BndExpl bnd(*this, debug);
        const HornRuleExt& rule = chcs[cycles[loopRel][0][0]];

        Expr pref = bnd.compactPrefix(loopRel, 0);

        for (auto& i : varsInt)
        {
          Expr a = invVars[loopRel][i];
          Expr b = invVarsPrime[loopRel][i];

          bool isAnIter = false;
          bool iterDecreases = bool(u.implies(rule.body, mk<GT>(a, b)));
          bool iterIncreases = bool(u.implies(rule.body, mk<LT>(a, b)));

          if (iterIncreases || iterDecreases)
          {
            Expr add;
            Expr initVal = findInitialValue(i, pref);
            Expr transitionVal = findTransitionValue(i, rule.body);
            Expr limitVal = findFinalValue(i, rule.body, add, iterIncreases);

            isAnIter = initVal && transitionVal && limitVal;
            if (isAnIter)
            {
              auto numOfIters = numIterations(initVal, transitionVal, limitVal, add);
              iter = new Iterator{i, iterIncreases, numOfIters};
              return true;
            }
          }
        }
        return false;
      }

      void mergeIterationsFact(int unrollFact, HornRuleExt &fact, const vector<int> &cycle,
          BndExpl &bnd, Expr &prefixBody, bool actualAlign, int prefix)
      {
        if (unrollFact > 0) {

          vector<int> traceFactUnroll = {prefix};
          // merge iterations to the fact, given the unrollFact value
          for (int j = 0; j < unrollFact; j++)
            for (int m = 0; m < cycle.size(); m++)
              traceFactUnroll.push_back(cycle[m]);

          ExprVector ssa;
          bnd.getSSA(traceFactUnroll, ssa, varname);

          ssa[unrollFact] = replaceAll(ssa[unrollFact], bnd.bindVars[unrollFact], fact.dstVars);
          prefixBody = conjoin(ssa, m_efac);

          // in case factSrcVars are empty, we needed the factSrcVars as bnd.bindVars[0]
          // in case factSrcVars are not empty, we just replaced the whole fact with some formula,
          // initial variables are then bnd.bindVars[0]
          if (actualAlign)
          {
            for (auto i = 1; i < bnd.bindVars.size()-1; i++)
            {
              fact.locVars.reserve(fact.locVars.size()+bnd.bindVars[i].size());
              fact.locVars.insert(fact.locVars.end(), bnd.bindVars[i].begin(),
                  bnd.bindVars[i].end());
            }
            factSrcVars = bnd.bindVars[0];
          }
        }
      }

      void mergeIterationsLoop(int unrollTrans, HornRuleExt &loop, const vector<int>& cycle,
          BndExpl &bnd, int prefix)
      {
        // unroll the inductive rule unrollTrans times
        if (unrollTrans > 1) {
          // initially adding prefix only to make variable renaming handling easier
          vector<int> traceLoopUnroll = {prefix};
          for (int j = 0; j < unrollTrans-1; j++)
            for (int m = 0; m < cycle.size(); m++)
              traceLoopUnroll.push_back(cycle[m]);

          ExprVector ssa;
          bnd.getSSA(traceLoopUnroll, ssa, varname);
          ssa.erase(ssa.begin());
          ExprSet locVars;
          filter(conjoin(ssa, m_efac), IsConst(), inserter(locVars, locVars.begin()));

          loop.body = replaceAll(loop.body, loop.dstVars, bnd.bindVars[0]);
          ssa[unrollTrans-2] = replaceAll(ssa[unrollTrans-2], bnd.bindVars[unrollTrans-1],
              loop.dstVars);

          loop.body = mk<AND>(loop.body, conjoin(ssa, m_efac));
          loop.locVars.insert(loop.locVars.end(), locVars.begin(), locVars.end());
        }
      }

      void mergeIterationsQuery(int unrollQuery, const vector<int>& cycle, BndExpl &bnd)
      {
        // merge iterations to the query, given the unrollquery value
        if (unrollQuery > 0) {
          vector<int> traceQueryUnroll;
          for (int j = 0; j < unrollQuery; j++)
            for (int m = 0; m < cycle.size(); m++)
              traceQueryUnroll.push_back(cycle[m]);

          ExprVector ssa;
          bnd.getSSA(traceQueryUnroll, ssa, varname);
          auto query = getQuery();
          queryDstVars = bnd.bindVars[bnd.bindVars.size()-1];
          query->body = conjoin(ssa, m_efac);
          for (auto i = 1; i < bnd.bindVars.size()-1; i++)
          {
            query->locVars.reserve(query->locVars.size()+bnd.bindVars[i].size());
            query->locVars.insert(query->locVars.end(), bnd.bindVars[i].begin(),
                bnd.bindVars[i].end());
          }
        }
      }

      void createAlignment(int unrollTrans, int unrollFact, int unrollQuery, BndExpl &bnd,
          Expr &prefixBody, bool actualAlign=true)
      {
        if (actualAlign)
        {
          cout << "Iterations in the loop: " << unrollTrans << "\n";
          cout << "Iterations added to fact: " << unrollFact << "\n";
          cout << "Iterations added to query: " << unrollQuery << "\n";
        }

        vector<int>& cycle = cycles[loopRel][0];
        HornRuleExt& loopRule = chcs[cycle[0]];
        vector<int>& prefix = prefixes[loopRel][0];
        HornRuleExt& prefixRule = chcs[prefix[0]];

        // ************* FACT UNROLLING ***************
        mergeIterationsFact(unrollFact, prefixRule, cycle, bnd, prefixBody, actualAlign,
            prefix[0]);

        // ************* QUERY UNROLLING ***************
        mergeIterationsQuery(unrollQuery, cycle, bnd);

        // ************* LOOP UNROLLING ***************
        mergeIterationsLoop(unrollTrans, loopRule, cycle, bnd, prefix[0]);
      }
  };
}

#endif
