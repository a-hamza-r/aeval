#ifndef EXTENDEDHORN__HPP__
#define EXTENDEDHORN__HPP__

#include "deep/Horn.hpp"
#include <algorithm>
#include <set>
#include <map>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>
#include <functional>
#include "boost/functional/hash_fwd.hpp"
#include <unordered_set>
#include <unordered_map>
#include <memory>
#include <array>

#include "deep/RndLearnerV4.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  struct RecursiveCHC {
    Expr condition;
    pair<Expr, Expr> recursiveEquality;
  };

  static void printRecursiveDefinition(const vector<RecursiveCHC>& recs) {
    for (int i = 0; i < recs.size(); i++) {
      if (i == 0) outs() << "if ";
      else outs() << "else if ";
      outs() << "(" << recs[i].condition << ") ";
      outs() << "then ";
      outs() << "{ " << recs[i].recursiveEquality.first << " = "
        << recs[i].recursiveEquality.second << " }\n";
    }
  }

  class ExtendedCHCs : public CHCs
  {
    vector<RecursiveCHC> recursiveCHCs;
    set<Expr> declsRecursive;

  public:
    ExtendedCHCs(ExprFactory &efac, EZ3 &z3, int d = false) :
      CHCs(efac, z3, d) {};

    bool normalizeRecursiveAndLoop(Expr& r, HornRuleExt& hr, bool& isRecursive)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      // small rewr
      if (isOpX<IMPL>(r) && isOpX<ITE>(r->right()))
      {
        return true;
      }

      if (isOpX<IMPL>(r) && isOpX<IMPL>(r->right()))
      {
        r = mk<IMPL>(mk<AND>(r->left(), r->right()->left()), r->right()->right());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        else if (isOpX<EQ>(r->right()) && !hasUninterp(r->left())) {
          auto left = r->right()->left();
          auto right = r->right()->right();
          if (isFapp(left) || isFapp(right)) {
            if (!isFapp(left)) {
              auto tmp = left;
              left = right;
              right = tmp;
            }
            isRecursive = true;
            return false;
          }
        }
        r = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool parseRecursiveAndLoop(string smt, bool doElim = true, bool doArithm = true)
    {
      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      chcs.reserve(fp.m_rules.size());

      ExprMap eqs;
      for (auto it = fp.m_rules.begin(); it != fp.m_rules.end(); )
      {
        if (isOpX<EQ>(*it))
        {
          eqs[(*it)->left()->left()] = (*it)->right()->left();
          it = fp.m_rules.erase(it);
        }
        else ++it;
      }

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        while (true)
        {
          auto r1 = replaceAll(r, eqs);
          if (r == r1) break;
          else r = r1;
        }

        bool isRecursive = false;
        if (!normalizeRecursiveAndLoop(r, hr, isRecursive))
        {
          chcs.pop_back();
          if (isRecursive) {
            recursiveCHCs.push_back(RecursiveCHC());
            RecursiveCHC& rchc = recursiveCHCs.back();
            rchc.condition = r->left();
            rchc.recursiveEquality = make_pair(r->right()->left(), r->right()->right());
            declsRecursive.insert(r->right()->left()->arg(0));
          }
          continue;
        }

        filter (r, bind::IsConst(), inserter (origVrs, origVrs.begin()));
        // small rewr:
        if (isOpX<ITE>(r->last()))
        {
          hr.body = mk<IMPL>(mk<AND>(r->left(), r->last()->left()),
                             r->last()->right());
          chcs.push_back(chcs.back());
          chcs.back().body = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->last()->left())),
                             r->last()->last());
        }
        else
        {
          hr.body = r;
        }
      }

      for (auto & hr : chcs)
      {
        Expr head = hr.body->right();
        hr.body = hr.body->left();
        if (isOpX<FAPP>(head))
        {
          if (head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), head) !=
               fp.m_queries.end()))
            addFailDecl(head->left()->left());
          else
            addDecl(head->left());
          hr.dstRelation = head->left()->left();
          for (auto it = head->args_begin()+1; it != head->args_end(); ++it)
            hr.dstVars.push_back(*it); // to be rewritten later
        }
        else
        {
          if (!isOpX<FALSE>(head)) hr.body = mk<AND>(hr.body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.dstRelation = mk<FALSE>(m_efac);
        }
        hasBV |= containsOp<BVSORT>(hr.body);
      }

      if (debug > 0) {
        outs() << "Reserved space for " << recursiveCHCs.size()
                          << " recursive CHCs and " << declsRecursive.size() << " declarations\n";
        outs() << "Recursive CHCs:\n";
        printRecursiveDefinition(recursiveCHCs);
        outs() << "\n";
      }
      if (debug > 0) outs () << "Reserved space for " << chcs.size()
                          << " CHCs and " << decls.size() << " declarations\n";

      // the second loop is needed because we want to distinguish
      // uninterpreted functions used as variables
      // from relations to be synthesized
      for (auto it = chcs.begin(); it != chcs.end(); )
      {
        // ExprVector origSrcSymbs, origDstSymbs;
        // ExprSet lin;
        HornRuleExt & hr = *it;
        if (!hr.splitBody())
        {
          it = chcs.erase(it);
          continue;
        }
        else ++it;

        if (hr.srcRelation == NULL) hr.srcRelation = mk<TRUE>(m_efac);

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        if (hr.isQuery) { hasQuery = true; }
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        hr.origDst = hr.dstVars;
        hr.dstVars.clear();

        hr.assignVarsAndRewrite (invVars[hr.srcRelation],
                                 invVarsPrime[hr.dstRelation]);

        if (doElim)
        {
          hr.body = eliminateQuantifiers(conjoin(hr.lin, m_efac), hr.locVars,
                                                 !hasBV && doArithm, false);
          hr.body = u.removeITE(hr.body);
          hr.body = simplifyArr(hr.body);
          hr.shrinkLocVars();
        }
        else
          hr.body = conjoin(hr.lin, m_efac);
      }

      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      findCycles();

      // prepare a version of wtoCHCs w/o queries
      dwtoCHCs = wtoCHCs;
      for (auto it = dwtoCHCs.begin(); it != dwtoCHCs.end();)
        if ((*it)->isQuery) it = dwtoCHCs.erase(it);
          else ++it;

      if (debug >= 1)
      {
        outs () << (doElim ? "  Simplified " : "  Parsed ") << "CHCs:\n";
        print(debug >= 4, true);
      }
      return true;
    }
  };

  void learnInvariants(ExtendedCHCs& ruleManager, unsigned maxAttempts, unsigned to,
       bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
       bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
       bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
       bool dSee, bool ser, int debug)
  {
    if (ruleManager.hasBV)
    {
      outs() << "Bitvectors currently not supported. Try `bnd/expl`.\n";
      return;
    }

    BndExpl bnd(ruleManager, to, debug);
    if (!ruleManager.hasCycles())
      return (void)bnd.exploreTraces(1, ruleManager.chcs.size(), true);

    RndLearnerV4 ds(ruleManager.m_efac, ruleManager.m_z3, ruleManager, to, freqs, aggp, mut, dat,
                    doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
                    dFwd, dRec, dGenerous, debug);

    map<Expr, ExprSet> cands;
    for (auto& cyc : ruleManager.cycles)
    {
      Expr rel = cyc.first;
      for (int i = 0; i < cyc.second.size(); i++)
      {
        assert(rel == ruleManager.chcs[cyc.second[i][0]].srcRelation);
        if (ds.initializedDecl(rel)) continue;
        ds.initializeDecl(rel);
        if (!dSee) continue;

        Expr pref = bnd.compactPrefix(rel, i);
        ExprSet tmp;
        getConj(pref, tmp);
        for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[rel]))
        cands[rel].insert(t);

        if (mut > 0) ds.mutateHeuristicEq(cands[rel], cands[rel], rel, true);
        ds.initializeAux(cands[rel], bnd, rel, i, pref);
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

    if (ds.bootstrap()) return;

    ds.calculateStatistics();
    ds.deferredPriorities();
    std::srand(std::time(0));
    ds.synthesize(maxAttempts);
  }

  inline void parseRecursiveAndLoopDefinitions(string smt, unsigned maxAttempts, unsigned to,
       bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
       bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
       bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
       bool dSee, bool ser, int debug) {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    SMTUtils u(m_efac);

    ExtendedCHCs ruleManager(m_efac, z3, debug - 2);
    auto res = ruleManager.parseRecursiveAndLoop(smt, false, doArithm);
    if (ser)
    {
      ruleManager.serialize();
      return;
    }
    if (!res) return;
    learnInvariants(ruleManager, maxAttempts, to, freqs, aggp, dat, mut, doElim, doArithm,
        doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous,
        dSee, ser, debug);
  }
}

#endif
