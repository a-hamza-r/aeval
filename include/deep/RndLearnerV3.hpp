#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearnerV2.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    map<int, ExprVector> candidates;
    int updCount = 1;

    map<int, Expr> iterators; // per cycle
    map<int, vector<vector<int>>> iters;  // contains all vars that have a behavior of iterator
    map<int, map<int, bool>> itersGrow;  // whether the iters are increasing or decreasing
    map<int, map<int, cpp_int>> numOfIters;  // contains all vars that have a behavior of iterator
    map<int, vector<vector<int>>> nonIters;  // contains all vars that do not have a behavior of iterator
    map<int, map<int, Expr>> initValsIters;
    map<int, map<int, Expr>> limitValsIters;
    map<int, vector<vector<vector<int>>>> equalityCands;
    map<int, Expr> preconds;
    map<int, Expr> postconds;
    map<int, Expr> ssas;
    map<int, ExprSet> qvars;
    map<int, bool> iterGrows;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, bool freqs, bool aggp) :
      RndLearnerV2 (efac, z3, r, freqs, aggp){}

    bool checkInit(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isFact && hr.dstRelation == rel)
        {
          adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    bool checkInductiveness(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        bool checkedSrc = find(checked.begin(), checked.end(), hr.srcRelation) != checked.end();
        bool checkedDst = find(checked.begin(), checked.end(), hr.dstRelation) != checked.end();
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && checkedDst) ||
            (hr.dstRelation == rel && checkedSrc) ||
            (checkedSrc && checkedDst) ||
            (hr.isFact && checkedDst))
        {
          if (!hr.isQuery) adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      for (auto & v : invarVars[invNum])
        newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
      return newCand;
    }

    Expr eliminateQuantifiers(Expr e, ExprVector& varsRenameFrom, int invNum, bool bwd)
    {
      ExprSet complex;
      if (!containsOp<FORALL>(e))
      {
        e = rewriteSelectStore(e);
        findComplexNumerics(e, complex);
      }
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), *it) != varsRenameFrom.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, varsRenameFrom);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = ufo::eliminateQuantifiers(eTmp, ev3);
      if (bwd) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(/*simplifyArithm*/(eTmp /*, false, true*/));
      e = replaceAll (eTmp, replsRev);

      e = renameCand(e, varsRenameFrom, invNum);
      return e;
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int> tmp;
      ruleManager.getCycleForRel(rel, tmp);
      if (tmp.size() != 1) return; // todo: support

      Expr fls = replaceAll(candToProp->last()->right(),
                            *arrAccessVars[invNum].begin(), iterators[invNum]);
      Expr bdy = rewriteSelectStore(ruleManager.chcs[tmp[0]].body);

      ExprVector ev;
      for (int h = 0; h < ruleManager.chcs[tmp[0]].dstVars.size(); h++)
      {
        Expr var = ruleManager.chcs[tmp[0]].srcVars[h];
        if (iterators[invNum] == var)
          ev.push_back(iterators[invNum]);
        else
          ev.push_back(ruleManager.chcs[tmp[0]].dstVars[h]);
      }

      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(fls, cnjs);
      getConj(bdy, cnjs);
      for (auto & a : cnjs) // hack
      {
        if (isOpX<EQ>(a) && !isNumeric(a->left())) continue;
        newCnjs.insert(a);
      }
      ExprMap mp;
      bdy = replaceSelects(conjoin(newCnjs, m_efac), mp);
      for (auto & a : mp)
      {
        if (!emptyIntersect(a.first, ruleManager.chcs[tmp[0]].dstVars))
        {
          ev.push_back(a.second);
        }
      }

      Expr newCand2;
      cnjs.clear();
      getConj(eliminateQuantifiers(bdy, ev, invNum, false), cnjs);
      for (auto & c : cnjs)
      {
        if (u.isTrue(c) || u.isFalse(c)) continue;
        Expr e = ineqNegReverter(c);
        if (isOp<ComparissonOp>(e))
        {
          for (auto & a : mp) e = replaceAll(e, a.second, a.first);
          if (containsOp<ARRAY_TY>(e) && !emptyIntersect(iterators[invNum], e))
          {
            e = replaceAll(e, iterators[invNum], *arrAccessVars[invNum].begin());
            e = renameCand(e, ruleManager.chcs[tmp[0]].dstVars, invNum);

            // workaround: it works only during bootstrapping now
            arrCands[invNum].insert(e);
          }
        }
      }
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom, ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      Expr formula = mk<AND>(candToProp, constraint);
      if (!containsOp<FORALL>(candToProp) && !u.isSat(formula)) return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      Expr newCand;

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        if (finalizeArrCand(candToProp, constraint, relFrom))
        {
          addPropagatedArrayCands(rel, invNum, candToProp);
          newCand = getForallCnj(eliminateQuantifiers(mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          // GF: temporary workaround:
          // need to support Houdini for arrays, to be able to add newCand and newCand1 at the same time
          Expr newCand1 = replaceArrRangeForIndCheck(invNum, newCand, true);
          auto candsTmp = candidates;
          candidates[invNum].push_back(newCand);
          bool res0 = checkCand(invNum);
          if (!candidates[invNum].empty()) return res0;
          if (newCand1 == NULL) return true;
          candidates = candsTmp;
          candidates[invNum].push_back(newCand1);
          res0 = checkCand(invNum);
          return res0;
        }
        else
        {
          // very ugly at the moment, to be revisited
          newCand = getForallCnj(eliminateQuantifiers(mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          candidates[invNum].push_back(newCand);
          bool res0 = checkCand(invNum);
          return res0;
        }
      }

      ExprSet dsjs;
      getDisj(candToProp, dsjs);
      ExprSet newSeedDsjs;
      for (auto & d : dsjs)
      {
        Expr r = eliminateQuantifiers(mk<AND>(d, constraint), varsRenameFrom, invNum, !fwd);
        newSeedDsjs.insert(r);
      }
      newCand = disjoin(newSeedDsjs, m_efac);

      if (seed)
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(newCand, cnjs);
        for (auto & cnd : cnjs)
        {
          newCnjs.insert(cnd);
          addCandidate(invNum, cnd);
        }

        newCand = conjoin(newCnjs, m_efac);

        if (u.isTrue(newCand)) return true;
        else return propagate(invNum, newCand, true);
      }
      else
      {
        ExprSet cnjs;
        getConj(newCand, cnjs);
        for (auto & a : cnjs) addCandidate(invNum, a);
        return checkCand(invNum);
      }
    }

    bool addCandidate(int invNum, Expr cnd)
    {
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
        {
          auto hr = ruleManager.getFirstRuleOutside(decls[invNum]);
          assert(hr != NULL);

          ExprSet cnjs;
          ExprSet newCnjs;
          Expr it = iterators[invNum];
          if (it != NULL) cnd = replaceArrRangeForIndCheck (invNum, cnd);
        }
        candidates[invNum].push_back(cnd);
        return true;
      }
      if (!isOpX<TRUE>(allLemmas) && u.implies(allLemmas, cnd)) return false;

      for (auto & a : candidates[invNum])
      {
        if (u.isEquiv(a, cnd)) return false;
      }
      candidates[invNum].push_back(cnd);
      return true;
    }

    bool finalizeArrCand(Expr& cand, Expr constraint, Expr relFrom)
    {
      // only forward currently
      if (!isOpX<FORALL>(cand)) return false;
      if (!containsOp<ARRAY_TY>(cand)) return false;

      // need to make sure the candidate is finalized (i.e., not a nested loop)
      int invNum = getVarIndex(relFrom, decls);
      if (u.isSat(postconds[invNum], constraint)) return false;

      cand = replaceAll(cand, cand->last()->left(), conjoin(arrIterRanges[invNum], m_efac));
      return true;
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    Expr replaceArrRangeForIndCheck(int invNum, Expr cand, bool fwd = false)
    {
      assert(isOpX<FORALL>(cand));
      Expr itRepl = iterators[invNum];
      Expr post = postconds[invNum];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(cand->last()->left(), cnjs);

      // TODO: support the case when there are two or more quantified vars

      Expr it = bind::fapp(cand->arg(0));
      ExprSet extr;
      if      (iterGrows[invNum] && fwd)   extr.insert(mk<GEQ>(it, itRepl));
      else if (iterGrows[invNum] && !fwd)   extr.insert(mk<LT>(it, itRepl));
      else if (!iterGrows[invNum] && fwd)  extr.insert(mk<LEQ>(it, itRepl));
      else if (!iterGrows[invNum] && !fwd)  extr.insert(mk<GT>(it, itRepl));

      extr.insert(cand->last()->left());
      return replaceAll(cand, cand->last()->left(), conjoin(extr, m_efac));
    }

    bool propagate(int invNum, Expr cand, bool seed)
    {
      bool res = true;
      Expr rel = decls[invNum];
      checked.insert(rel);
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.srcRelation == hr.dstRelation || hr.isQuery) continue;

        SamplFactory* sf1;
        SamplFactory* sf2;

        // adding lemmas to the body. GF: disabled because something is wrong with them and arrays
        Expr constraint = hr.body;
        sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
//        Expr lm2 = sf2->getAllLemmas();
//        for (auto & v : invarVars[getVarIndex(hr.dstRelation, decls)])
//          lm2 = replaceAll(lm2, v.second, hr.dstVars[v.first]);
//        constraint = mk<AND>(constraint, lm2);

        if (!hr.isFact)
        {
          sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
//          constraint = mk<AND>(constraint, sf1->getAllLemmas());
        }

        // forward:
        if (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) == checked.end())
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf1->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.srcVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.dstVars, hr.dstRelation, seed, true);
        }

        // backward (very similarly):
        if (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) == checked.end() && !hr.isFact)
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf2->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.dstVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.srcVars, hr.srcRelation, seed, false);
        }
      }
      return res;
    }

    bool checkCand(int invNum)
    {
      Expr rel = decls[invNum];
      if (!checkInit(rel)) return false;
      if (!checkInductiveness(rel)) return false;

      return propagate(invNum, conjoin(candidates[invNum], m_efac), false);
    }

    // a simple method to generate properties of a larger Array range, given already proven ranges
    void generalizeArrInvars (SamplFactory& sf)
    {
      if (sf.learnedExprs.size() > 1)
      {
        ExprVector posts;
        ExprVector pres;
        map<Expr, ExprVector> tmp;
        ExprVector tmpVars;
        ExprVector arrVars;
        Expr tmpIt = bind::intConst(mkTerm<string> ("_tmp_it", m_efac));

        for (auto & a : sf.learnedExprs)
        {
          if (!isOpX<FORALL>(a)) continue;
          Expr learnedQF = a->last();
          if (!isOpX<IMPL>(learnedQF)) continue;
          ExprVector se;
          filter (learnedQF->last(), bind::IsSelect (), inserter(se, se.begin()));

          // filter out accesses via non-quantified indeces
          for (auto it = se.begin(); it != se.end();)
          {
            bool found = false;
            for (int i = 0; i < a->arity(); i++)
            {
              if (contains(se[0]->right(), a->arg(0)))
              {
                found = true;
                break;
              }
            }
            if (!found) it = se.erase(it);
            else ++it;
          }

          bool multipleIndex = false;
          for (auto & s : se) {
            if (se[0]->right() != s->right()) {
              multipleIndex = true;
              break;
            }
          }

          if (se.size() == 0 || multipleIndex) continue;

          if (arrVars.size() == 0) {
            for (int index = 0; index < se.size(); index++) {
              arrVars.push_back(se[index]->left());
              tmpVars.push_back(bind::intConst(mkTerm<string> ("_tmp_var_" + lexical_cast<string>(index), m_efac)));
            }
          } else {
            bool toContinue = false;
            for (auto & s : se) {
              if (find(arrVars.begin(), arrVars.end(), s->left()) == arrVars.end()) {
                toContinue = true;
                break;
              }
            }
            if (toContinue) continue;
          }

          Expr postReplaced = learnedQF->right();
          for (int index = 0; index < se.size() && index < tmpVars.size(); index++)
          postReplaced = replaceAll(postReplaced, se[index], tmpVars[index]);

          ExprSet postVars;
          filter(postReplaced, bind::IsConst(), inserter(postVars, postVars.begin()));
          for (auto & fhVar : sf.lf.getVars()) postVars.erase(fhVar);
          for (auto & tmpVar : tmpVars) postVars.erase(tmpVar);
          if (postVars.size() > 0)
          {
            AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(postReplaced, mk<EQ>(tmpIt, se[0]->right())), postVars);
            if (ae.solve())
            {
              Expr pr = ae.getValidSubset();
              ExprSet conjs;
              getConj(pr, conjs);
              if (conjs.size() > 1)
              {
                for (auto conjItr = conjs.begin(); conjItr != conjs.end();)
                {
                  ExprVector conjVars;
                  filter (*conjItr, bind::IsConst(), inserter(conjVars, conjVars.begin()));
                  bool found = false;
                  for (auto & conjVar : conjVars)
                  {
                    if (find (tmpVars.begin(), tmpVars.end(), conjVar) != tmpVars.end())
                    {
                      found = true;
                      break;
                    }
                  }
                  if (!found) conjItr = conjs.erase(conjItr);
                  else ++conjItr;
                }
              }
              postReplaced = conjoin(conjs, m_efac);
            }
          }

          pres.push_back(learnedQF->left());
          posts.push_back(postReplaced);
          tmp[mk<AND>(learnedQF->left(), postReplaced)].push_back(se[0]->right());
        }

        if (tmp.size() > 0)
        {
          for (auto & a : tmp)
          {
            if (a.second.size() > 1)
            {
              Expr disjIts = mk<FALSE>(m_efac);
              for (auto & b : a.second) disjIts = mk<OR>(disjIts, mk<EQ>(tmpIt, b));
              ExprSet elementaryIts;
              filter (disjIts, bind::IsConst (), inserter(elementaryIts, elementaryIts.begin()));
              for (auto & a : sf.lf.getVars()) elementaryIts.erase(a);
              elementaryIts.erase(tmpIt);
              if (elementaryIts.size() == 1)
              {
                AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(disjIts, a.first->left()), elementaryIts);
                if (ae.solve())
                {
                  ExprVector args;
                  Expr it = *elementaryIts.begin();
                  args.push_back(it->left());
                  Expr newPre = replaceAll(ae.getValidSubset(), tmpIt, it);
                  Expr newPost = replaceAll(a.first->right(), tmpIt, it);
                  for (int index = 0; index < tmpVars.size() && index < arrVars.size(); index++)
                  newPost = replaceAll(newPost, tmpVars[index], mk<SELECT>(arrVars[index], it));
                  args.push_back(mk<IMPL>(newPre, newPost));
                  Expr newCand = mknary<FORALL>(args);
                  sf.learnedExprs.insert(newCand);
                }
              }
            }
          }
        }
      }
    }

    void assignPrioritiesForLearned()
    {
//      bool progress = true;
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          ExprVector invVars;
          for (auto & a : invarVars[cand.first]) invVars.push_back(a.second);
          SamplFactory& sf = sfs[cand.first].back();
          for (auto b : cand.second)
          {
            b = simplifyArithm(b);
            if (containsOp<ARRAY_TY>(b) || findNonlin(b))
            {
              sf.learnedExprs.insert(b);
            }
            else
            {
              Expr learnedCand = normalizeDisj(b, invVars);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                sf.learnedExprs.insert(learnedCand);
            }
//            else progress = false;
          }
        }
      }
//            if (progress) updateGrammars(); // GF: doesn't work great :(
    }

    bool synthesize(int maxAttempts, char * outfile)
    {
      ExprSet cands;
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        int tmp = ruleManager.cycles[i % ruleManager.cycles.size()][0];
        int invNum = getVarIndex(ruleManager.chcs[tmp].srcRelation, decls);
        checked.clear();
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand = sf.getFreshCandidate(i < 25); // try simple array candidates first
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog)
          outs () << " - - - sampled cand (#" << i << ") for " << *decls[invNum] << ": " << *cand << "\n";

        if (!addCandidate(invNum, cand)) continue;
        if (checkCand(invNum))
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations\n";
            printSolution();
            return true;
          }
        }
      }
      outs() << "unknown\n";
      return false;
    }

    bool splitUnsatSets(ExprVector & src, ExprVector & dst1, ExprVector & dst2)
    {
      if (u.isSat(src)) return false;

      for (auto & a : src) dst1.push_back(a);

      for (auto it = dst1.begin(); it != dst1.end(); )
      {
        dst2.push_back(*it);
        it = dst1.erase(it);
        if (u.isSat(dst1)) break;
      }

      // now dst1 is SAT, try to get more things from dst2 back to dst1

      for (auto it = dst2.begin(); it != dst2.end(); )
      {
        if (!u.isSat(conjoin(dst1, m_efac), *it)) { ++it; continue; }
        dst1.push_back(*it);
        it = dst2.erase(it);
      }

      return true;
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          for (auto & hr : ruleManager.chcs)
          {
            if (hr.dstRelation == decls[i]) worklist.push_back(&hr);
          }
        }
      }

      // basically, just checks initiation and immediately removes bad candidates
      multiHoudini(worklist, false);

      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          splitUnsatSets(candidates[i], tmp, stub);
          candidates[i] = tmp;
        }
      }

      return true;
    }

    bool isSkippable(Expr model, ExprVector vars, map<int, ExprVector>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
      {
        for (auto & b : a.second)
        {
          if (containsOp<FORALL>(b)) return true;
        }
      }
      return false;
    }


    // AH: make this function efficient, works so far
    int findPattern(vector<int> array)
    {
      for (int i = 1; i <= array.size()/2; i++)
      {
        bool found = true;
        for (int j = i; j < array.size(); j += i)
        {
          for (int k = 0; k < i, j+k < array.size(); k++)
          {
            if (array[k] != array[j+k]) 
            {
              found = false;
              break;
            }
          }
          if (!found) break;
        }
        if (found) return i;
      }
      return -1;
    }

    bool varsRelated(Expr a, Expr b, ExprSet& relations)
    {
      ExprSet varsConsidered1, varsConsidered2, vars;
      varsConsidered1.insert(a); varsConsidered2.insert(b);

      int vars1Size = 0, vars2Size = 0;
      // keep adding vars to the list if any variable is added to any of the sets in previous loop
      while (vars1Size != varsConsidered1.size() || vars2Size != varsConsidered2.size())
      { 
        vars1Size = varsConsidered1.size(); vars2Size = varsConsidered2.size();
        for (auto it : varsConsidered1)
        {
          for (auto it2 : relations)
          {
            if (contains(it2, it))
            {
              filter (it2, bind::IsConst (), inserter(vars, vars.begin()));
            }
          }
        }
        varsConsidered1.insert(vars.begin(), vars.end());

        for (auto it : varsConsidered2)
        {
          for (auto it2 : relations)
          {
            if (contains(it2, it))
            {
              filter (it2, bind::IsConst (), inserter(vars, vars.begin()));
            }
          }
        }
        varsConsidered2.insert(vars.begin(), vars.end());

        // at any point, if both sets have similar Exprs, we are done
        vector<Expr> inters;
        set_intersection(varsConsidered1.begin(), varsConsidered1.end(), 
          varsConsidered2.begin(), varsConsidered2.end(), std::back_inserter(inters));

        if (!inters.empty()) return true;
      }
      return false;
    }

    template <typename O> 
    void getTypeVars(HornRuleExt &CHC, vector<int> &chc1Vars, vector<int> &chc2Vars, int rel1DeclSize)
    {
      for (int i = 0; i < CHC.dstVars.size(); i++)
      {
        Expr result;
        if (isOpX<O>(bind::typeOf(CHC.dstVars[i])))
        {
          // use u.hasOneModel() instead of finding the equality
          findExpr<EQ>(CHC.dstVars[i], CHC.body, result);
          if (!result)
          {
            if (i < rel1DeclSize) chc1Vars.push_back(i);
            else chc2Vars.push_back(i);
          }
        }
      }
    }

    void combinations(vector<int> &vars1, vector<int> &vars2, vector<vector<int>> c, vector<int> vars2Used, vector<vector<vector<int>>> &combs, int pos)
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
          c.push_back(vector<int>{vars1[pos], vars2[i]});
          combinations(vars1, vars2, c, vars2Used, combs, pos+1);
          c.pop_back();
          vars2Used.pop_back();
        }
      } 
    }


    // works if sizes of vars1 and vars2 are equal
    void combinationsOfVars(vector<int> &vars1, vector<int> &vars2, vector<vector<vector<int>>> &combs)
    {
      for (int i = 0; i < vars2.size(); i++)
      {
        vector<int> vars2Used{i};
        vector<int> v{vars1[0], vars2[i]};
        vector<vector<int>> c{v};
        combinations(vars1, vars2, c, vars2Used, combs, 1);
      }
    }

    void joinVars(vector<vector<vector<int>>> &vec1, vector<vector<vector<int>>> &vec2, 
      vector<vector<vector<int>>> &combs)
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
            vector<vector<int>> v;
            concatenateVectors(v, it, it2);
            combs.push_back(v);
          }
        }
      }
    }


    int alignment(const vector<string> & behaviorfiles, BndExpl& bnd)
    {
      vector<bool> equivalentLoops;

      int fileIndex = 0;
      for (int i = 0; i < ruleManager.cycles.size(); i++)
      {
        vector<vector<int>> iterPairs;
        vector<vector<int>> nonIterPairs;
        vector<int> &cycle = ruleManager.cycles[i];
        HornRuleExt &rule = ruleManager.chcs[cycle[0]];
        vector<int> &prefix = ruleManager.prefixes[i];
        HornRuleExt &prefixRule = ruleManager.chcs[prefix[0]];
        Expr rel = rule.srcRelation;
        int invNum = getVarIndex(rel, decls);

        vector<vector<int>> itersForInv = iters[invNum];
        vector<vector<int>> nonItersForInv = nonIters[invNum];

        // matching all iters of one CHC system to all iters of other one
          // could be a better way to match lesser iters
        for (int j = 0; j < itersForInv[0].size(); j++)
        {
          for (int k = 0; k < itersForInv[1].size(); k++)
          {
            vector<int> v{itersForInv[0][j], itersForInv[1][k]};
            iterPairs.push_back(v);
          }
        }

        for (auto &comb : equalityCands[i])
        {
          Expr ruleBodyBackup = prefixRule.body;
          Expr pre, post;

          if (comb[0][0] != -1)
          {
            for (auto &pair : comb)
            {
              // errs() << "pair: " << pair[0] << " " << pair[1] << "\n";
              if (!pre) pre = mk<EQ>(rule.dstVars[pair[0]], rule.dstVars[pair[1]]);
              else pre = mk<AND>(pre, mk<EQ>(rule.dstVars[pair[0]], rule.dstVars[pair[1]]));
            }

            prefixRule.body = mk<AND>(prefixRule.body, pre);
          }
          else pre = mk<TRUE>(m_efac);

          errs() << "prefixRule: " << *prefixRule.body << "\n";

          HornRuleExt* query = NULL;
          for (auto num: ruleManager.outgs[rel])
            if (ruleManager.chcs[num].isQuery) 
              query = &ruleManager.chcs[num];

          // matching all non-iters of one CHC system to all non-iters of other one
          // could be a better way to match lesser non-iters
          bool found = false;
          for (int j = 0; j < nonItersForInv[0].size(); j++)
          {
            for (int k = 0; k < nonItersForInv[1].size(); k++)
            {
              // not tested
              for (auto a : comb)
              {
                if (nonItersForInv[0][j] == a[0] || nonItersForInv[1][k] == a[1])
                {
                  found = true; break;
                }
              }
              vector<int> v{nonItersForInv[0][j], nonItersForInv[1][k]};
              // either we found the whole pair in the comb, or we found none of the elems of the pair
              if (find(comb.begin(), comb.end(), v) != comb.end() || !found)
                nonIterPairs.push_back(v);
            }
          }

          // running the data matrix initially
          map<Expr, ExprSet> candsFromCurrentMatrix;
          arma::mat dataMatrix;
          #ifdef HAVE_ARMADILLO
            getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix);
          #else
            outs() << "Skipping learning from data as required library (armadillo) not found\n";
          #endif

          Expr candsFromCurrentMatrixCnj = conjoin(candsFromCurrentMatrix[rel], m_efac);
          candsFromCurrentMatrixCnj = simplifyArithm(candsFromCurrentMatrixCnj);

          for (auto it = iterPairs.begin(); it != iterPairs.end(); it++)
          {
            int indx1 = (*it)[0], indx2 = (*it)[1];
            Expr iter1 = rule.srcVars[indx1], iter2 = rule.srcVars[indx2];
            errs() << "\n\nassuming iters: " << *iter1 << " and " << *iter2 << "\n";
            cpp_int numIters1 = numOfIters[invNum][indx1];
            cpp_int numIters2 = numOfIters[invNum][indx2];
            cout << "numIters: " << numIters1 << " and " << numIters2 << "\n";

            ExprSet cands;
            vector<vector<int>> aligningCandidates;

            Expr candsAddToQuery;
            int indsQuery = 0;
            // alignment candidates are all variables that are non-iters
            for (auto& it2 : nonIterPairs)
            {
              Expr cand1, cand2, queryVar, initCond, finalCond;
              Expr select1, select2, selectsNotEq, toAddToQuery;
              aligningCandidates.push_back(it2);
              if (isConst<ARRAY_TY>(rule.srcVars[it2[0]]))
              {
                if (!ruleManager.arrayStores[i][it2[0]].empty())
                  cand1 = ruleManager.arrayStores[i][it2[0]].back();
                else 
                  cand1 = ruleManager.arraySelects[i][it2[0]].back();
                if (!ruleManager.arrayStores[i][it2[1]].empty())
                  cand2 = ruleManager.arrayStores[i][it2[1]].back();
                else 
                  cand2 = ruleManager.arraySelects[i][it2[1]].back();
                cands.insert(mk<EQ>(mk<SELECT>(rule.srcVars[it2[0]], cand1), mk<SELECT>(rule.srcVars[it2[1]], cand2)));
                if (query)
                {
                  queryVar = mkTerm<string>("i"+lexical_cast<string>(indsQuery), m_efac);
                  queryVar = cloneVar(rule.srcVars[indx1], queryVar);

                  initCond = mk<GEQ>(queryVar, initValsIters[i][indx1]);
                  finalCond = mk<LT>(queryVar, limitValsIters[i][indx1]);

                  select1 = mk<SELECT>(rule.srcVars[it2[0]], queryVar);
                  select2 = mk<SELECT>(rule.srcVars[it2[1]], queryVar);

                  selectsNotEq = mk<NEQ>(select1, select2);

                  toAddToQuery = mk<AND>(mk<AND>(initCond, finalCond), selectsNotEq);

                  indsQuery++;
                }
              }
              else
              {
                cands.insert(mk<EQ>(rule.srcVars[it2[0]], rule.srcVars[it2[1]]));
                if (query)
                  toAddToQuery = mk<NEQ>(rule.srcVars[it2[0]], rule.srcVars[it2[1]]);
              }
              if (candsAddToQuery) candsAddToQuery = mk<OR>(candsAddToQuery, toAddToQuery);
              else candsAddToQuery = toAddToQuery;
            }

            if (query) errs() << "candsAddToQuery: " << *candsAddToQuery << "\n";
            Expr queryBodyBackUp = query->body;
            query->body = mk<AND>(query->body, candsAddToQuery);

            // query->printMemberVars();

            // errs() << "cands: " << *conjoin(cands, m_efac) << "\n";

            // check if number of iters for iters pair is same, 
            // if so, see whether we can find a relation between each of the alignment candidates pair
            // if we find relation between each candidate, we assume the loops are equivalent
            // possibly, find a relation between current iters pair too? 
            bool foundRelation = true;
            if (numIters1 == numIters2 && numIters1 != 0)
            {
              for (auto& it2 : aligningCandidates)
              {
                foundRelation = varsRelated(rule.srcVars[it2[0]], rule.srcVars[it2[1]], candsFromCurrentMatrix[rel]);
                if (!foundRelation) break;
              }
              if (foundRelation)
              {
                equivalentLoops.push_back(true);
                errs() << "We have found the loop is equivalent: " << *rel << "\n";
              }
            }

            if (equivalentLoops.size() == ruleManager.cycles.size() && query != NULL) 
            {
              // query->body = mk<AND>(query->body, mkNeg(candsFromCurrentMatrixCnj));
              errs() << "query body: " << *query->body << "\n";
              return 1;
            }
            
            Expr currentHrBody = rule.body;

            bool firstMatrix = true;

            while (true)
            {
              errs() << "cands to be aligned: " << *conjoin(cands, m_efac) << "\n";

              HornRuleExt& hr = rule;

              Expr model;
              Expr currentMatrix = mk<AND>(candsFromCurrentMatrixCnj, mkNeg(conjoin(cands, m_efac)));

              // Expr check = mk<AND>(mk<AND>(hr.body, eq), mkNeg(conjoin(cands, m_efac)));

              errs() << "currentHrBody is: " << *currentHrBody << "\n";

              // current dataMatrix does not imply equality
              if (u.isSat(currentMatrix))
              {
                errs() << "current matrix\n";
                model = bnd.compactPrefix(i);
                model = replaceAll(model, hr.srcVars, hr.dstVars);
              }
              // check if at any point, the cands (equalities) do not hold
              else if (!checkCHC1(hr, mk<AND>(mk<AND>(candsFromCurrentMatrixCnj, pre), currentHrBody), cands))
              {
                // Expr e, invAndCond;
                firstMatrix = false;
                model = u.getModel(hr.srcVars);
                errs() << "\nmodel src: " << *model << "\n\n";
                // model = u.getModel(hr.dstVars);
                // errs() << "\nmodel: " << *model << "\n\n";


                // if (itersGrow[invNum][indx1])
                // {
                  // findExpr<EQ>(iter1, model, e);
                  // invAndCond = mk<AND>(invariantCnj, mk<LT>(iter1, e->right()));
                  // e = NULL;
                 
                  // findExpr<EQ>(iter2, model, e);
                  // if (itersGrow[invNum][indx2])
                    // invAndCond = mk<AND>(invAndCond, mk<LT>(iter2, e->right()));
                  // else if (!itersGrow[invNum][indx2])
                  //   invAndCond = mk<AND>(invAndCond, mk<GT>(iter2, e->right()));

                  // errs() << "inv: " << *invAndCond << "\n";
                  // if (!checkCHC1(hr, invAndCond, cands))
                  // {
                  //   errs() << "something is wrong\n";
                  //   return -1;
                  // }
                // }

                // else if (!itersGrow[invNum][indx1])
                // {
                  // findExpr<EQ>(iter1, model, e);
                  // invAndCond = mk<AND>(invariantCnj, mk<GT>(iter1, e->right()));
                  // e = NULL;

                  // findExpr<EQ>(iter2, model, e);
                  // if (itersGrow[invNum][indx2])
                  //   invAndCond = mk<AND>(invAndCond, mk<LT>(iter2, e->right()));
                  // else if (!itersGrow[invNum][indx2])
                  //   invAndCond = mk<AND>(invAndCond, mk<GT>(iter2, e->right()));
                  
                  // errs() << "inv: " << *invAndCond << "\n";
                  // if (!checkCHC1(hr, invAndCond, cands))
                  // {
                  //   errs() << "something is wrong\n";
                  //   return -1;
                  // }
                // }

                model = replaceAll(model, hr.srcVars, hr.dstVars);
                candsFromCurrentMatrix.clear();
                #ifdef HAVE_ARMADILLO
                  getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix, model);
                #else
                  outs() << "Skipping learning from data as required library (armadillo) not found\n";
                #endif
                candsFromCurrentMatrixCnj = conjoin(candsFromCurrentMatrix[rel], m_efac);
              }
              else
              {
                equivalentLoops.push_back(true);
                firstMatrix = false;
                errs() << "It is done\n";
                // prefixRule.printMemberVars();
                // worklist[0]->printMemberVars();
                // query->printMemberVars();
                // bootstrap();

                if (equivalentLoops.size() == ruleManager.cycles.size() && query != NULL) 
                {
                  // query->body = mk<AND>(query->body, mkNeg(candsFromCurrentMatrixCnj));
                  errs() << "query body: " << *query->body << "\n";

                  return 2;
                }
                else continue;
              }


              Expr conjoined = conjoin(candsFromCurrentMatrix[rel], m_efac);
              candsFromCurrentMatrixCnj = simplifyArithm(candsFromCurrentMatrixCnj);
              errs() << "\ncands for current data matrix: \n" << *candsFromCurrentMatrixCnj << "\n";
              int numItersOfLoop1 = 0, numItersOfLoop2 = 0;

              // make sure it comes here and is the right condition
              if (numIters1 != numIters2 && numIters1 != 0 && numIters2 != 0 
                && (numIters2 % numIters1 == 0 || numIters1 % numIters2 == 0))
              {
                if (numIters1 % numIters2 == 0)
                {
                  cpp_int numIters1Div = numIters1 / numIters2;
                  if (numIters1 < 0 && numIters2 < 0)
                  {
                    numItersOfLoop1 = 1; 
                    numItersOfLoop2 = (int)(numIters1Div);
                  }
                  else if (numIters1 > 0 && numIters2 > 0)
                  {
                    numItersOfLoop1 = (int)numIters1Div; 
                    numItersOfLoop2 = 1;
                  }
                }
                else if (numIters2 % numIters1 == 0)
                {
                  cpp_int numIters2Div = numIters2 / numIters1;
                  if (numIters1 < 0 && numIters2 < 0)
                  {
                    numItersOfLoop1 = (int)(numIters2Div); 
                    numItersOfLoop2 = 1;
                  }
                  else if (numIters1 > 0 && numIters2 > 0)
                  {
                    numItersOfLoop1 = 1; 
                    numItersOfLoop2 = (int)numIters2Div;
                  }
                }
              }
              else if (numIters1 != numIters2 && numIters1 != 0 && numIters2 != 0)
              {
                // current assumption: 
                  // align just any of the aligning candidates, the rest should align if the program is equivalent
                // going with the first candidate
                vector<int> checking = aligningCandidates[0];

                auto ind1 = checking[0];
                auto ind2 = checking[1];

                errs() << "indices are: " << ind1 << " and " << ind2 << "\n";

                int j, k;
                bool found = false;
                // find the first point of equivalency
                for (k = 0; k < dataMatrix.n_rows; k++)
                {
                  for (j = 0; j < dataMatrix.n_rows; j++)
                  {
                    if (dataMatrix(j, ind1+1) == dataMatrix(k, ind2+1)) 
                    {
                      errs() << "matching at: " << dataMatrix(j, ind1+1) << " and " << dataMatrix(k, ind2+1) << "\n";
                      found = true;
                      break;
                    } 
                  }
                  if (found) break;
                }

                vector<int> matchesInd1, matchesInd2;
                int currentMatch1 = j, currentMatch2 = k;
                // assumes that the variables are only aligned in increasing direction
                // relax this assumption later, 
                // we should be able to check if candidates are aligned in opposite directions
                if (found)
                {
                  for (int a = j+1; a < dataMatrix.n_rows; a++)
                  {
                    for (int b = k+1; b < dataMatrix.n_rows; b++)
                    {
                      if (dataMatrix(a, ind1+1) == dataMatrix(b, ind2+1)) 
                      {
                        matchesInd1.push_back(a - currentMatch1);
                        matchesInd2.push_back(b - currentMatch2);
                        currentMatch1 = a; currentMatch2 = b;
                      }
                    }
                  }
                }
                // else 
                // {
                //   Expr newModel = mk<TRUE>(m_efac);
                //   for (int i = 1; i < dataMatrix.n_cols; i++)
                //   {
                //     newModel = mk<AND>(newModel, mk<EQ>(hr.srcVars[i-1], mkMPZ(dataMatrix(dataMatrix.n_rows-1, i), m_efac)));
                //   }

                //   getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix, newModel);
                // }

                errs() << "matches 1: \n";
                for (auto it : matchesInd1) errs() << it << " ";
                errs() << "\n";
                errs() << "matches 2: \n";
                for (auto it : matchesInd2) errs() << it << " ";
                errs() << "\n";

                int alignPattern1 = findPattern(matchesInd1);
                int alignPattern2 = findPattern(matchesInd2);

                if (alignPattern1 > 0 && alignPattern2 > 0)
                {
                  // cout << "first alignment at: " << alignPattern1 << "\n";
                  // cout << "second alignment at: " << alignPattern2 << "\n";

                  if (alignPattern1 % alignPattern2 == 0)
                  {
                    for (int a = 0; a < alignPattern1; a++) 
                    {
                      numItersOfLoop1 += matchesInd1[a];
                      numItersOfLoop2 += matchesInd2[a];
                    }
                  }
                  else if (alignPattern2 % alignPattern1 == 0)
                  {
                    for (int a = 0; a < alignPattern2; a++) 
                    {
                      numItersOfLoop1 += matchesInd1[a];
                      numItersOfLoop2 += matchesInd2[a];
                    }
                  }
                  else errs() << "alignment could not be found\n";
                }
                else {}
              }

              cout << "numIters for loop 1: " << numItersOfLoop1 << "\n";
              cout << "numIters for loop 2: " << numItersOfLoop2 << "\n";

              ExprVector subRelations = ruleManager.productRelsToSrcDst[rel];
              int chc1, chc2;
              for (auto it2 : ruleManager.chcSrc->outgs[subRelations[0]])
                if (ruleManager.chcSrc->chcs[it2].dstRelation == subRelations[0]) 
                {
                  chc1 = it2;
                  break;
                }
              for (auto it2 : ruleManager.chcDst->outgs[subRelations[1]])
                if (ruleManager.chcDst->chcs[it2].dstRelation == subRelations[1]) 
                {
                  chc2 = it2;
                  break;
                }

              auto& rules1 = ruleManager.chcSrc->chcs[chc1];
              auto& rules2 = ruleManager.chcDst->chcs[chc2];
              
              ExprSet vars(rules1.locVars.begin(), rules1.locVars.end());
              Expr rules1BodyQE = ufo::eliminateQuantifiers(rules1.body, vars);

              ExprSet vars1(rules2.locVars.begin(), rules2.locVars.end());
              Expr rules2BodyQE = ufo::eliminateQuantifiers(rules2.body, vars1);

              auto rulesBody = hr.body;
              ExprSet extraVars;

              Expr var, var1, new_name;
              Expr rules1Body, rules2Body;

              for (int l = 1; l < numItersOfLoop1; l++)
              {
                rules1Body = rules1BodyQE;
                for (int v = 0; v < rules1.srcVars.size(); v++)
                {
                  // every time, introduce a new variable and replace dstVars of rulesPr with new variable var
                  // replace rules1 srcVars with the new var and dstVars with current dstVars of rulesPr (before updating)
                  // and add the rules1 body to rulesPr body
                  new_name = mkTerm<string>("_pr_"+lexical_cast<string>(v)+"_"+lexical_cast<string>(l), m_efac);
                  var = cloneVar(rules1.srcVars[v], new_name);
                  var1 = hr.dstVars[v];
                  
                  rules1Body = replaceAll(rules1Body, rules1.srcVars[v], var);
                  rules1Body = replaceAll(rules1Body, rules1.dstVars[v], var1);

                  rulesBody = replaceAll(rulesBody, hr.dstVars[v], var);

                  extraVars.insert(var);
                }
                rulesBody = mk<AND>(rulesBody, rules1Body);
              }

              int rules1DeclSize = rules1.srcVars.size();

              for (int l = 1; l < numItersOfLoop2; l++)
              {
                rules2Body = rules2BodyQE;
                for (int v = 0; v < rules2.srcVars.size(); v++)
                {
                  // same logic as rules1 above, except the location of 
                  // corresponding variables in rulesPr srcVars and dstVars
                  new_name = mkTerm<string>("_pr_"+lexical_cast<string>(rules1DeclSize+v)+"_"+lexical_cast<string>(l), m_efac);
                  var = cloneVar(rules2.srcVars[v], new_name);
                  var1 = hr.dstVars[rules1DeclSize+v];
                  
                  rules2Body = replaceAll(rules2Body, rules2.srcVars[v], var);
                  rules2Body = replaceAll(rules2Body, rules2.dstVars[v], var1);

                  rulesBody = replaceAll(rulesBody, hr.dstVars[rules1DeclSize+v], var);

                  extraVars.insert(var);
                }
                rulesBody = mk<AND>(rulesBody, rules2Body);
              }

              rulesBody = ufo::eliminateQuantifiers(rulesBody, extraVars);

              // errs() << "\nnewly created body: " << *rulesBody << "\n";

              // if (itersGrow[invNum][iter1]) errs() << *iter1 << " grows\n";
              // if (itersGrow[invNum][iter2]) errs() << *iter2 << " grows\n";

              Expr res1, res2, cond, condPrev;
              Expr modelRepl = replaceAll(model, hr.dstVars, hr.srcVars);
              // errs() << "model: " << *modelRepl << "\n";

              findExpr<EQ>(iter1, modelRepl, res1);
              findExpr<EQ>(iter2, modelRepl, res2);

              res1 = ineqSimplifier(iter1, res1);
              res2 = ineqSimplifier(iter2, res2);

              if (itersGrow[invNum][indx1]) 
              {
                cond = mk<GEQ>(iter1, res1->right());
                condPrev = mk<LT>(iter1, res1->right());
              }
              else 
              {
                cond = mk<LEQ>(iter1, res1->right());
                condPrev = mk<GT>(iter1, res1->right());
              }
              if (itersGrow[invNum][indx2]) 
              {
                cond = mk<AND>(cond, mk<GEQ>(iter2, res2->right()));
                condPrev = mk<AND>(condPrev, mk<LT>(iter2, res2->right()));
              }
              else 
              {
                cond = mk<AND>(cond, mk<LEQ>(iter2, res2->right()));
                condPrev = mk<AND>(condPrev, mk<GT>(iter2, res2->right()));
              }

              // the cond is appended to the new rule rulesPr
              errs() << "\ncond is: " << *cond << "\n";

              currentHrBody = mk<AND>(rulesBody, cond);

              // possibly, the current rule we are handling, add !cond to the body
              errs() << "\ncond prev is: " << *condPrev << "\n";

              if (firstMatrix)
                hr.body = rulesBody;
              else
                hr.body = mk<OR>(mk<AND>(hr.body, condPrev), mk<AND>(rulesBody, cond));

              firstMatrix = false;

              errs() << "\nUpdated rule: ";
              hr.printMemberVars();

              ruleManager.arrayStores[i].clear();
              ruleManager.arraySelects[i].clear();

              ExprSet ssa, conjs;
              getConj(rulesBody, ssa);

              // errs() << "new rule: " << *rulesBody << "\n";


              // AH: FIX THIS BIG TIME (make it more efficient)
              for (int j = 0; j < bnd.bindVars.back().size(); j++)
              {
                Expr a = hr.srcVars[j];
                Expr b = hr.dstVars[j];
                if (!isOpX<ARRAY_TY>(bind::typeOf(a))) continue;
                // errs() << "ARRAY: " << *a << "\n";
                Expr result, result1, indx;
                if (!u.implies(rulesBody, mk<EQ>(a, b)))
                {
                  findExpr<EQ>(b, rulesBody, result);
                  // errs() << "found: " << *result << "\n";
                  if (isOpX<STORE>(result->right())) 
                  {
                    // errs() << "index: " << *result->right()->arg(1) << "\n";
                    indx = result->right()->arg(1);
                    for (int k = 0; k < hr.dstVars.size(); k++)
                    {
                      if (contains(indx, hr.dstVars[k]))
                      {
                        // errs() << "contains: " << *hr.dstVars[k] << "\n";
                        findExpr<EQ>(hr.dstVars[k], rulesBody, result1);
                        // errs() << "result1 is: " << *result1 << "\n";
                        getConj(result1, conjs);
                        result1 = NULL;
                        for (auto &it : conjs)
                        {
                          if (!containsOp<ARRAY_TY>(it))
                          {
                            if (!result1) result1 = it;
                            else result1 = mk<AND>(result1, it);
                          }
                        }
                        // errs() << "updated result1 is: " << *result1 << "\n";

                        ExprSet s{hr.dstVars[k]};
                        indx = ufo::eliminateQuantifiers(mk<AND>(indx, result1), s);
                        // errs() << "updated index is: " << *indx << "\n";
                      }
                    }
                    ruleManager.arrayStores[i][j].push_back(indx);
                  }
                }
                else
                {
                  for (auto &it : ssa)
                  {
                    // errs() << "\n\nsearching in: " << *it << "\n";
                    findStoresAndSelects(a, it->right(), j, i);
                  }
                  
                  Expr result1;
                  Expr indx = ruleManager.arraySelects[i][j].back();
                  // errs() << "for array select, indx: " << *indx << "\n";
                  for (int k = 0; k < hr.dstVars.size(); k++)
                  {
                    if (contains(indx, hr.dstVars[k]))
                    {
                      // errs() << "contains: " << *hr.dstVars[k] << "\n";
                      findExpr<EQ>(hr.dstVars[k], rulesBody, result1);
                      // errs() << "result1 is: " << *result1 << "\n";
                      getConj(result1, conjs);
                      result1 = NULL;
                      for (auto &it : conjs)
                      {
                        if (!containsOp<ARRAY_TY>(it))
                        {
                          if (!result1) result1 = it;
                          else result1 = mk<AND>(result1, it);
                        }
                      }
                      // errs() << "updated result1 is: " << *result1 << "\n";

                      ExprSet s{hr.dstVars[k]};
                      indx = ufo::eliminateQuantifiers(mk<AND>(indx, result1), s);
                      // errs() << "updated index is: " << *indx << "\n";
                    }
                  }
                  ruleManager.arraySelects[i][j].back() = indx;
                }
              }

              candsFromCurrentMatrix.clear();
              getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix, model);
              candsFromCurrentMatrixCnj = conjoin(candsFromCurrentMatrix[rel], m_efac);

              candsFromCurrentMatrixCnj = simplifyArithm(candsFromCurrentMatrixCnj);

              errs() << "cands from updated matrix: " << *candsFromCurrentMatrixCnj << "\n";

              cands.clear();
              for (auto& it2 : nonIterPairs)
              {
                Expr cand1, cand2;
                if (isConst<ARRAY_TY>(rule.srcVars[it2[0]]))
                {
                  if (!ruleManager.arrayStores[i][it2[0]].empty())
                    cand1 = ruleManager.arrayStores[i][it2[0]].back();
                  else 
                    cand1 = ruleManager.arraySelects[i][it2[0]].back();
                  if (!ruleManager.arrayStores[i][it2[1]].empty())
                    cand2 = ruleManager.arrayStores[i][it2[1]].back();
                  else 
                    cand2 = ruleManager.arraySelects[i][it2[1]].back();
                  // cands.insert(mk<EQ>(cand1, cand2));
                  cands.insert(mk<EQ>(mk<SELECT>(rule.srcVars[it2[0]], cand1), mk<SELECT>(rule.srcVars[it2[1]], cand2)));
                }
                else
                  cands.insert(mk<EQ>(rule.srcVars[it2[0]], rule.srcVars[it2[1]]));
              }
            }
            query->body = queryBodyBackUp;
          }
          prefixRule.body = ruleBodyBackup;
        }
      }
      return 0;
    }


    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      map<int, ExprVector> candidatesTmp = candidates;
      bool res1 = true;
      for (auto &h: worklist)
      {
        HornRuleExt& hr = *h;

        if (hr.isQuery) continue;

        if (!checkCHC(hr, candidatesTmp))
        {
          bool res2 = true;
          int ind = getVarIndex(hr.dstRelation, decls);
          errs() << "\ncands considered:\n";
          for (auto it : candidatesTmp[ind])
            errs() << *it << "\n";
          Expr model = u.getModel(hr.dstVars);
          if (model)
          errs() << "\nmodel: " << *model << "\n";
          if (isSkippable(model, hr.dstVars, candidatesTmp))
          {
            errs() << "isSkippable\n";
            // something went wrong with z3. do aggressive weakening (TODO: try bruteforce):
            candidatesTmp[ind].clear();
            res2 = false;
          }
          else
          {
            errs() << "isSkippable not\n";
            ExprVector& ev = candidatesTmp[ind];
            ExprVector invVars;
            for (auto & a : invarVars[ind]) invVars.push_back(a.second);
            SamplFactory& sf = sfs[ind].back();

            for (auto it = ev.begin(); it != ev.end(); )
            {
              Expr repl = *it;
              for (auto & v : invarVars[ind]) repl = replaceAll(repl, v.second, hr.dstVars[v.first]);

              if (!u.isSat(model, repl))
              {
                if (hr.isFact)
                {
                  Expr failedCand = normalizeDisj(*it, invVars);
               outs () << "failed cand for " << *hr.dstRelation << ": " << *failedCand << "\n";
                  Sampl& s = sf.exprToSampl(failedCand);
                  sf.assignPrioritiesForFailed();
                }
                errs() << "erasing: " << **it << "\n";
                it = ev.erase(it);
                res2 = false;
              }
              else
              {
                ++it;
              }
            }
          }

          if (recur && !res2)
          {
            errs() << "recur && !res2\n";
            res1 = false;
            break;
          }
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool findInvVar(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));

      for (auto & v : vars)
      {
        bool found = false;
        for (auto & w : invarVars[invNum])
        {
          if (w.second == v)
          {
            found = true;
            break;
          }
        }
        if (!found)
        {
          if (find (ve.begin(), ve.end(), v) == ve.end())
            return false;
        }
      }
      return true;
    }

    bool toCont(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));
      bool toCont = true;
      for (auto & expr : vars)
      {
        if (!findInvVar(invNum, expr, ve))
        {
          toCont = false;
          break;
        }
      }
      return toCont;
    }

    // heuristic to instantiate a quantified candidate for some particular instances
    void createGroundInstances (ExprSet& vals, ExprSet& res, Expr qcand, Expr iterVar)
    {
      ExprSet se;
      filter (qcand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (iterVar == a->right())
        {
          for (auto & v : vals)
          {
            res.insert(replaceAll(qcand, iterVar, v));
          }
        }
      }
    }

    // heuristic to replace weird variables in candidates
    bool prepareArrCand (Expr& replCand, ExprMap& replLog, ExprVector& av,
                         ExprSet& tmpRanges, ExprSet& concreteVals, int ind, int i = 0)
    {
      if (av.empty()) return false;

      ExprSet se;
      filter (replCand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (isOpX<MPZ>(a->right())  || (!findInvVar(ind, a->right(), av)))
        {
          if (isOpX<MPZ>(a->right()))
          {
            tmpRanges.insert(mk<EQ>(av[i], a->right()));
            concreteVals.insert(a->right());
          }
          // TODO:  try other combinations of replacements
          if (i >= av.size()) return false;
          replLog[a->right()] = av[i];
          replCand = replaceAll(replCand, a->right(), replLog[a->right()]);

          return prepareArrCand (replCand, replLog, av, tmpRanges, concreteVals, ind, i + 1);
        }
      }
      return true;
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands, /*map<Expr, ExprSet>& candsForPhi, */bool analizeCode = true)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      ExprSet candsFromCode;
      bool analizedExtras = false;
      bool isFalse = false;
      bool hasArrays = false;

      // for Arrays
      ExprSet tmpArrAccess;
      ExprSet tmpArrSelects;
      ExprSet tmpArrCands;
      ExprSet tmpArrFuns;
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[ind], sf.lf.nonlinVars);

        if (analizeCode) sm.analizeCode(/*candsForPhi[invRel]*/);
        else sm.candidates.clear();

        if (!analizedExtras && hr.srcRelation == invRel)
        {
          sm.analizeExtras (cands[invRel]);
          analizedExtras = true;
        }
        // parse seed miner directly here
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);

        // for arrays
        if (analizeCode && ruleManager.hasArrays[invRel])
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          tmpArrSelects.insert(sm.arrSelects.begin(), sm.arrSelects.end());
          tmpArrFuns.insert(sm.arrFs.begin(), sm.arrFs.end());
          hasArrays = true;
        }
      }

      if (hasArrays)
      {
        Expr pre = preconds[ind];
        if (pre != NULL)
        {
          pre = ineqSimplifier(iterators[ind], pre);
          Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
          arrAccessVars[ind].push_back(qVar);

          assert (isOpX<EQ>(pre)); // TODO: support more

          ExprVector invAndIterVarsAll;
          for (auto & a : invarVars[ind]) invAndIterVarsAll.push_back(a.second);
          invAndIterVarsAll.push_back(qVar);

          Expr fla;
          if (pre->right() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, pre->left()) :
                                     mk<LEQ>(qVar, pre->left());
          else if (pre->left() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, pre->right()) :
                                     mk<LEQ>(qVar, pre->right());

          arrIterRanges[ind].insert(normalizeDisj(fla, invAndIterVarsAll));
          arrIterRanges[ind].insert(normalizeDisj(
                  replaceAll(postconds[ind], iterators[ind], qVar), invAndIterVarsAll));
        }

        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr qVar2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[ind].push_back(qVar2);

          Expr range = conjoin (arrIterRanges[invNumTo], m_efac);
          ExprSet quantified;
          for (int i = 0; i < nested->dstVars.size(); i++)
          {
            range = replaceAll(range, invarVars[invNumTo][i], nested->dstVars[i]);
            quantified.insert(nested->dstVars[i]);
          }

          // naive propagation of ranges
          ExprSet cnjs;
          getConj(nested->body, cnjs);
          for (auto & a : cnjs)
          {
            for (auto & b : quantified)
            {
              if (isOpX<EQ>(a) && a->right() == b)
              {
                range = replaceAll(range, b, a->left());
              }
              else if (isOpX<EQ>(a) && a->left() == b)
              {
                range = replaceAll(range, b, a->right());
              }
            }
          }
          arrIterRanges[ind].insert(
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), qVar2),
                      iterators[ind], *arrAccessVars[ind].begin()));
        }

        // process all quantified seeds
        for (auto & a : tmpArrCands)
        {
          // push all elements in tmpArrCands to candForPhi, unless the below transformations are required
          // in that case, push replCand
          if (u.isTrue(a) || u.isFalse(a)) continue;
          Expr replCand = a;
          for (int i = 0; i < 3; i++)
            for (auto & v : sf.lf.nonlinVars)
              replCand = replaceAll(replCand, v.second, v.first);
          if (!u.isTrue(replCand) && !u.isFalse(replCand))
          {
            ExprMap replLog;
            ExprSet tmpRanges;
            ExprSet concreteVals;
            if (prepareArrCand (replCand, replLog, arrAccessVars[ind], tmpRanges, concreteVals, ind) &&
               (contains(replCand, iterators[ind]) || !emptyIntersect(replCand, arrAccessVars[ind])))
            {
              // very cheeky heuristic: sometimes restrict, but sometimes extend the range
              // depending on existing constants
              if (u.isSat(conjoin(tmpRanges, m_efac), conjoin(arrIterRanges[ind], m_efac)))
              {
                arrIterRanges[ind].insert(tmpRanges.begin(), tmpRanges.end());
              }
              else
              {
                for (auto & a : tmpArrCands)
                  createGroundInstances (concreteVals, candsFromCode, a, iterators[ind]);
              }

              // at this point it should not happen, but sometimes it does. To debug.
              if (!findInvVar(ind, replCand, arrAccessVars[ind])) continue;

              for (auto iter : arrAccessVars[ind])
                arrCands[ind].insert(replaceAll(replCand, iterators[ind], iter));
            }
            else candsFromCode.insert(a);
          }
        }

        // trick for tiling benchs
        ExprSet afs;
        for (auto & a : tmpArrFuns)
        {
          ExprVector vars;
          filter (a, bind::IsConst(), std::inserter (vars, vars.begin ()));
          if (vars.size() != 1 || *vars.begin() == a) continue;
          afs.insert(replaceAll(a, *vars.begin(), arrAccessVars[ind][0]));
        }

        for (auto & s : afs)
        {
          for (auto & qcand : arrCands[ind])
          {
            ExprSet se;
            filter (qcand, bind::IsSelect (), inserter(se, se.begin()));
            for (auto & arrsel : se)
            {
              Expr qcandTmp = replaceAll(qcand, arrsel->right(), s);
              arrCands[ind].insert(qcandTmp);
            }
          }
        }
      }

      // process all quantifier-free seeds
      for (auto & cand : candsFromCode)
      {
        checked.clear();
        Expr replCand = cand;
        for (int i = 0; i < 3; i++)
          for (auto & v : sf.lf.nonlinVars)
            replCand = replaceAll(replCand, v.second, v.first);
        // sanity check for replCand:
        if (toCont (ind, replCand, arrAccessVars[ind]) && addCandidate(ind, replCand))
          propagate (ind, replCand, true);
      }
    }

    void refreshCands(map<Expr, ExprSet>& cands)
    {
      cands.clear();
      for (auto & a : candidates)
      {
        cands[decls[a.first]].insert(a.second.begin(), a.second.end());
      }
    }

    bool anyProgress(vector<HornRuleExt*> worklist)
    {
      for (int i = 0; i < invNumber; i++)
      {
        // simple check if there is a non-empty candidate
        for (auto & hr : worklist)
        {
          if (hr->srcRelation == decls[i] || hr->dstRelation == decls[i])
          {
            if (candidates[i].size() > 0)
            {
              return true;
            }
          }
        }
      }
      return false;
    }

#ifdef HAVE_ARMADILLO
    void getDataCandsForDcl(map<Expr, ExprSet>& cands, const vector<string> & behaviorfiles, 
      Expr dcl, int& fileIndex, arma::mat& dataMatrix, Expr initVals=NULL){
      DataLearner dl(ruleManager, m_z3);
      errs() << "before initialize\n";
      dl.initialize(dcl, true /*multipleLoops*/, 2, initVals);
      string filename("");
      if (fileIndex < behaviorfiles.size()) {
        filename = behaviorfiles[fileIndex];
        fileIndex++;
      }
      errs() << "before computeData\n";
      if (!dl.computeData(filename)) return;
      ExprSet tmp, tmp2;
      map<Expr, ExprVector> substs;
      errs() << "before computePolynomials\n";
      (void)dl.computePolynomials(tmp);
      errs() << "after computePolynomials\n";
      for (auto a : tmp)
      {
        errs() << " >>>> CAND FROM DATA for " << *dcl << ": " << *a << "\n";
        // before pushing them to the cand set, we do some small mutations to get rid of specific consts
        a = simplifyArithm(a);
        if (isOpX<EQ>(a) && isIntConst(a->left()) &&
            isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
        {
          substs[a->right()].push_back(a->left());
        }
        else
        {
          tmp2.insert(a);
        }
      }
      for (auto a : tmp2)
      {
        cands[dcl].insert(a);
        if (isNumericConst(a->right()))

        for (auto b : substs)
        {
          cpp_int i1 = lexical_cast<cpp_int>(a->right());
          cpp_int i2 = lexical_cast<cpp_int>(b.first);

          if (i1 % i2 == 0)
            for (auto c : b.second)
            {
              Expr e = replaceAll(a, a->right(), mk<MULT>(mkMPZ(i1/i2, m_efac), c));
              cands[dcl].insert(e);
            }
        }
      }
      dataMatrix = dl.getDataMatrix();
    }

    void getDataCandidates(map<Expr, ExprSet>& cands, const vector<string> &behaviorfiles){
      int fileIndex = 0;
      arma::mat d;
      for (auto & dcl : decls) {
        getDataCandsForDcl(cands, behaviorfiles, dcl, fileIndex, d);
      }
    }
#endif

    bool bootstrap()
    {
      filterUnsat();

      if (multiHoudini(ruleManager.wtoCHCs))
      {
        errs() << "After multiHoudini\n";
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          printSolution();
          return true;
        }
      }

      // try array candidates one-by-one (adapted from `synthesize`)
      // TODO: batching
      //if (ruleManager.hasArrays)
      {
        for (auto & dcl: ruleManager.wtoDecls)
        {
          int invNum = getVarIndex(dcl, decls);
          SamplFactory& sf = sfs[invNum].back();
          for (auto & c : arrCands[invNum])
          {
            if (u.isTrue(c) || u.isFalse(c)) continue;
            checked.clear();
            Expr cand = sf.af.getSimplCand(c);
            if (printLog)
              outs () << " - - - bootstrapped cand for " << *dcl << ": " << *cand << "\n";

            auto candidatesTmp = candidates[invNum]; // save for later
            if (!addCandidate(invNum, cand)) continue;
            if (checkCand(invNum))
            {
              assignPrioritiesForLearned();
              generalizeArrInvars(sf);
              if (checkAllLemmas())
              {
                outs () << "Success after bootstrapping\n";
                printSolution();
                return true;
              }
            }
            else
            {
              if (candidates[invNum].empty()) candidates[invNum] = candidatesTmp;
            }
          }
        }

        // second round of bootstrapping (to be removed after Houdini supports arrays)

        candidates.clear();
        ExprVector empt;
        for (auto &hr: ruleManager.chcs)
        {
          if (hr.isQuery)
          {
            int invNum = getVarIndex(hr.srcRelation, decls);
            ExprSet cnjs;
            getConj(hr.body, cnjs);
            for (auto & a : cnjs)
            {
              if (isOpX<NEG>(a) && findInvVar(invNum, a, empt))
              {
                candidates[invNum].push_back(a->left());
                break;
              }
            }
            break;
          }
        }
        if (multiHoudini(ruleManager.wtoCHCs))
        {
          assignPrioritiesForLearned();
          if (checkAllLemmas())
          {
            outs () << "Success after bootstrapping\n";
            printSolution();
            return true;
          }
        }
      }

      return false;
    }

    void updateGrammars()
    {
      // convert candidates to curCandidates and run the method from RndLearner
      for (int ind = 0; ind < invNumber; ind++)
      {
        if (candidates[ind].size() == 0) curCandidates[ind] = mk<TRUE>(m_efac);
        else curCandidates[ind] = conjoin(candidates[ind], m_efac);
      }
      updateRels();
      updCount++;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        if (!checkCHC(hr, candidates)) {
          if (!hr.isQuery)
          {
            errs() << "WARNING: Something went wrong" <<
              (ruleManager.hasArrays[hr.srcRelation] || ruleManager.hasArrays[hr.dstRelation] ?
              " (possibly, due to quantifiers)" : "") <<
              ". Restarting...\n";

            for (int i = 0; i < decls.size(); i++)
            {
              SamplFactory& sf = sfs[i].back();
              ExprSet lms = sf.learnedExprs;
              for (auto & l : lms) candidates[i].push_back(l);
            }
            multiHoudini(ruleManager.wtoCHCs);
            assignPrioritiesForLearned();

            return false;
            assert(0);    // only queries are allowed to fail
          }
          else
            return false; // TODO: use this fact somehow
        }
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations)
    {
      // outs()  << "CHECKING " << * hr.srcRelation << " -> "<< * hr.dstRelation << "\n";
      ExprSet exprs;
      exprs.insert(hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        { 
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      return bool(!u.isSat(exprs));
    }

    bool checkCHC1 (HornRuleExt& hr, Expr assump, ExprSet& annotations)
    {
      // outs()  << "CHECKING " << * hr.srcRelation << " -> "<< * hr.dstRelation << "\n";
      ExprSet exprs;
      // exprs.insert(hr.body);
      exprs.insert(assump);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        // SamplFactory& sf = sfs[ind].back();
        // ExprSet lms = sf.learnedExprs;
        // for (auto & a : annotations) lms.insert(a);
        for (auto a : annotations)
        { 
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        ExprSet negged;
        for (auto a : annotations)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      errs() << "exprs: " << "\n";
      for (auto it : exprs)
        errs() << *it << "\n";
      errs() << "\n\n";
      return bool(!u.isSat(exprs));
    }


    // need to fix, not really covered all cases
    // look at getChainOfStores and getCounters in ExprSimpl.hpp
    void findStoresAndSelects(Expr array, Expr e, int i, int cycleNum)
    {
      if (contains(e, array) && (containsOp<STORE>(e) || containsOp<SELECT>(e))) 
      {
        // errs() << *e << "\n";
        if (isOpX<STORE>(e))
        {
          if (array == e->arg(0))
          {
            // errs() << "store at array " << *array << " at index " << *e->arg(1) << "\n";
            auto &v = ruleManager.arrayStores[cycleNum][i];
            if (find(v.begin(), v.end(), e->arg(1)) == v.end())
              v.push_back(e->arg(1));
            findStoresAndSelects(array, e->arg(2), i, cycleNum);
          }
          else 
          {
            findStoresAndSelects(array, e->arg(0), i, cycleNum);
            findStoresAndSelects(array, e->arg(2), i, cycleNum);
          }
        }

        if (isOpX<SELECT>(e))
        {
          if (array == e->arg(0))
          {
            // errs() << "select at array " << *array << " at index " << *e->arg(1) << "\n";
            auto &v = ruleManager.arraySelects[cycleNum][i];
            if (find(v.begin(), v.end(), e->arg(1)) == v.end())
              v.push_back(e->arg(1));
            // findStoresAndSelects(array, e->arg(1), i, cycleNum)
          }
          else 
          {
            findStoresAndSelects(array, e->arg(0), i, cycleNum);
            findStoresAndSelects(array, e->arg(1), i, cycleNum);
          }
        }
      }
      else return;
      if (isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e) || isOpX<DIV>(e))
      {
        findStoresAndSelects(array, e->arg(0), i, cycleNum);
        findStoresAndSelects(array, e->arg(1), i, cycleNum);
      }
    }

    void initArrayStuff(BndExpl& bnd, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      Expr rel = ruleManager.chcs[cycle[0]].srcRelation;
      int invNum = getVarIndex(rel, decls);
      if (iterators[invNum] != NULL) return;    // GF: TODO more sanity checks (if needed)

      ExprSet ssa;
      ssas[invNum] = bnd.toExpr(cycle);
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return; // todo: support

      getConj(ssas[invNum], ssa);

      // errs() << "SSA\n";
      // errs() << *ssas[invNum] << "\n\n";

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(&ruleManager.chcs[cycle[0]]);

      for (int i = 0; i < bnd.bindVars.back().size(); i++)
      {
        Expr a = ruleManager.chcs[cycle[0]].srcVars[i];
        Expr b = bnd.bindVars.back()[i];
        if (!isOpX<ARRAY_TY>(bind::typeOf(a))) continue;
        // errs() << "ARRAY: " << *a << "\n";
        Expr result;
        if (!u.implies(ssas[invNum], mk<EQ>(a, b)))
        {
          findExpr<EQ>(b, ssas[invNum], result);
          if (isOpX<STORE>(result->right())) {
            // errs() << "index: " << *result->right()->arg(1) << "\n";
            ruleManager.arrayStores[cycleNum][i].push_back(result->right()->arg(1));
          }
        }
        else
        {
          for (auto &it : ssa)
          {
            // errs() << "\n\nsearching in: " << *it << "\n";
            findStoresAndSelects(a, it->right(), i, cycleNum);
          }
        }
      }

      for (int i = 0; i < bnd.bindVars.back().size(); i++)
      {
        Expr a = ruleManager.chcs[cycle[0]].srcVars[i];
        Expr b = bnd.bindVars.back()[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        // TODO: pick one if there are multiple available
        if (u.implies(ssas[invNum], mk<GT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = false;
          ruleManager.iterator[rel] = i;
          break;
        }
        else if (u.implies(ssas[invNum], mk<LT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = true;
          ruleManager.iterator[rel] = i;
          break;
        }
      }

      ssa.clear();
      getConj(pref, ssa);
      for (auto & a : ssa)
      {
        if (contains(a, iterators[invNum]) && isOpX<EQ>(a))
        {
          preconds[invNum] = a;
          break;
        }
      }

      if (iterators[invNum] != NULL)
        ruleManager.hasArrays[rel] = true;
    }

    template <typename T>
    void findExpr(Expr toFind, Expr conj, Expr &result)
    {
      Expr res;
      if (isOpX<AND>(conj))
      {
        for (auto it = conj->args_begin(); it != conj->args_end(); it++)
        {
          findExpr<T>(toFind, *it, res);
          if (res)
          {
            if (result)
              result = mk<AND>(result, res);
            else
              result = res;
            res = NULL;
          }
        }
      }
      else if (isOpX<OR>(conj))
      {
        for (auto it = conj->args_begin(); it != conj->args_end(); it++)
        {
          findExpr<T>(toFind, *it, res);
          if (res)
          {
            if (result)
              result = mk<OR>(result, res);
            else
              result = res;
            res = NULL;
          }
        }
      }
      else if (isOpX<T>(conj))
        if (contains(conj, toFind))
          result = conj;
    }

    void varsMetaInfo(BndExpl& bnd, int cycleNum)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      Expr rel = ruleManager.chcs[cycle[0]].srcRelation;
      Expr rel1 = ruleManager.productRelsToSrcDst[rel][0];

      ruleManager.chcSrc->getDecl(rel1, rel1);
      int rel1DeclSize = rel1->arity() - 2;

      int invNum = getVarIndex(rel, decls);
      iters[cycleNum] = vector<vector<int>>{vector<int>(), vector<int>()};
      nonIters[cycleNum] = vector<vector<int>>{vector<int>(), vector<int>()};
      Expr init = bnd.compactPrefix(cycleNum);
      Expr initAndCycle = mk<AND>(init, ssas[invNum]);
      vector<int> chc1VarsArray, chc2VarsArray, chc1VarsInt, chc2VarsInt, chc1VarsBool, chc2VarsBool;

        errs() << *ssas[invNum] << "\n";
      for (int i = 0; i < bnd.bindVars.back().size(); i++)
      {
        bool notAnIter = false;
        Expr e, gt, ge, lt, le, limit;
        Expr a = ruleManager.chcs[cycle[0]].srcVars[i];
        Expr b = bnd.bindVars.back()[i];
        // errs() << "checking: " << *b << "\n";

        // would it consider a variable iterator if it's increasing/decreasing but does not have a limit value?
        // make sure 

        // iterator always decreases
        if (bind::isIntConst(a) && u.implies(ssas[invNum], mk<GT>(a, b)))
        {
          findExpr<EQ>(b, ssas[invNum], e);
          errs() << "\nfinding: " << *b << "\n\n";
          
          e = ineqSimplifier(b, e);
          errs() << "found: " << *e << "\n\n";

          // AH: handle the case where e is a conjunction or disjunction
          // for now, just skip the case
          if (isOpX<AND>(e) || isOpX<OR>(e)) continue;

          Expr right = e->right();
          Expr initVal, transitionVal;
          int minusOrDiv = 0;
          bool initValFound = false, transitionValFound = false, limitValFound = false;
          bool hasInitVal = false, hasTransitionVal = false, hasLimitVal = false;
          cpp_int initValNumeric, transitionValNumeric, limitValNumeric, numIters = 0, diff;

          // just a way to check if the operator is MINUS or DIV
          // fix this, choose a better way to check
          if (isOpX<MINUS>(right) || (isOpX<PLUS>(right) && isOpX<MPZ>(right->arg(1)))) minusOrDiv = 1;  
          else if (isOpX<DIV>(right)) minusOrDiv = 2;

          // check if it's a simple relation like (var - c), where c is a constant
          // make sure the ordering of the occurence of both Exprs var and c are correct
          // right->arg(0) should be the same as variable a in this code
          if (isIntConst(right->arg(0)))
          {
            Expr model;
            findExpr<EQ>(right->arg(0), init, initVal);
            initVal = ineqSimplifier(right->arg(0), initVal);
            // errs() << "init: " << *initVal << "\n";
            /*if (initVal && isNumericConst(initVal->right())) 
            {
              initValNumeric = lexical_cast<cpp_int>(initVal->right());
              initValFound = true;
            }
            else */if (u.hasOneModel(right->arg(0), init))
            {
              u.isSat(init);
              model = u.getModel(right->arg(0));
              initValNumeric = lexical_cast<cpp_int>(model);
              initValFound = true;
            }
            if (initVal) hasInitVal = true;
            if (model) initVal = model;
          }

          transitionVal = right->arg(1);
          if (isNumericConst(transitionVal))
          {
            transitionValNumeric = lexical_cast<cpp_int>(transitionVal);
            transitionValFound = true;
            hasTransitionVal = true;
          }
          else if (isNumeric(transitionVal))
          {
            Expr model;
            if (u.hasOneModel(transitionVal, initAndCycle))
            {
              u.isSat(initAndCycle);
              model = u.getModel(transitionVal);
              transitionValNumeric = lexical_cast<cpp_int>(model);
              transitionValFound = true;
            }
            hasTransitionVal = true;
          }

          findExpr<GT>(a, ssas[invNum], gt);
          findExpr<GEQ>(a, ssas[invNum], ge);

          // make sure there is no case where both gt and ge are not null
          // cannot think of any but could be
          if (gt) 
          {
            gt = ineqSimplifier(a, gt);
            // errs() << "gt: " << *gt << "\n";
            limit = gt->arg(1);
          }
          if (ge) 
          {
            ge = ineqSimplifier(a, ge);
            // errs() << "ge: " << *ge << "\n";
            limit = ge->arg(1);
          }
          // limit is just a number, like (var > c), c is a constant
          if (limit && isNumericConst(limit))
          {
            limitValNumeric = lexical_cast<cpp_int>(limit);
            cout << "limitValNumeric: " << limitValNumeric << "\n";
            limitValFound = true;
            hasLimitVal = true;
          }
          // limit is some variable and not constant, can occur in the case var > n, n is a variable
          else if (limit && isIntConst(limit))
          {
            Expr model;
            errs() << "intConst: " << *limit << "\n";
            if (u.hasOneModel(limit, initAndCycle))
            {
              u.isSat(initAndCycle);
              model = u.getModel(limit);
              limitValNumeric = lexical_cast<cpp_int>(model);
              limitValFound = true;
            }
            hasLimitVal = true;
            if (model) limit = model;
          }

          if (initValFound && transitionValFound && limitValFound)
          {
            if (minusOrDiv == 1)
            {
              cout << "initial val: " << initValNumeric << "\n";
              cout << "transition val: " << transitionValNumeric << "\n";
              cout << "final val: " << limitValNumeric << "\n";
              diff = abs(limitValNumeric - initValNumeric);
              if (ge) diff++;
              numIters = diff/abs(transitionValNumeric);
              cout << "numIters: " << numIters << "\n";
            }
          }
          else if (transitionValFound && hasInitVal && hasLimitVal)
          {
            if (minusOrDiv == 1)
            {
              numIters = -transitionValNumeric;
              cout << "numIters: " << numIters << "\n";
            }
          }

          bool isAnIter = hasInitVal && hasTransitionVal && hasLimitVal;
          if (numIters != 0 || isAnIter)
          {
            if (i < rel1DeclSize)
              iters[cycleNum][0].push_back(i);
            else
              iters[cycleNum][1].push_back(i);
            
            // this iter is decreasing
            itersGrow[cycleNum][i] = false;
            numOfIters[cycleNum][i] = numIters;
            initValsIters[cycleNum][i] = initVal;
            limitValsIters[cycleNum][i] = limit;
          }
          else notAnIter = true;
        }
        // iterator always increases
        else if (bind::isIntConst(a) && u.implies(ssas[invNum], mk<LT>(a, b)))
        {
          findExpr<EQ>(b, ssas[invNum], e);
          errs() << "\nfinding: " << *b << "\n\n";

          e = ineqSimplifier(b, e);
          errs() << "found: " << *e << "\n\n";

          // handle the case where e is a conjunction or disjunction
          // for now, just skip the case
          if (isOpX<AND>(e) || isOpX<OR>(e)) continue;

          Expr right = e->right();
          Expr initVal, transitionVal;
          int plusOrMult = 0;
          bool initValFound = false, transitionValFound = false, limitValFound = false;
          bool hasInitVal = false, hasTransitionVal = false, hasLimitVal = false;
          cpp_int initValNumeric, transitionValNumeric, limitValNumeric, numIters = 0, diff;

          // just a way to check if the operator is PLUS or MULT
          if (isOpX<PLUS>(right)) plusOrMult = 1;  
          else if (isOpX<MULT>(right)) plusOrMult = 2;

          // check if it's a simple relation like (var + c), where c is a constant
          // make sure the ordering of the occurence of both Exprs var and c are correct
          // right->arg(0) should be the same as variable a in this code
          if (isIntConst(right->arg(0)))
          {
            Expr model;
            findExpr<EQ>(right->arg(0), init, initVal);
            initVal = ineqSimplifier(right->arg(0), initVal);
            // errs() << "init: " << *initVal << "\n";
            /*if (initVal && isNumericConst(initVal->right())) 
            {
              initValNumeric = lexical_cast<cpp_int>(initVal->right());
              initValFound = true;
            }
            else */if (u.hasOneModel(right->arg(0), init))
            {
              u.isSat(init);
              model = u.getModel(right->arg(0));
              initValNumeric = lexical_cast<cpp_int>(model);
              initValFound = true;
            }
            if (initVal) hasInitVal = true;
            if (model) initVal = model;
          }

          transitionVal = right->arg(1);
          if (isNumericConst(transitionVal))
          {
            transitionValNumeric = lexical_cast<cpp_int>(transitionVal);
            transitionValFound = true;
            hasTransitionVal = true;
          }
          else if (isNumeric(transitionVal))
          {
            Expr model;
            if (u.hasOneModel(transitionVal, initAndCycle))
            {
              u.isSat(initAndCycle);
              model = u.getModel(transitionVal);
              transitionValNumeric = lexical_cast<cpp_int>(model);
              transitionValFound = true;
            }
            hasTransitionVal = true;
          }

          findExpr<LT>(a, ssas[invNum], lt);
          findExpr<LEQ>(a, ssas[invNum], le);

          // make sure there is no case where both lt and le are not null
          // cannot think of any but could be
          if (lt) 
          {
            lt = ineqSimplifier(a, lt);
            // errs() << "lt: " << *lt << "\n";
            limit = lt->right();
          }
          if (le) 
          {
            le = ineqSimplifier(a, le);
            // errs() << "le: " << *le << "\n";
            limit = le->right();
          }
          // limit is just a number, like (var < c), c is a constant
          if (limit && isNumericConst(limit))
          {
            limitValNumeric = lexical_cast<cpp_int>(limit);
            cout << "limitValNumeric: " << limitValNumeric << "\n";
            limitValFound = true;
            hasLimitVal = true;
          }
          // limit is some variable and not constant, can occur in the case var > n, n is a variable
          else if (limit && isIntConst(limit))
          {
            Expr model;
            errs() << "intConst: " << *limit << "\n";
            if (u.hasOneModel(limit, initAndCycle))
            {
              u.isSat(initAndCycle);
              model = u.getModel(limit);
              limitValNumeric = lexical_cast<cpp_int>(model);
              limitValFound = true;
            }
            hasLimitVal = true;
            if (model) limit = model;
          }

          if (initValFound && transitionValFound && limitValFound)
          {
            if (plusOrMult == 1)
            {
              cout << "initial val: " << initValNumeric << "\n";
              cout << "transition val: " << transitionValNumeric << "\n";
              cout << "final val: " << limitValNumeric << "\n";
              diff = abs(limitValNumeric - initValNumeric);
              if (ge) diff++;
              numIters = diff/abs(transitionValNumeric);
              cout << "numIters: " << numIters << "\n";
            }
          }
          else if (transitionValFound && hasInitVal && hasLimitVal)
          {
            if (plusOrMult == 1)
            {
              numIters = -transitionValNumeric;
              cout << "numIters: " << numIters << "\n";
            }
          }

          bool isAnIter = hasInitVal && hasTransitionVal && hasLimitVal;
          if (numIters != 0 || isAnIter)
          {
            if (i < rel1DeclSize)
              iters[cycleNum][0].push_back(i);
            else
              iters[cycleNum][1].push_back(i);
            
            // this iter is increasing
            itersGrow[cycleNum][i] = true;
            numOfIters[cycleNum][i] = numIters;
            initValsIters[cycleNum][i] = initVal;
            limitValsIters[cycleNum][i] = limit;
          }
          else notAnIter = true;
        }
        else notAnIter = true;

        // todo: might need to handle the case when the variable is an iterator but not initialized 
        // so, have to add it to the chc1VarsInt and chc2VarsInt
 
        // the variable is not an iter 
        if (notAnIter)
        {
          if (bind::isIntConst(a))
          {
            if (!u.hasOneModel(a, init))
            {
              if (i < rel1DeclSize) chc1VarsInt.push_back(i);
              else chc2VarsInt.push_back(i);
            }
          }
          else if (bind::isBoolConst(a))
          {
            if (!u.hasOneModel(a, init))
            {
              if (i < rel1DeclSize) chc1VarsBool.push_back(i);
              else chc2VarsBool.push_back(i);
            }
          }
          else if (isOpX<ARRAY_TY>(bind::typeOf(a)))
          {
            // any way to make sure the array is properly initialized? 
            // For now, assume it's not initialized
            if (i < rel1DeclSize) chc1VarsArray.push_back(i);
            else chc2VarsArray.push_back(i);
          }

          // only use an int as a non-iter if it changes in the cycle, use all other vars as non-iters
          if (!bind::isIntConst(a) || !u.implies(ssas[invNum], mk<EQ>(a, b)))
            if (i < rel1DeclSize) nonIters[cycleNum][0].push_back(i);
            else nonIters[cycleNum][1].push_back(i);
        }
      }

      auto &chc = ruleManager.chcs[cycle[0]];

      // errs() << "ARRAY1\n";
      // for (auto it1 : chc1VarsArray) errs() << "var: " << *chc.dstVars[it1] << "\n";
      // errs() << "ARRAY2\n";
      // for (auto it1 : chc2VarsArray) errs() << "var: " << *chc.dstVars[it1] << "\n";

      // errs() << "Int1\n";
      // for (auto it1 : chc1VarsInt) errs() << "var: " << *chc.dstVars[it1] << "\n";
      //   errs() << "Int2\n";
      // for (auto it1 : chc2VarsInt) errs() << "var: " << *chc.dstVars[it1] << "\n";

      // errs() << "Bool1\n";
      // for (auto it1 : chc1VarsBool) errs() << "var: " << *chc.dstVars[it1] << "\n";
      //   errs() << "Bool2\n";
      // for (auto it1 : chc2VarsBool) errs() << "var: " << *chc.dstVars[it1] << "\n";

      vector<vector<vector<int>>> combsArray, combsInt, combsBool, combs, combs1;
      combinationsOfVars(chc1VarsArray, chc2VarsArray, combsArray);
      combinationsOfVars(chc1VarsInt, chc2VarsInt, combsInt);
      combinationsOfVars(chc1VarsBool, chc2VarsBool, combsBool);

      joinVars(combsArray, combsInt, combs1);
      joinVars(combs1, combsBool, combs);

      // fix later
      vector<vector<int>> v{{-1, -1}};
      if (combs.empty()) combs.push_back(v);
      equalityCands[cycleNum] = combs;

      // for (auto elems: equalityCands[cycleNum])
      // {
      //   for (auto elems1 : elems)
      //   {
      //     errs() << "vars: " << *chc.dstVars[elems1[0]] << " and " << *chc.dstVars[elems1[1]] << "\n";
      //   }
      //   errs() << "\n\n";
      // }
    }

    void printSolution(bool simplify = true)
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        ExprSet lms = sf.learnedExprs;

        outs () << "(define-fun " << *rel << " (";
        for (auto & b : ruleManager.invVars[rel])
          outs () << "(" << *b << " " << u.varType(b) << ")";
        outs () << ") Bool\n  ";
        Expr tmp = conjoin(lms, m_efac);
        if (simplify && !containsOp<FORALL>(tmp)) u.removeRedundantConjuncts(lms);
        Expr res = simplifyArithm(tmp);
        u.print(res);
        outs () << ")\n";
      }
    }
  };

  inline void learnInvariantsPr(CHCs &ruleManager, int maxAttempts, bool freqs, bool aggp, bool enableDataLearning, const vector<string> & behaviorfiles)
  {
    char *c;
    EZ3 z3(ruleManager.m_efac);

    BndExpl bnd(ruleManager);

    if (!ruleManager.hasCycles())
    {
      bnd.exploreTraces(1, ruleManager.chcs.size(), true);
      return;
    }

    RndLearnerV3 ds(ruleManager.m_efac, z3, ruleManager, freqs, aggp);
    map<Expr, ExprSet> cands/*, candsForPhi*/;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      cands[ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation].insert(pref);
      //if (ruleManager.hasArrays)
      ds.initArrayStuff(bnd, i, pref);
      ds.varsMetaInfo(bnd, i);
    }

//     candsForPhi = cands;

    // errs() << "\n\n";
    // for (auto it : cands)
    // {
    //   errs() << "cand: " << *it.first << "\n";
    //   for (auto it2 : it.second)
    //     errs() << *it2 << " ";
    //   errs() << "\n";
    // }
    // errs() << "\n\n";

    for (auto& dcl: ruleManager.wtoDecls) ds.getSeeds(dcl, cands/*, candsForPhi*/);
    ds.refreshCands(cands);

    // errs() << "after refreshCands\n";
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();
    // errs() << "after calculateStatistics\n";
    // if (ds.bootstrap()) return;
    // bool check = ds.bootstrap();
    // errs() << "HERE\n";
    int eqStatus = ds.alignment(behaviorfiles, bnd);
    if (eqStatus == 1 && ds.checkAllLemmas())
      errs() << "The programs are equivalent\n";
    else if (eqStatus == 2)
    {
      for (auto it : ruleManager.chcs)
      {
        ExprVector v;
        Expr q = createQuantifiedFormula(it.body, v);
        SMTUtils su(it.body->getFactory());
        su.serialize_formula(q);
      }

      RndLearnerV3 ds1(ruleManager.m_efac, z3, ruleManager, freqs, aggp);
      map<Expr, ExprSet> cands1;
      for (auto& dcl: ruleManager.decls) ds1.initializeDecl(dcl);

      for (int i = 0; i < ruleManager.cycles.size(); i++)
      {
        Expr pref = bnd.compactPrefix(i);
        cands1[ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation].insert(pref);
        //if (ruleManager.hasArrays)
        ds1.initArrayStuff(bnd, i, pref);
        ds1.varsMetaInfo(bnd, i);
        for (auto num : ruleManager.outgs[ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation])
          if (ruleManager.chcs[num].isQuery)
           errs() << "body of query is: " << *ruleManager.chcs[num].body << "\n";
      }

      for (auto it : cands1)
      {
        errs() << "cand: " << *it.first << "\n";
        for (auto it2 : it.second)
          errs() << *it2 << " ";
        errs() << "\n";
      }
      errs() << "\n\n";

      for (auto& dcl: ruleManager.wtoDecls) ds1.getSeeds(dcl, cands1);
      ds1.refreshCands(cands1);

      for (auto& dcl: ruleManager.decls) ds1.doSeedMining(dcl->arg(0), cands1[dcl->arg(0)], false);
      ds1.calculateStatistics();
      bool check1 = ds1.bootstrap();
      if (check1) errs() << "The programs are equivalent\n";
      else errs() << "The programs are not equivalent\n";
    }
    else errs() << "The programs are not equivalent\n";

    // if (check) return;
//     std::srand(std::time(0));
//     ds.synthesize(maxAttempts, c);
  }
}

#endif
