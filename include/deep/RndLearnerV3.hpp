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
    map<int, ExprVector> candidatesBackUp;
    int updCount = 1;

    map<int, Expr> iterators; // per cycle
    map<int, vector<ExprVector>> iters;  // contains all vars that have a behavior of iterator
    map<int, map<Expr, bool>> itersGrow;  // whether the iters are increasing or decreasing
    map<int, map<Expr, cpp_int>> numOfIters;  // contains all vars that have a behavior of iterator
    map<int, vector<ExprVector>> nonIters;  // contains all vars that do not have a behavior of iterator
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

    void alignment(const vector<string> & behaviorfiles)
    {
      // ExprSet equivalentLoops;
      map<Expr, ExprSet> invariant;
      for (auto it : candidatesBackUp) {
        for (auto it2 : it.second) {
          invariant[decls[it.first]].insert(it2);
        }
      }
      int fileIndex = 0;
      for (int i = 0; i < ruleManager.cycles.size(); i++)
      {
        bool equivalent = false;
        vector<ExprVector> iterPairs;
        vector<ExprVector> nonIterPairs;
        vector<int>& cycle = ruleManager.cycles[i];
        Expr rel = ruleManager.chcs[cycle[0]].srcRelation;
        int invNum = getVarIndex(rel, decls);

        vector<ExprVector> itersForInv = iters[invNum];
        vector<ExprVector> nonItersForInv = nonIters[invNum];

        for (int j = 0; j < itersForInv[0].size(); j++)
        {
          ExprVector v{itersForInv[0][j], itersForInv[1][j]};
          iterPairs.push_back(v);
        }

        for (int j = 0; j < nonItersForInv[0].size(); j++)
        {
          ExprVector v{nonItersForInv[0][j], nonItersForInv[1][j]};
          nonIterPairs.push_back(v);
        }

        map<Expr, ExprSet> candsFromCurrentMatrix;
        arma::mat dataMatrix;
        getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix);

        Expr candsFromCurrentMatrixCnj = conjoin(candsFromCurrentMatrix[rel], m_efac);
        Expr invariantCnj = conjoin(invariant[rel], m_efac);
        Expr candsFromCurrentMatrixAndInv = mk<AND>(candsFromCurrentMatrixCnj, invariantCnj);

        for (auto it = iterPairs.begin(); it != iterPairs.end(); it++)
        {
          Expr iter1 = (*it)[0], iter2 = (*it)[1];
          errs() << "\n\nassuming iters: " << *iter1 << " and " << *iter2 << "\n";
          cpp_int numIters1 = numOfIters[invNum][iter1];
          cpp_int numIters2 = numOfIters[invNum][iter2];
          cout << "numIters: " << numIters1 << " and " << numIters2 << "\n";

          ExprSet cands;
          vector<ExprVector> aligningCandidates;

          for (auto& it2 : nonIterPairs)
          {
            aligningCandidates.push_back(it2);
            cands.insert(mk<EQ>(it2[0], it2[1]));
          }

          for (auto it3 = iterPairs.begin(); it3 != iterPairs.end(); it3++)
          {
            if (it3 != it) 
            {
              aligningCandidates.push_back(*it3);
              cands.insert(mk<EQ>((*it3)[0], (*it3)[1]));
            }
          }

          bool foundRelation = true;
          if (numIters1 == numIters2 && numIters1 > 0)
          {
            for (auto& it2 : aligningCandidates)
            {
              foundRelation = varsRelated(it2[0], it2[1], candsFromCurrentMatrix[rel]);
              if (!foundRelation) break;
            }
            if (foundRelation)
            {
              // equivalentLoops.insert(rel);
              equivalent = true;
              errs() << "We have found the loop is equivalent: " << *rel << "\n";
            }
          }

          // if (find(equivalentLoops.begin(), equivalentLoops.end(), rel) != equivalentLoops.end())
          if (equivalent)
            break;

          vector<HornRuleExt*> worklist;
          for (auto &hr: ruleManager.chcs)
            if ((hr.srcRelation == rel || hr.dstRelation == rel) && !hr.isQuery)
              worklist.push_back(&hr);
          
          for (auto &h: worklist)
          {
            HornRuleExt& hr = *h;

            while (true) 
            {
              Expr model;
              Expr firstMatrix = mk<AND>(candsFromCurrentMatrixCnj, mkNeg(conjoin(cands, m_efac)));
              if (u.isSat(firstMatrix))
              {
                errs() << "First dataMatrix does not imply equality\n";
              }
              else if (!checkCHC1(hr, invariantCnj, cands))
              {
                model = u.getModel(hr.dstVars);
                // model = replaceAll(model, hr.dstVars, hr.srcVars);
                errs() << "\nmodel: " << *model << "\n\n";

                candsFromCurrentMatrix.clear();
                getDataCandsForDcl(candsFromCurrentMatrix, behaviorfiles, rel, fileIndex, dataMatrix, model);
              }
              else
                 break;

              errs() << "\ncands for current data matrix: \n";
              for (auto it : candsFromCurrentMatrix[rel]) errs() << *it << " ";
                errs() << "\n";

              Expr conjoined = conjoin(candsFromCurrentMatrix[rel], m_efac);

              ExprVector checking = aligningCandidates[0];

              auto ind1 = find(hr.srcVars.begin(), hr.srcVars.end(), checking[0]);
              auto ind2 = find(hr.srcVars.begin(), hr.srcVars.end(), checking[1]);

              if (ind1 != hr.srcVars.end() && ind2 != hr.srcVars.end())
              {
                int i1 = ind1 - hr.srcVars.begin();
                int i2 = ind2 - hr.srcVars.begin();
                errs() << "indices are: " << i1 << " and " << i2 << "\n";

                int j, k;
                bool found = false;
                for (k = 0; k < dataMatrix.n_rows; k++)
                {
                  for (j = 0; j < dataMatrix.n_rows; j++)
                  {
                    if (dataMatrix(j, i1+1) == dataMatrix(k, i2+1)) 
                    {
                      errs() << "matching at: " << dataMatrix(j, i1+1) << " and " << dataMatrix(k, i2+1) << "\n";
                      found = true;
                      break;
                    } 
                  }
                  if (found) break;
                }

                vector<int> matchesInd1, matchesInd2;
                int currentMatch1 = j, currentMatch2 = k;
                if (found)
                {
                  for (int a = j+1; a < dataMatrix.n_rows; a++)
                  {
                    for (int b = k+1; b < dataMatrix.n_rows; b++)
                    {
                      if (dataMatrix(a, i1+1) == dataMatrix(b, i2+1)) 
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

                int numItersOfLoop1 = 0, numItersOfLoop2 = 0;
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
                rules1.body = ufo::eliminateQuantifiers(rules1.body, vars);
                rules1.locVars.clear();

                ExprSet vars1(rules2.locVars.begin(), rules2.locVars.end());
                rules2.body = ufo::eliminateQuantifiers(rules2.body, vars1);
                rules2.locVars.clear();
                
                // rules1.printMemberVars();
                // rules2.printMemberVars();

                auto rulesPr = ruleManager.chcs[cycle[0]];
                // rulesPr.printMemberVars();

                Expr var, var1;
                for (int l = 1; l < numItersOfLoop1; l++)
                {
                  for (int v = 0; v < rules1.srcVars.size(); v++)
                  {
                    var = mkTerm<string>("_pr_"+lexical_cast<string>(v)+"_"+lexical_cast<string>(l), m_efac);
                    var1 = rulesPr.dstVars[v];
                    
                    rules1.body = replaceAll(rules1.body, rules1.srcVars[v], var);
                    rules1.body = replaceAll(rules1.body, rules1.dstVars[v], var1);

                    rulesPr.body = replaceAll(rulesPr.body, rulesPr.dstVars[v], var);

                    rulesPr.locVars.push_back(var);
                  }
                  rulesPr.body = mk<AND>(rulesPr.body, rules1.body);
                }

                int rules1DeclSize = rules1.srcVars.size();

                for (int l = 1; l < numItersOfLoop2; l++)
                {
                  for (int v = 0; v < rules2.srcVars.size(); v++)
                  {
                    var = mkTerm<string>("_pr_"+lexical_cast<string>(rules1DeclSize+v)+"_"+lexical_cast<string>(l), m_efac);
                    var1 = rulesPr.dstVars[rules1DeclSize+v];
                    
                    rules2.body = replaceAll(rules2.body, rules2.srcVars[v], var);
                    rules2.body = replaceAll(rules2.body, rules2.dstVars[v], var1);

                    rulesPr.body = replaceAll(rulesPr.body, rulesPr.dstVars[rules1DeclSize+v], var);

                    rulesPr.locVars.push_back(var);
                  }
                  rulesPr.body = mk<AND>(rulesPr.body, rules2.body);
                }

                errs() << "\nupdated HornRuleExt: \n";
                ExprSet vars2(rulesPr.locVars.begin(), rulesPr.locVars.end());
                rulesPr.body = ufo::eliminateQuantifiers(rulesPr.body, vars2);
                rulesPr.locVars.clear();

                rulesPr.printMemberVars();

                // if (itersGrow[invNum][iter1]) errs() << *iter1 << " grows\n";
                // if (itersGrow[invNum][iter2]) errs() << *iter2 << " grows\n";

                // in case model is not initialized, it should be the initial values of vars
                if (model)
                {
                  Expr res1, res2, cond;
                  Expr modelRepl = replaceAll(model, hr.dstVars, hr.srcVars);
                  // errs() << "model: " << *modelRepl << "\n";

                  findExpr<EQ>(iter1, modelRepl, res1);
                  findExpr<EQ>(iter2, modelRepl, res2);

                  res1 = ineqSimplifier(iter1, res1);
                  res2 = ineqSimplifier(iter2, res2);

                  if (itersGrow[invNum][iter1]) cond = mk<GEQ>(iter1, res1->right());
                  else cond = mk<LEQ>(iter1, res1->right());
                  if (itersGrow[invNum][iter2]) cond = mk<AND>(cond, mk<GEQ>(iter2, res2->right()));
                  else cond = mk<AND>(cond, mk<LEQ>(iter2, res2->right()));

                  errs() << "\ncond is: " << *cond << "\n";

                  
                }
              }
              break;
            }
          }
        }

      }
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
          // errs() << "\ncands considered:\n";
          // for (auto it : candidatesTmp[ind])
          //   errs() << *it << "\n";
          Expr model = u.getModel(hr.dstVars);
          errs() << "\nmodel: " << *model << "\n";
          if (isSkippable(model, hr.dstVars, candidatesTmp))
          {
            // something went wrong with z3. do aggressive weakening (TODO: try bruteforce):
            candidatesTmp[ind].clear();
            res2 = false;
          }
          else
          {
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
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands, map<Expr, ExprSet>& candsForPhi, bool analizeCode = true)
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

        if (analizeCode) sm.analizeCode(candsForPhi[invRel]);
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
      dl.initialize(dcl, true /*multipleLoops*/, 2, initVals);
      string filename("");
      if (fileIndex < behaviorfiles.size()) {
        filename = behaviorfiles[fileIndex];
        fileIndex++;
      }
      if (!dl.computeData(filename)) return;
      ExprSet tmp, tmp2;
      map<Expr, ExprVector> substs;
      (void)dl.computePolynomials(tmp);
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
      return !u.isSat(exprs);
    }

    bool checkCHC1 (HornRuleExt& hr, Expr assump, ExprSet& annotations)
    {
      outs()  << "CHECKING " << * hr.srcRelation << " -> "<< * hr.dstRelation << "\n";
      ExprSet exprs;
      exprs.insert(hr.body);
      exprs.insert(assump);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
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
      errs() << *conjoin(exprs, m_efac) << "\n";
      return !u.isSat(exprs);
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

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(&ruleManager.chcs[cycle[0]]);

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

    void getIters(BndExpl& bnd, int cycleNum)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      Expr rel = ruleManager.chcs[cycle[0]].srcRelation;
      Expr rel1 = ruleManager.productRelsToSrcDst[rel][0];

      ruleManager.chcSrc->getDecl(rel1, rel1);
      int rel1DeclSize = rel1->arity() - 2;

      int invNum = getVarIndex(rel, decls);
      iters[cycleNum] = vector<ExprVector>{ExprVector(), ExprVector()};
      nonIters[cycleNum] = vector<ExprVector>{ExprVector(), ExprVector()};

        errs() << *ssas[invNum] << "\n";
      for (int i = 0; i < bnd.bindVars.back().size(); i++)
      {
        Expr e, gt, ge, lt, le, limit;
        Expr a = ruleManager.chcs[cycle[0]].srcVars[i];
        Expr b = bnd.bindVars.back()[i];
        // errs() << "checking: " << *b << "\n";
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        if (u.implies(ssas[invNum], mk<GT>(a, b)))
        {
          findExpr<EQ>(b, ssas[invNum], e);
          // errs() << "\nfinding: " << *b << "\n\n";
          // handle the case where e is a conjunction or disjunction
          e = ineqSimplifier(b, e);
          // errs() << "found: " << *e << "\n\n";

          Expr right = e->right();
          Expr init, initVal;
          int minusOrDiv = 0;
          bool simpleRelation = false;
          cpp_int initValNumeric, transitionValNumeric, numIters = 0, diff;

          if (isOpX<PLUS>(right)) minusOrDiv = 1;  
          else if (isOpX<MULT>(right)) minusOrDiv = 2;

          if (isIntConst(right->arg(0)) && isNumericConst(right->arg(1)))
          {
            init = bnd.compactPrefix(cycleNum);
            findExpr<EQ>(right->arg(0), init, initVal);
            initVal = ineqSimplifier(right->arg(0), initVal);
            // errs() << "init: " << *initVal << "\n";
            if (initVal && isNumericConst(initVal->right())) 
            {
              initValNumeric = lexical_cast<cpp_int>(initVal->right());
              simpleRelation = true;
            }
            transitionValNumeric = lexical_cast<cpp_int>(right->arg(1));
          }

          findExpr<GT>(a, ssas[invNum], gt);
          findExpr<GEQ>(a, ssas[invNum], ge);
          // findExpr<LT>(a, ssas[invNum], lt);
          // findExpr<LEQ>(a, ssas[invNum], le);

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
          if (limit && isNumericConst(limit))
          {
            cpp_int limitValNumeric = lexical_cast<cpp_int>(limit);
            // cout << "limitValNumeric: " << limitValNumeric << "\n";

            if (minusOrDiv == 1 && simpleRelation)
            {
              // cout << "initial val: " << initValNumeric << "\n";
              // cout << "transition val: " << transitionValNumeric << "\n";
              // cout << "final val: " << limitValNumeric << "\n";
              diff = abs(limitValNumeric - initValNumeric);
              if (ge) diff++;
              numIters = diff/abs(transitionValNumeric);
              cout << "numIters: " << numIters << "\n";
            }
            else if (minusOrDiv == 2 && simpleRelation)
            {

            }
          }
          else if (limit && isIntConst(limit))
          {
            // errs() << "intConst: " << *limit << "\n";
          }

          // if (lt) errs() << "lt: " << *lt << "\n";
          // if (le) errs() << "le: " << *le << "\n";

          if (i < rel1DeclSize) 
          {
            iters[cycleNum][0].push_back(a);
          }
          else 
          {
            iters[cycleNum][1].push_back(a);
          }
          itersGrow[cycleNum][a] = false;
          numOfIters[cycleNum][a] = numIters;
        }
        else if (u.implies(ssas[invNum], mk<LT>(a, b)))
        {
          findExpr<EQ>(b, ssas[invNum], e);
          // errs() << "\nfinding: " << *b << "\n\n";
          // handle the case where e is a conjunction or disjunction
          e = ineqSimplifier(b, e);
          // errs() << "found: " << *e << "\n\n";

          Expr right = e->right();
          Expr init, initVal;
          int plusOrMult = 0;
          bool simpleRelation = false;
          cpp_int initValNumeric, transitionValNumeric, numIters = 0, diff;

          if (isOpX<PLUS>(right)) plusOrMult = 1;  
          else if (isOpX<MULT>(right)) plusOrMult = 2;

          if (isIntConst(right->arg(0)) && isNumericConst(right->arg(1)))
          {
            init = bnd.compactPrefix(cycleNum);
            findExpr<EQ>(right->arg(0), init, initVal);
            initVal = ineqSimplifier(right->arg(0), initVal);
            if (initVal && isNumericConst(initVal->right())) 
            {
              initValNumeric = lexical_cast<cpp_int>(initVal->right());
              simpleRelation = true;
            }
            transitionValNumeric = lexical_cast<cpp_int>(right->arg(1));
          }
          findExpr<LT>(a, ssas[invNum], lt);
          findExpr<LEQ>(a, ssas[invNum], le);

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
          if (limit && isNumericConst(limit))
          {
            // errs() << "limit: " << *limit << "\n";
            cpp_int limitValNumeric = lexical_cast<cpp_int>(limit);
            // cout << "limitValNumeric: " << limitValNumeric << "\n";

            if (plusOrMult == 1 && simpleRelation)
            {
              // cout << "initial val: " << initValNumeric << "\n";
              // cout << "transition val: " << transitionValNumeric << "\n";
              // cout << "final val: " << limitValNumeric << "\n";
              diff = limitValNumeric - initValNumeric;
              if (le) diff++;
              numIters = diff/transitionValNumeric;
              cout << "numIters: " << numIters << "\n";
            }
            else if (plusOrMult == 2 && simpleRelation)
            {

            }
          }
          else if (limit && isIntConst(limit))
          {
            // errs() << "intConst: " << *limit << "\n";
          }

          if (i < rel1DeclSize) 
          {
            iters[cycleNum][0].push_back(a);
          }
          else 
          {
            iters[cycleNum][1].push_back(a);
          }
          itersGrow[cycleNum][a] = true;
          numOfIters[cycleNum][a] = numIters;
        }
        else 
        {
          if (i < rel1DeclSize)
              nonIters[cycleNum][0].push_back(a);
          else
              nonIters[cycleNum][1].push_back(a);
        }
      }
    }

    void printSolution(bool simplify = true)
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        ExprSet lms = sf.learnedExprs;

        ExprVector v(lms.begin(), lms.end());
        candidatesBackUp[i] = v;
        
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
    map<Expr, ExprSet> cands, candsForPhi;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      cands[ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation].insert(pref);
      //if (ruleManager.hasArrays)
      ds.initArrayStuff(bnd, i, pref);
      ds.getIters(bnd, i);
    }

//     if (enableDataLearning) {
// #ifdef HAVE_ARMADILLO
//       ds.getDataCandidates(cands, behaviorfiles);
// #else
//       outs() << "Skipping learning from data as required library (armadillo) not found\n";
// #endif
//     }

//     candsForPhi = cands;



    errs() << "\n\n";
    for (auto it : cands)
    {
      errs() << "cand: " << *it.first << "\n";
      for (auto it2 : it.second)
        errs() << *it2 << " ";
      errs() << "\n";
    }
    errs() << "\n\n";

    for (auto& dcl: ruleManager.wtoDecls) {
      ds.getSeeds(dcl, cands, candsForPhi);
//       errs() << "\n\ncands for phi\n";
//       for (auto it : candsForPhi[dcl])
//         errs() << *it << "\t";
//       errs() << "\n";
    }
    ds.refreshCands(cands);

//   errs() << "\n\n";
//     for (auto it : cands)
//     {
//       errs() << "cand: " << *it.first << "\n";
//       for (auto it2 : it.second)
//         errs() << *it2 << "\n";
//       errs() << "\n";
//     }
//     errs() << "\n\n";  

    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();
    // if (ds.bootstrap()) return;
    bool check = ds.bootstrap();
    ds.alignment(behaviorfiles);
    // if (check) return;
//     std::srand(std::time(0));
//     ds.synthesize(maxAttempts, c);
  }
}

#endif
