#ifndef HORN__HPP__
#define HORN__HPP__

#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  template <typename T>
  void concatenateVectors(vector<T> &result, vector<T> vec1, vector<T> vec2)
  {
    result.reserve(result.size()+vec1.size()+vec2.size());
    result.insert(result.end(), vec1.begin(), vec1.end());
    result.insert(result.end(), vec2.begin(), vec2.end());
  }

  template <typename T>
  void setUnion(set<T> &result, set<T> set1, set<T> set2)
  {
    result = set1;
    result.insert(set2.begin(), set2.end());
  }

  template <typename T, typename T1>
  void concatenateMaps(map<T, T1> &result, map<T, T1> map1, map<T, T1> map2)
  {
    result = map1;
    result.insert(map2.begin(), map2.end());
  }

  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    Expr srcRelation;
    Expr dstRelation;

    ExprMap repls;

    bool isFact;
    bool isQuery;
    bool isInductive;

    // possibly, add an option to detect multiple srcRelations

    void assignVarsAndRewrite (ExprVector& _srcVars, ExprVector& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        srcVars.push_back(invVarsSrc[i]);
        body = mk<AND>(body, mk<EQ>(_srcVars[i], srcVars[i]));
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }


    void printMemberVars()
    {
      errs() << "\nStarting to print a HornRuleExt: \n";
      errs() << "body: " << *body << "\n";
      errs() << "head: " << *head << "\n";

      errs() << "srcVars: ";
      for (auto it = srcVars.begin(); it != srcVars.end(); it++)
        errs() << **it << " ";
      errs() << "\n";

      errs() << "dstVars: ";
      for (auto it = dstVars.begin(); it != dstVars.end(); it++)
        errs() << **it << " ";
      errs() << "\n";

      errs() << "locVars: ";
      for (auto it = locVars.begin(); it != locVars.end(); it++)
        errs() << **it << " ";
      errs() << "\n";

      errs() << "srcRelation: " << *srcRelation << "\n";
      errs() << "dstRelation: " << *dstRelation << "\n";
      errs() << "isFact: " << isFact << "\n";
      errs() << "isQuery: " << isQuery << "\n";
      errs() << "isInductive: " << isInductive << "\n";
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname;

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> wtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> outgs;
    vector<vector<int>> prefixes;  // for cycles
    vector<vector<int>> cycles;
    map<Expr, bool> hasArrays;
    map<Expr, int> iterator;

    CHCs *chcSrc;
    CHCs *chcDst;
    map<Expr, ExprVector> productRelsToSrcDst;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3), varname("_FH_") {};
    CHCs(ExprFactory &efac, EZ3 &z3, string n) : m_efac(efac), m_z3(z3), varname(n) {};

    CHCs(CHCs &rules1, CHCs &rules2, string n) : m_efac(rules1.m_efac), m_z3(rules1.m_z3), varname(n), chcSrc(&rules1), chcDst(&rules2) 
    {
      setUnion(decls, rules1.decls, rules2.decls);
      concatenateVectors(chcs, rules1.chcs, rules2.chcs);
      concatenateMaps(invVars, rules1.invVars, rules2.invVars);
    };

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }

    void getDecl(Expr relation, Expr &relationDecl)
    {
      if (isFdecl(relation)) 
      {
        relationDecl = relation;
        return;
      }
      for (auto it = decls.begin(); it != decls.end(); it++)
      {
        if ((*it)->arg(0) == relation)
        {
          relationDecl = *it;
          return;
        }
      }
    }

    void removeDecl(Expr relation)
    {
      Expr decl;
      ExprSet::iterator it;
      if (!isOpX<TRUE>(relation))
      {
        getDecl(relation, decl);
        it = decls.find(decl);
        if (it != decls.end()) 
          decls.erase(it);
      }
    }

    void rulesOfPredicate(Expr &predicateDecl, vector<HornRuleExt> &rulesOfP)
    {
      for (auto it = chcs.begin(); it != chcs.end(); it++)
      {
          if (predicateDecl == it->head || predicateDecl == it->dstRelation)
          {
            rulesOfP.push_back(*it);
          }
      }
    }

    void preprocess (Expr term, ExprVector& srcVars, Expr &srcRelation, ExprSet& lin)
    {
      if (isOpX<AND>(term))
      {
        for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
        {
          preprocess(*it, srcVars, srcRelation, lin);
        }
      }
      else
      {
        if (bind::isBoolConst(term))
        {
          lin.insert(term);
        }
        if (isOpX<FAPP>(term) && isOpX<FDECL>(term->arg(0)))
        {
          Expr rel = term->arg(0);
          renameFdecl(rel); // added to rename rel fdecl
          if (find(decls.begin(), decls.end(), rel) != decls.end())
                // GF: the last requirement might be too restrictive: a rule with
                //     the term->arg(0) in the head should already be encountered
                // AH: moved this if-condition separate from previous if-condition
                //      in order to support renaming fdecls; does the same thing 
                //      except it renames the rel
          {
            if (srcRelation != NULL)
            {
              outs() << "Nonlinear CHCs are currently unsupported:\n   ";
              outs () << *srcRelation << " /\\ " << *rel->arg(0) << "\n";
              exit(0);
            }
            srcRelation = rel->arg(0);
            for (auto it = term->args_begin()+1, end = term->args_end(); it != end; ++it)
              srcVars.push_back(*it);

          }
        }
        else
        {
          lin.insert(term);
        }
      }
    }

    void renameFdecl(Expr &fdecl)
    {
      Expr name;
      ExprVector args;
      if (isOpX<FDECL>(fdecl))
      {
        name = mkTerm<string> (varname + lexical_cast<string>(fdecl->arg(0)), m_efac);
        for (auto it = fdecl->args_begin()+1; it != fdecl->args_end(); it++)
        {
          args.push_back(*it);
        }
        fdecl = bind::fdecl(name, args);
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->arg(0)].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(i - 1), m_efac);
          Expr var = a->arg(i);
          if (isOpX<INT_TY> (var))
            var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (var))
            var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (var))
            var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (var))
            var = bind::mkConst(new_name, sort::arrayTy(var->left(), var->right()));
          else if (isOpX<BVSORT> (var))
            var = bv::bvConst(new_name, bv::width(var));
          else assert(0);
          invVars[a->arg(0)].push_back(var);
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      Expr localVar;
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          // AH: modified code to add version name to local vars
          localVar = r->arg(i);
          renameFdecl(localVar); // renaming local vars according to version
          hr.repls[r->arg(i)] = localVar;
          hr.locVars.push_back(bind::fapp(localVar));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++) 
        {
          // AH: modified code to add version name to local vars
          localVar = r->first()->arg(i);
          renameFdecl(localVar); // renaming local vars according to version
          hr.repls[r->first()->arg(i)] = localVar;
          hr.locVars.push_back(bind::fapp(localVar));
        }

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    void parse(string smt)
    {
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      Expr decl;

      for (auto &r: fp.m_rules)
      {
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        Expr body = r->arg(0);
        Expr head = r->arg(1);

        ExprVector origSrcSymbs;
        ExprSet lin;
        preprocess(body, origSrcSymbs, hr.srcRelation, lin);
        if (hr.srcRelation == NULL)
        {
          if (hasUninterp(body))
          {
            outs () << "Unsupported format\n";
            outs () << "   " << *body << "\n";
            exit (0);
          }
          hr.srcRelation = mk<TRUE>(m_efac);
        }

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        if (isOpX<FAPP>(head))
        {
          decl = head->arg(0);
          renameFdecl(decl);
          if (decl->arity() == 2 && !hr.isFact)
          {
            addFailDecl(decl->arg(0));
          }
          else
          {
            addDecl(decl);
          }
          hr.head = decl;
          hr.dstRelation = hr.head->arg(0);
        }
        else
        {
          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }

        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        ExprVector allOrigSymbs = origSrcSymbs;
        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = head->args_begin()+1, end = head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
        }
        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());

        simplBoolReplCnj(allOrigSymbs, lin);
        hr.body = conjoin(lin, m_efac);
        hr.assignVarsAndRewrite (origSrcSymbs, invVars[hr.srcRelation],
                                 origDstSymbs, invVars[hr.dstRelation]);
        if (!hr.isQuery) hr.body = simpleQE(hr.body, hr.locVars);
        hr.body = replaceAll(hr.body, hr.repls); // replaces all variable names in the body
        print(hr);
      }

      // remove useless rules
//      if (failShrink(failDecl))
//        for (auto rit = indeces.rbegin(); rit != indeces.rend(); ++rit)
//          chcs.erase(chcs.begin() + *rit);

//      indeces.clear();
//      chcSliceBwd(failDecl);
//      vector<HornRuleExt> tmpChcs;
//      for (auto i : indeces) tmpChcs.push_back(chcs[i]);
//      chcs = tmpChcs;
      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      // sort rules
     wtoSort();
     print();
      outs () << " = = = parsing done\n";
    }

    bool failShrink (Expr dstRel)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].dstRelation != dstRel) continue;

        ExprSet quantified;
        quantified.insert(chcs[i].dstVars.begin(), chcs[i].dstVars.end());
        quantified.insert(chcs[i].locVars.begin(), chcs[i].locVars.end());
        Expr tmp = chcs[i].body;

         // current limitations
        if (findNonlin(tmp) || containsOp<IDIV>(tmp) || containsOp<MOD>(tmp)) return false;

        if (quantified.size() > 0)
        {
          AeValSolver ae(mk<TRUE>(m_efac), tmp, quantified);
          ae.solve();
          tmp = ae.getValidSubset();
        }

        if (isOpX<TRUE>(tmp))
        {
          failShrink(chcs[i].srcRelation);
          indeces.insert(i);
          return true;
        }
      }
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].dstRelation == dstRel)
        {
          chcs[i].isQuery = true;
          chcs[i].dstRelation = failDecl;
        }
      }
      return true;
    }

    void chcSliceBwd (Expr dstRel)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].dstRelation == dstRel)
        {
          bool alreadyIn = find(indeces.begin(), indeces.end(), i) != indeces.end();
          indeces.insert(i);
          if (!alreadyIn) chcSliceBwd(chcs[i].srcRelation);
        }
      }
      chcSliceFwd (dstRel);
    }

    void chcSliceFwd (Expr srcRel)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].srcRelation == srcRel)
        {
          bool alreadyIn = find(indeces.begin(), indeces.end(), i) != indeces.end();
          indeces.insert(i);
          if (!alreadyIn) chcSliceFwd(chcs[i].dstRelation);
        }
      }
    }

    bool hasCycles()
    {
      if (cycles.size() > 0) return true;

      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].isFact) findCycles(i, vector<int>());
      }

      assert (cycles.size() == prefixes.size());
//      for (auto & c : cycles)
//      {
//        outs () << "   cycle: ";
//        for (auto & chcNum : c) outs () << *chcs[chcNum].srcRelation << " -> ";
//        outs () << "    [";
//        for (auto & chcNum : c) outs () << chcNum << " -> ";
//        outs () << "]\n";
//      }
      return (cycles.size() > 0);
    }

    void findCycles(int chcNum, vector<int> vec)
    {
      Expr srcRel = chcs[chcNum].srcRelation;
      Expr dstRel = chcs[chcNum].dstRelation;
      bool res = false;
      for (int i = 0; i < vec.size(); i++)
      {
        auto c = vec[i];
        bool newCycle = (chcs[c].srcRelation == srcRel);
        // TODO: some cycles can be redundant
        if (newCycle)
        {
          cycles.push_back(vector<int>());
          prefixes.push_back(vector<int>());
          for (int j = 0; j < i; j++) prefixes.back().push_back(vec[j]);
          res = true;
        }
        if (res)
        {
          cycles.back().push_back(c);
        }
      }

      if (! res)
      {
        vec.push_back(chcNum);

        for (auto & i : outgs[dstRel])
        {
          if (chcs[i].dstRelation == failDecl) continue;
          bool newRel = true;
          for (auto & c : cycles)
          {
            if (c[0] == i)
            {
              newRel = false;
              break;
            }
          }
          if (newRel) findCycles(i, vec);
        }
      }
    }

    void getCycleForRel(Expr rel, vector<int>& cycle)
    {
      for (auto & c : cycles)
      {
        if (chcs[c[0]].srcRelation == rel)
        {
          cycle.insert(std::end(cycle), c.begin(), c.end());
          return;
        }
      }
    }

    HornRuleExt* getNestedRel (Expr rel)
    {
      vector<int> cycle;
      getCycleForRel(rel, cycle);
      if (cycle.size() > 0 && !chcs[cycle[0]].isInductive)
        return &chcs[cycle[0]];
      else
        return NULL;
    }

    HornRuleExt* getFirstRuleOutside (Expr rel)
    {
      for (auto & c : cycles)
      {
        if (chcs[c[0]].srcRelation == rel)
        {
          for (auto & a : outgs[rel])
          {
            if (a != c.back()) return &chcs[a];
          }
        }
      }
      return NULL;
    }

    void addRule (HornRuleExt* r)
    {
      chcs.push_back(*r);
      Expr srcRel = r->srcRelation;
      if (!isOpX<TRUE>(srcRel))
      {
        if (invVars[srcRel].size() == 0)
        {
          addDeclAndVars(srcRel, r->srcVars);
        }
      }
      outgs[srcRel].push_back(chcs.size()-1);
    }

    void addDeclAndVars(Expr rel, ExprVector& args)
    {
      ExprVector types;
      for (auto &var: args) {
        types.push_back (bind::typeOf (var));
      }
      types.push_back (mk<BOOL_TY> (m_efac));

      decls.insert(bind::fdecl (rel, types));
      for (auto & v : args)
      {
        invVars[rel].push_back(v);
      }
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          outs () << "Multiple queries are unsupported\n";
          exit(0);
        }
      }
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(simpleQE(hr->body, hr->dstVars), cnjs);
      for (auto &a : cnjs)
        if (emptyIntersect(a, hr->dstVars) && emptyIntersect(a, hr->locVars))
          newCnjs.insert(a);

      return conjoin(newCnjs, m_efac);
    }

    Expr getPrecondition (Expr decl)
    {
      for (auto &a : chcs)
        if (a.srcRelation == decl->left() && a.dstRelation == decl->left())
          return getPrecondition(&a);
      return mk<TRUE>(m_efac);
    }

    void wtoSort()
    {
      hasCycles();
      if (wtoCHCs.size() > 0)
      {
        outs () << "Already sorted\n";
        return;
      }

      int r1 = 0;

      for (auto & c : cycles)
      {
        unique_push_back(chcs[c[0]].srcRelation, wtoDecls);
        for (int i = 1; i < c.size(); i++)
        {
          unique_push_back(chcs[c[i]].dstRelation, wtoDecls);
          unique_push_back(&chcs[c[i]], wtoCHCs);
        }
      }

      int r2 = wtoDecls.size();
      if (r2 == 0) return;

      while (r1 != r2)
      {
        for (int i = r1; i < r2; i++)
        {
          auto dcl = wtoDecls[i];
          for (auto &hr : chcs)
          {
            if (find(wtoCHCs.begin(), wtoCHCs.end(), &hr) != wtoCHCs.end()) continue;

            if (hr.srcRelation == dcl)
            {
              unique_push_back(hr.dstRelation, wtoDecls);
              unique_push_back(&hr, wtoCHCs);
            }
            else if (hr.dstRelation == dcl)
            {
              unique_push_back(hr.srcRelation, wtoDecls);
              unique_push_back(&hr, wtoCHCs);
            }
          }
        }
        r1 = r2;
        r2 = wtoDecls.size();
      }

      assert(wtoCHCs.size() == chcs.size());

      // filter wtoDecls
      for (auto it = wtoDecls.begin(); it != wtoDecls.end();)
      {
        if (*it == failDecl || isOpX<TRUE>(*it)) it = wtoDecls.erase(it);
        else ++it;
      }
    }

    // Transformations

    void mergeIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      Expr pre = getPrecondition(decl);
      ExprSet newCnjs;
      newCnjs.insert(mk<NEG>(pre));
      for (int i = 0; i < hr->srcVars.size(); i++)
      {
        newCnjs.insert(mk<EQ>(hr->dstVars[i], hr->srcVars[i]));
      }
      Expr body2 = conjoin(newCnjs, m_efac);

      // adaping the code from BndExpl.hpp
      ExprVector ssa;
      ExprVector bindVars1;
      ExprVector bindVars2;
      ExprVector newLocals;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int c = 0; c < num; c++)
      {
        Expr body = hr->body;
        bindVars2.clear();
        if (c != 0)
        {
          body = replaceAll(mk<OR>(body, body2), hr->srcVars, bindVars1);
          for (int i = 0; i < hr->locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr->locVars[i], new_name);
            body = replaceAll(body, hr->locVars[i], var);
            newLocals.push_back(var);
          }
        }

        if (c != num-1)
        {
          for (int i = 0; i < hr->dstVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr->dstVars[i], new_name));
            body = replaceAll(body, hr->dstVars[i], bindVars2[i]);
            newLocals.push_back(bindVars2[i]);
          }
        }
        ssa.push_back(body);
        bindVars1 = bindVars2;
      }
      hr->body = conjoin(ssa, m_efac);
      hr->locVars.insert(hr->locVars.end(), newLocals.begin(), newLocals.end());
    }

    void slice (Expr decl, ExprSet& vars)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr->body, cnjs);
      map <Expr, ExprSet> deps;

      for (auto &a : cnjs)
      {
        ExprSet cnj_vars;
        ExprSet cnj_vars_cmpl;
        expr::filter (a, bind::IsConst(), std::inserter (cnj_vars, cnj_vars.begin ()));
        for (auto & a : cnj_vars)
        {
          int index = getVarIndex(a, hr->srcVars);
          if (index >= 0)
          {
            cnj_vars_cmpl.insert(hr->dstVars[index]);
            continue;
          }
          index = getVarIndex(a, hr->dstVars);
          if (index >= 0)
          {
            cnj_vars_cmpl.insert(hr->srcVars[index]);
          }
        }
        cnj_vars.insert(cnj_vars_cmpl.begin(), cnj_vars_cmpl.end());
        deps[a] = cnj_vars;
      }

      while (vars.size() > 0)
      {
        for (auto vit = vars.begin(); vit != vars.end(); )
        {
          for (auto cit = cnjs.begin(); cit != cnjs.end(); )
          {
            ExprSet& d = deps[*cit];
            if (find(d.begin(), d.end(), *vit) != d.end())
            {
              newCnjs.insert(*cit);
              cit = cnjs.erase(cit);
              vars.insert(d.begin(), d.end());
            }
            else
            {
              ++cit;
            }
          }
          vit = vars.erase (vit);
        }
      }
      hr->body = conjoin(newCnjs, m_efac);
    }

    bool checkWithSpacer()
    {
      bool success = false;

      // fixed-point object
      ZFixedPoint<EZ3> fp (m_z3);
      ZParams<EZ3> params (m_z3);
      params.set (":engine", "spacer");
      params.set (":xform.slice", false);
      params.set (":pdr.utvpi", false);
      params.set (":use_heavy_mev", true);
      params.set (":xform.inline-linear", false);
      params.set (":xform.inline-eager", false);
      params.set (":xform.inline-eager", false);

      fp.set (params);

      fp.registerRelation (bind::boolConstDecl(failDecl));

      for (auto & dcl : decls) fp.registerRelation (dcl);
      Expr errApp;

      for (auto & r : chcs)
      {
        ExprSet allVars;
        allVars.insert(r.srcVars.begin(), r.srcVars.end());
        allVars.insert(r.dstVars.begin(), r.dstVars.end());
        allVars.insert(r.locVars.begin(), r.locVars.end());

        if (!r.isQuery)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.dstRelation)
            {
              r.head = bind::fapp (dcl, r.dstVars);
              break;
            }
          }
        }
        else
        {
          r.head = bind::fapp(bind::boolConstDecl(failDecl));
          errApp = r.head;
        }

        Expr pre;
        if (!r.isFact)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.srcRelation)
            {
              pre = bind::fapp (dcl, r.srcVars);
              break;
            }
          }
        }
        else
        {
          pre = mk<TRUE>(m_efac);
        }

        fp.addRule(allVars, boolop::limp (mk<AND>(pre, r.body), r.head));
      }
      try {
        success = bool(!fp.query(errApp));
      } catch (z3::exception &e){
        char str[3000];
        strncpy(str, e.msg(), 300);
        outs() << "Z3 ex: " << str << "...\n";
        exit(55);
      }
      return success;
    }

    void print()
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs){
        print(hr);
      }
    }

    void print(HornRuleExt& hr)
    {
//      outs() << "CHCs:\n";
//      for (auto &hr: chcs)
      {
//        if (hr.isFact) outs() << "  INIT:\n";
//        if (hr.isInductive) outs() << "  LOOP:\n";
//        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    " << * hr.srcRelation;
        if (hr.srcVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.srcVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs () << " -> " << * hr.dstRelation ;

        if (hr.dstVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.dstVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs () << "\n";
//        outs() << "\n    body: " << * hr.body << "\n";
      }
    }
  };
}


#endif
