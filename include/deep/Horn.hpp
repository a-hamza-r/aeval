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

  template <typename T>
    void findExpr(Expr toFind, Expr conj, Expr &result, bool skipArray=false)
    {
      Expr res;
      if (isOpX<AND>(conj))
      {
        for (auto it = conj->args_begin(); it != conj->args_end(); it++)
        {
          findExpr<T>(toFind, *it, res, skipArray);
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
          findExpr<T>(toFind, *it, res, skipArray);
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
      {
        if (skipArray && containsOp<ARRAY_TY>(conj)) return;
        if (contains(conj, toFind)) result = conj;
      }
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

    bool isFact;
    bool isQuery;
    bool isInductive;

    bool subRelationsBothInductive;

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
        dstVars.push_back(invVarsDst[i]);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }

    void printMemberVars()
    {
      outs() << "\nStarting to print a HornRuleExt: \n";
      outs() << "body: " << *body << "\n";
      outs() << "head: " << *head << "\n";

      outs() << "srcVars: ";
      for (auto it = srcVars.begin(); it != srcVars.end(); it++)
        outs() << **it << " ";
      outs() << "\n";

      outs() << "dstVars: ";
      for (auto it = dstVars.begin(); it != dstVars.end(); it++)
        outs() << **it << " ";
      outs() << "\n";

      outs() << "locVars: ";
      for (auto it = locVars.begin(); it != locVars.end(); it++)
        outs() << **it << " ";
      outs() << "\n";

      outs() << "srcRelation: " << *srcRelation << "\n";
      outs() << "dstRelation: " << *dstRelation << "\n";
      outs() << "isFact: " << isFact << "\n";
      outs() << "isQuery: " << isQuery << "\n";
      outs() << "isInductive: " << isInductive << "\n";
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname;
    SMTUtils u;

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> wtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars;
    map<Expr, ExprVector> invVarsPrime;
    map<Expr, vector<int>> outgs;
    vector<vector<int>> prefixes;  // for cycles
    vector<vector<int>> cycles;
    map<Expr, bool> hasArrays;
    map<Expr, int> iterator;
    bool hasAnyArrays;

    // assuming only one loop
    int iter;
    bool iterGrows;
    Expr numOfIters;
    vector<int> varsInt;
    vector<int> varsBool;
    vector<int> varsArray;
    map<Expr, Expr> exprEqualities;

    map<Expr, ExprVector> productRelsToSrcDst;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3), varname("_FH_"), u(efac) {};
    CHCs(ExprFactory &efac, EZ3 &z3, string n) : m_efac(efac), m_z3(z3), varname(n), u(efac) {};

    CHCs(CHCs &rules1, CHCs &rules2, string n) : 
      m_efac(rules1.m_efac), m_z3(rules1.m_z3), varname(n), u(rules1.m_efac) 
    {
      setUnion(decls, rules1.decls, rules2.decls);
      concatenateVectors(chcs, rules1.chcs, rules2.chcs);
      concatenateMaps(invVars, rules1.invVars, rules2.invVars);
    };

    string getVarName() {return varname;}

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->left()))
            if (e->left()->arity() >= 2)
              return true;
      return false;
    }

    Expr getDecl(Expr relation)
    {
      Expr relationDecl;
      if (isFdecl(relation)) 
      {
        relationDecl = relation;
        return relationDecl;
      }
      for (auto it = decls.begin(); it != decls.end(); it++)
      {
        if ((*it)->arg(0) == relation)
        {
          relationDecl = *it;
          return relationDecl;
        }
      }
    }

    void removeDecl(Expr relation)
    {
      Expr decl;
      ExprSet::iterator it;
      if (!isOpX<TRUE>(relation))
      {
        decl = getDecl(relation);
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

    void splitBody (Expr body, ExprVector& srcVars, Expr &srcRelation, ExprSet& lin)
    {
      getConj (body, lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        Expr rel = cnj->left();
        renameFdecl(rel);
        if (isOpX<FAPP>(cnj) && isOpX<FDECL>(rel) &&
            find(decls.begin(), decls.end(), rel) != decls.end())
        {
          if (srcRelation != NULL)
          {
            errs () << "Nonlinear CHCs are currently unsupported:\n   ";
            errs () << *srcRelation << " /\\ " << *rel->left() << "\n";
            exit(1);
          }
          srcRelation = rel->left();
          for (auto it = cnj->args_begin()+1, end = cnj->args_end(); it != end; ++it)
            srcVars.push_back(*it);
          c = lin.erase(c);
        }
        else ++c;
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
      if (invVars[a->left()].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(i - 1), m_efac);
          Expr var;
          if (isOpX<INT_TY> (a->arg(i)))
            var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (a->arg(i)))
            var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (a->arg(i)))
            var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (a->arg(i))) // GF: currently support only arrays over Ints
          {
            var = bind::mkConst(new_name, mk<ARRAY_TY>
                  (mk<INT_TY> (m_efac), mk<INT_TY> (m_efac)));
          }
          new_name = mkTerm<string> (lexical_cast<string>(var) + "'", m_efac);
          invVars[a->left()].push_back(var);
          invVarsPrime[a->left()].push_back(cloneVar(var, new_name));
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
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
        {
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));
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

    void renameVars(ExprVector& vars, Expr& body)
    {
      for (int i = 0; i < vars.size(); i++)
      {
        Expr decl = vars[i]->arg(0);
        renameFdecl(decl);
        body = replaceAll(body, bind::fapp(vars[i]->arg(0)), bind::fapp(decl));
        vars[i] = bind::fapp(decl);
      }
    }

    void parse(string smt, bool doElim = true)
    {
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        hr.body = r->left();
        hr.head = r->right();
        if (isOpX<FAPP>(hr.head))
        {
          Expr head = hr.head->left();
          renameFdecl(head);
          if (hr.head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), r->right()) !=
               fp.m_queries.end())) 
            addFailDecl(head->left());
          else 
            addDecl(head);
          hr.dstRelation = head->left();
        }
        else
        {
          if (!isOpX<FALSE>(hr.head)) hr.body = mk<AND>(hr.body, mk<NEG>(hr.head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }
      }

      // the second loop is needed because we want to distunguish
      // uninterpreted functions used as variables from relations to be synthesized
      for (auto & hr : chcs)
      {
        ExprVector origSrcSymbs;
        ExprSet lin;
        splitBody(hr.body, origSrcSymbs, hr.srcRelation, lin);
        if (hr.srcRelation == NULL)
        {
          if (hasUninterp(hr.body))
          {
            errs () << "Unsupported format\n";
            errs () << "   " << *hr.body << "\n";
            exit (1);
          }
          hr.srcRelation = mk<TRUE>(m_efac);
        }

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        ExprVector allOrigSymbs = origSrcSymbs;
        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = hr.head->args_begin()+1, end = hr.head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
          Expr head = hr.head->left();
          renameFdecl(head);
          hr.head = head;
        }

        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
        simplBoolReplCnj(allOrigSymbs, lin);
        hr.body = conjoin(lin, m_efac);

        hr.assignVarsAndRewrite (origSrcSymbs, invVars[hr.srcRelation],
                                 origDstSymbs, invVarsPrime[hr.dstRelation]);
        if (qeUnsupported(hr.body))
          hr.body = simpleQE(hr.body, hr.locVars);
        else
          hr.body = eliminateQuantifiers(hr.body, hr.locVars);

        // rename locVars according to the version
        renameVars(hr.locVars, hr.body);

        hr.body = u.removeITE(hr.body);
      }
      if (doElim) eliminateDecls();

      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      // sort rules
      wtoSort();
    }

    Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
    {
      auto &fac = init->getFactory();
      if (!(init && transition && final)) return mkMPZ(-1, fac);
      Expr numer = mk<MINUS>(final, init);
      // works this way
      if (add) numer = mk<PLUS>(numer, add);
      Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, fac));

      Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, fac), mkMPZ(1, fac)));
      // outs() << "numIters: " << *numIters << "\n";
      return numIters;
    }

    void getExprEqualities(Expr var, HornRuleExt& rule)
    {
      Expr body = rule.body;
      ExprSet s;
      Expr final;
      getConj(body, s);
      for (auto &e : s)
      {
        bool skip = false;
        if (contains(e, var) && !containsOp<ARRAY_TY>(e) && containsOp<EQ>(e))
        {
          ExprSet ss;
          filter(e, IsConst(), inserter(ss, ss.begin()));
          for (auto &it : ss)
          {
            if (find(rule.dstVars.begin(), rule.dstVars.end(), it) != rule.dstVars.end())
            {
              skip = true;
              break;
            }
          }
          if (skip) continue;
          else 
          { 
            if (final) final = mk<AND>(final, e);
            else final = e;
          }
        }
      }
      exprEqualities[var] = final;
    }

    bool findInitialValue(int i, HornRuleExt& initRule, HornRuleExt& rule, Expr &initVal)
    {
      Expr init = initRule.body;
      Expr iter = rule.dstVars[i];

      findExpr<EQ>(iter, init, initVal, true);
      if (initVal)
      {
        Expr newInit;
        // a hack to avoid mod operations
        if (isOpX<AND>(initVal))
        {
          ExprSet s;
          getConj(initVal, s);
          for (auto &it : s)
          {
            Expr normalized = ineqSimplifier(iter, simplifyArithm(it));
            if (isOpX<EQ>(normalized) && normalized->left() == iter)  
            {
              // if multiple equalities are found, just return; support more
              if (newInit) return false;
              else newInit = normalized;
            }
          }
          initVal = newInit;
        }
        if (initVal) 
        {
          // initVal = ineqSimplifier(iter, initVal);
          initVal = initVal->right();
          // assigns non-primed variables
          initVal = replaceAll(initVal, rule.dstVars, rule.srcVars);
          // outs() << "initVal: " << *initVal << "\n";
          return true;

          // use when local vars are not eliminated, so extra equalities need to be calculated
          // initVar is then the iterator
          /*getExprEqualities(initVar, rule);
          outs() << "exprEqualities for " << *initVar << ": " << *exprEqualities[initVar] << "\n";

          ExprSet s;
          filter(initVal, IsConst(), inserter(s, s.begin()));
          if (!s.empty())
          {
            // outs() << "var: " << **s.begin() << "\n";

            getExprEqualities(*s.begin(), rule);
            // outs() << "exprEqualities for " << **s.begin() << ": " << *exprEqualities[*s.begin()] << "\n";
          }*/

        }
      }
      return false;
    }

    bool findTransitionValue(int i, HornRuleExt& rule, Expr& transitionVal)
    {
      ExprSet allExprs;
      Expr allExprsConj, e;
      bool multipleTransVal = false;

      Expr a = rule.srcVars[i];
      Expr b = rule.dstVars[i];

      findExpr<EQ>(b, rule.body, e, true);
      // errs() << "\nfinding: " << *b << "\n\n";

      if (!e) return false;

      e = ineqSimplifier(b, e);
      // errs() << "found: " << *e << "\n\n";

      getConjAndDisj(e, allExprs);
      for (auto &it : allExprs)
      {
        if (contains(it, a)) 
        {
          if (allExprsConj) multipleTransVal = true;
          else allExprsConj = it;
        }
      }

      // Cases when transition can't be found: multiple transition rels, no transition rel, contains an ITE
      if (multipleTransVal || !allExprsConj || allExprsConj->right()->arity() <= 1 || containsOp<ITE>(allExprsConj)) 
        return false;

      Expr right = allExprsConj->right();

      // assuming no local vars
      if (right->arg(0) == a)
        transitionVal = right->arg(1);
      else 
        transitionVal = right->arg(0);

      // check if delta value is constant; Eq. 10, section 4 in paper
      Expr replacedTrans = replaceAll(transitionVal, rule.srcVars, rule.dstVars);
      if (!u.implies(rule.body, mk<EQ>(transitionVal, replacedTrans)))
      {
        transitionVal = NULL;
        return false;
      }

      // outs() << "transitionVal: " << *transitionVal << "\n";
      return true;
    }

    bool findFinalValue(int i, HornRuleExt& rule, Expr& limitVal, Expr& add, bool iterIncreases)
    {
      Expr a = rule.srcVars[i];
      Expr b = rule.dstVars[i];

      Expr limitEq;
      Expr gt, ge, lt, le;
      if (iterIncreases)
      {
        findExpr<LT>(a, rule.body, lt, true);
        findExpr<LEQ>(a, rule.body, le, true);

        // make sure there is no case where both lt and le are not null
        // cannot think of any but could be
        // in case lt and le are either conjunction or disjunction, handle better
        if (lt) 
        {
          lt = ineqSimplifier(a, lt);
          if (!(isOpX<AND>(lt) || isOpX<OR>(lt))) limitEq = lt;
        }
        if (le) 
        {
          add = mkMPZ(1, m_efac);
          le = ineqSimplifier(a, le);
          if (!(isOpX<AND>(le) || isOpX<OR>(le))) limitEq = le;
        }
      }
      else 
      {
        findExpr<GT>(a, rule.body, gt);
        findExpr<GEQ>(a, rule.body, ge);

        // make sure there is no case where both gt and ge are not null
        // cannot think of any but could be
        if (gt) 
        {
          gt = ineqSimplifier(a, gt);
          if (!(isOpX<AND>(gt) || isOpX<OR>(gt))) limitEq = gt;
        }
        if (ge) 
        {
          add = mkMPZ(-1, m_efac);
          ge = ineqSimplifier(a, ge);
          if (!(isOpX<AND>(ge) || isOpX<OR>(ge))) limitEq = ge;
        }
      }

      if (limitEq) 
      {
        limitVal = limitEq->arg(1);
        // outs() << "limitVal: " << *limitVal << "\n";

        // check if limit value is constant; Eq. 8, section 4
        Expr replacedLimit = replaceAll(limitVal, rule.srcVars, rule.dstVars);
        bool constLimitValCheck = u.implies(rule.body, mk<EQ>(limitVal, replacedLimit));
        
        // check the case that iter does not exceed limit value during transition; Eq. 7, section 4
        bool loopEndCheck = limitEq && !u.isSat(mk<AND>(mkNeg(limitEq), rule.body));

        if (!constLimitValCheck || !loopEndCheck)
        {
          limitVal = NULL;
          return false;
        }

        // s.clear();
        // filter(limitVal, IsConst(), inserter(s, s.begin()));
        // if (!s.empty())
        // {
          // outs() << "var: " << **s.begin() << "\n";
          // for (auto &it : s)
          //   getExprEqualities(it, rule);
          // outs() << "exprEqualities for " << **s.begin() << ": " << *exprEqualities[*s.begin()] << "\n";
        // }
        return true;
      }
      return false;
    }

    void findIterators()
    {
      // assuming only one cycle
      vector<int>& cycle = cycles[0];
      HornRuleExt& rule = chcs[cycle[0]];
      vector<int> &prefix = prefixes[0];
      HornRuleExt &prefixRule = chcs[prefix[0]];
      Expr rel = rule.srcRelation;

      int invNum = getVarIndex(rel, decls);

      for (int i = 0; i < rule.srcVars.size(); i++)
      {
        Expr a = rule.srcVars[i];
        Expr b = rule.dstVars[i];
        bool isAnIter = false;

        bool iterDecreases = bind::isIntConst(a) && u.implies(rule.body, mk<GT>(a, b));
        bool iterIncreases = bind::isIntConst(a) && u.implies(rule.body, mk<LT>(a, b));

        if (iterIncreases || iterDecreases)
        {
          Expr initVal, transitionVal, limitVal;
          Expr add;

          // AH: handle the case where it is iterator but any of values are not available
          bool hasInitVal = findInitialValue(i, prefixRule, rule, initVal);

          bool hasTransitionVal = findTransitionValue(i, rule, transitionVal);

          bool hasLimitVal = findFinalValue(i, rule, limitVal, add, iterIncreases);

          isAnIter = hasInitVal && hasTransitionVal && hasLimitVal;
          if (isAnIter)
          {
            iter = i;
          
            // if iter is increasing/decreasing
            iterGrows = iterIncreases;
            numOfIters = numIterations(initVal, transitionVal, limitVal, add);
          }
        }

        // if not an iter, collect info about the type of variables
        if (!isAnIter)
        {
          if (bind::isIntConst(a)) varsInt.push_back(i);
          else if (bind::isBoolConst(a)) varsBool.push_back(i);
          else if (isOpX<ARRAY_TY>(bind::typeOf(a))) varsArray.push_back(i);
        }
      }
    }

    void eliminateVacuous()
    {
      set<int> toErase;
      for (auto c = chcs.begin(); c != chcs.end(); ++c)
      {
        if (c->isQuery && u.isTrue(c->body) && !c->isFact)
        {
          // thus, c->srcRelation should be false
          for (int i = 0; i < chcs.size(); i++)
          {
            HornRuleExt* s = &chcs[i];
            if (s->srcRelation == c->srcRelation)
            {
              toErase.insert(i);  // could erase here, but ther will be a mess with pointers
            }
            else if (s->dstRelation == c->srcRelation)
            {
              s->isQuery = true;
              s->dstRelation = failDecl;
              s->locVars.insert(s->locVars.end(), s->dstVars.begin(), s->dstVars.end());
              s->dstVars.clear();
            }
          }
          decls.erase(c->srcRelation);
        }
      }

      if (toErase.empty()) return;

      for (auto it = toErase.rbegin(); it != toErase.rend(); ++it)
        chcs.erase(chcs.begin() + *it);

      eliminateVacuous();     // recursive call
    }

    void eliminateDecls()
    {
      int preElim = chcs.size();

      eliminateVacuous();         // first, remove relations which are trivially false

      for (auto d = decls.begin(); d != decls.end();)
      {
        vector<int> src, dst;

        for (int i = 0; i < chcs.size(); i++)
          if (chcs[i].srcRelation == (*d)->left()) src.push_back(i);

        for (int i = 0; i < chcs.size(); i++)
          if (chcs[i].dstRelation == (*d)->left()) dst.push_back(i);

        if (src.size() == 1 && dst.size() > 0 && emptyIntersect(src, dst))
        {
          // a predicate is used only as an intermediate node
          // TODO: consider merging also if src.size() > 0
          for (int i : src)
            for (int j : dst)
              mergeCHCs(&chcs[i], &chcs[j]);
          set<int> to_erase;
          to_erase.insert(src.begin(), src.end());
          to_erase.insert(dst.begin(), dst.end());
          for (auto a = to_erase.rbegin(); a != to_erase.rend(); ++a)
            chcs.erase(chcs.begin()+*a);
          d = decls.erase(d);
        }
        else if (src.size() == 0)
        {
          // remove dangling CHCs
          for (int i = dst.size()-1; i >= 0; i--)
            chcs.erase(chcs.begin()+dst[i]);
          d = decls.erase(d);
        }
        else ++d;
      }

      removeTautologies();            // get rid of CHCs that don't add any _new_ constraints
      if (preElim > chcs.size())
        eliminateDecls();
      else
      {
        if (!hasAnyArrays) slice();   // remove unrelated constraints and shrink arities of predicates

        int preComb = chcs.size();
        combineCHCs();
        if (preComb > chcs.size())
          eliminateDecls();
      }
    }

    void mergeCHCs(HornRuleExt* s, HornRuleExt* d)
    {
      HornRuleExt* n = new HornRuleExt();
      n->srcRelation = d->srcRelation;
      n->dstRelation = s->dstRelation;
      n->srcVars = d->srcVars;
      n->dstVars = d->dstVars;

      ExprVector newVars;
      for (int i = 0; i < d->dstVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(i), m_efac);
        newVars.push_back(cloneVar(d->dstVars[i], new_name));
      }

      Expr mergedBody = replaceAll(s->body, s->srcVars, newVars);
      n->dstVars.insert(n->dstVars.end(), d->locVars.begin(), d->locVars.end());
      for (int i = 0; i < d->locVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__loc_var_" + to_string(i), m_efac);
        newVars.push_back(cloneVar(d->locVars[i], new_name));
      }
      mergedBody = mk<AND>(replaceAll(d->body, n->dstVars, newVars), mergedBody);
      n->locVars = newVars;
      n->locVars.insert(n->locVars.end(), s->locVars.begin(), s->locVars.end());

      if (!qeUnsupported(mergedBody))
      {
        mergedBody = eliminateQuantifiers(mergedBody, n->locVars);
        n->locVars.clear();
      }

      n->body = mergedBody;
      n->dstVars = s->dstVars;
      n->isInductive = n->srcRelation == n->dstRelation;
      n->isFact = isOpX<TRUE>(n->srcRelation);
      n->isQuery = n->dstRelation == failDecl;
      chcs.push_back(*n);
    }

    void removeTautologies()
    {
      for (auto h = chcs.begin(); h != chcs.end(); )
      {
        if (u.isFalse(h->body))
        {
          h = chcs.erase(h);
          continue;
        }

        bool found = false;
        if (h->isInductive)
        {
          found = true;
          for (int i = 0; i < h->srcVars.size(); i++)
          {
            if (u.isSat(h->body, mkNeg(mk<EQ>(h->srcVars[i], h->dstVars[i]))))
            {
              found = false;
              break;
            }
          }
        }
        if (found) h = chcs.erase(h);
          else ++h;
      }
    }

    void combineCHCs()
    {
      for (int i = 0; i < chcs.size(); i++)
        for (int j = i + 1; j < chcs.size(); j++)
        {
          HornRuleExt& s = chcs[i];
          HornRuleExt& d = chcs[j];
          if (s.srcRelation == d.srcRelation && s.dstRelation == d.dstRelation)
          {
            for (int k = 0; k < s.srcVars.size(); k++) assert (s.srcVars[k] == d.srcVars[k]);
            for (int k = 0; k < s.dstVars.size(); k++) assert (s.dstVars[k] == d.dstVars[k]);

            // small optim:
            Expr tmp = distribDisjoin(s.body, d.body);

            s.body = tmp;
            chcs.erase(chcs.begin()+j);
            return combineCHCs();
          }
        }
    }

    // (recursive) multi-stage slicing begins here
    set<int> chcsToVisit;
    map<Expr, ExprSet> varsSlice;

    void updateTodo(Expr decl, int num)
    {
      for (int i = 0; i < chcs.size(); i++)
        if (i != num &&
            !chcs[i].isQuery &&
            (chcs[i].srcRelation == decl || chcs[i].dstRelation == decl))
              chcsToVisit.insert(i);
    }

    void slice()
    {
      chcsToVisit.clear();
      varsSlice.clear();
      // first, compute sets of dependent variables
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].isQuery)
        {
          chcs[i].body = keepQuantifiers(chcs[i].body, chcs[i].srcVars);
          Expr decl = chcs[i].srcRelation;
          expr::filter (chcs[i].body, bind::IsConst(),
            std::inserter (varsSlice[decl], varsSlice[decl].begin ()));
          updateTodo(chcs[i].srcRelation, i);
        }
      }
      while (!chcsToVisit.empty()) slice(*chcsToVisit.begin());

      // now, prepare for variable elimination
      for (auto & d : varsSlice)
      {
//        if (invVars[d.first].size() > d.second.size())
//          outs () << "sliced for " << *d.first << ": " << invVars[d.first].size()
//                  << " -> "    << d.second.size() << "\n";
        ExprSet varsPrime;
        for (auto & v : d.second)
        {
          Expr pr = replaceAll(v, invVars[d.first], invVarsPrime[d.first]);
          varsPrime.insert(pr);
        }

        keepOnly(invVars[d.first], d.second);
        keepOnly(invVarsPrime[d.first], varsPrime);
      }

      // finally, update bodies and variable vectors
      for (auto & c : chcs)
      {
        if (u.isFalse(c.body) || u.isTrue(c.body)) continue;

        ExprSet bd;
        getConj(c.body, bd);
        for (auto b = bd.begin(); b != bd.end();)
        {
          if (emptyIntersect(*b, invVars[c.srcRelation]) &&
              emptyIntersect(*b, invVarsPrime[c.dstRelation]))
            b = bd.erase(b);
          else ++b;
        }
        if (!c.isFact) c.srcVars = invVars[c.srcRelation];
        if (!c.isQuery) c.dstVars = invVarsPrime[c.dstRelation];
        c.body = conjoin(bd, m_efac);
      }
    }

    void slice(int num)
    {
      HornRuleExt* hr = &chcs[num];
      assert (!hr->isQuery);
      ExprSet srcCore, dstCore, srcDep, dstDep, varDeps, cnjs;

      if (qeUnsupported(hr->body))
      {
        varDeps.insert(hr->srcVars.begin(), hr->srcVars.end());
        varDeps.insert(hr->locVars.begin(), hr->locVars.end());
        varDeps.insert(hr->dstVars.begin(), hr->dstVars.end());
      }
      else
      {
        varDeps = varsSlice[hr->srcRelation];
        expr::filter (getPrecondition(hr), bind::IsConst(),     // all src vars from the preconditions are dependent
                      std::inserter (varDeps, varDeps.begin ()));

        for (auto & v : varsSlice[hr->dstRelation])
          varDeps.insert(replaceAll(v, invVars[hr->dstRelation], hr->dstVars));

        srcCore = varsSlice[hr->dstRelation];
        dstCore = varDeps;

        getConj(hr->body, cnjs);
        while(true)
        {
          int vars_sz = varDeps.size();
          for (auto & c : cnjs)
          {
            ExprSet varsCnj;
            expr::filter (c, bind::IsConst(),
                          std::inserter (varsCnj, varsCnj.begin ()));
            if (!emptyIntersect(varDeps, varsCnj))
              varDeps.insert(varsCnj.begin(), varsCnj.end());
          }
          if (hr->isInductive)
          {
            for (auto & v : varDeps)
            {
              varDeps.insert(replaceAll(v, hr->dstVars, hr->srcVars));
              varDeps.insert(replaceAll(v, hr->srcVars, hr->dstVars));
            }
          }
          if (vars_sz == varDeps.size()) break;
        }
      }

      bool updateSrc = false;
      bool updateDst = false;
      if (!hr->isFact)
      {
        ExprSet& srcVars = varsSlice[hr->srcRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->srcVars.begin(), hr->srcVars.end(), *v) != hr->srcVars.end())
          {
            if (find(srcVars.begin(), srcVars.end(), *v) == srcVars.end())
            {
              updateSrc = true;
              srcVars.insert(*v);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      srcDep = varsSlice[hr->srcRelation];
      dstDep = varDeps;

      if (!hr->isQuery)
      {
        ExprSet& dstVars = varsSlice[hr->dstRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->dstVars.begin(), hr->dstVars.end(), *v) != hr->dstVars.end())
          {
            Expr vp = replaceAll(*v, hr->dstVars, invVars[hr->dstRelation]);
            if (find(dstVars.begin(), dstVars.end(), vp) == dstVars.end())
            {
              updateDst = true;
              dstVars.insert(vp);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      if (!varDeps.empty() && qeUnsupported(hr->body))
        hr->body = eliminateQuantifiers(hr->body, varDeps);
      else {/*TODO*/}

      if (updateSrc) updateTodo(hr->srcRelation, num);
      if (updateDst) updateTodo(hr->dstRelation, num);
      chcsToVisit.erase(num);
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
          errs () << "Multiple queries are unsupported\n";
          exit (1);
        }
      }
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      return
        eliminateQuantifiers(
          eliminateQuantifiers(hr->body, hr->locVars), hr->dstVars);
//      ExprSet cnjs;
//      ExprSet newCnjs;
//      getConj(simpleQE(hr->body, hr->dstVars), cnjs);
//      for (auto &a : cnjs)
//        if (emptyIntersect(a, hr->dstVars) && emptyIntersect(a, hr->locVars))
//          newCnjs.insert(a);
//
//      return conjoin(newCnjs, m_efac);
    }

//    Expr getPrecondition (Expr decl)
//    {
//      for (auto &a : chcs)
//        if (a.srcRelation == decl->left() && a.dstRelation == decl->left())
//          return getPrecondition(&a);
//      return mk<TRUE>(m_efac);
//    }

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

    void copyIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      Expr pre = getPrecondition(hr);
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
        errs() << "Z3 ex: " << str << "...\n";
        exit(55);
      }
      return success;
    }

    void print (bool full = false)
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs){
        if (full && hr.isFact) outs() << "  INIT:\n";
        if (full && hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (full && hr.isQuery) outs() << "  BAD:\n";

        outs () << "    " << * hr.srcRelation;
        if (full && hr.srcVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.srcVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs () << " -> " << * hr.dstRelation;

        if (full && hr.dstVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.dstVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        if (full) outs() << "\n    body: " << * hr.body << "\n";
        else outs() << "\n";
      }
    }
  };
}


#endif
