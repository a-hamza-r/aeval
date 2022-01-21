#ifndef EXTENDED_HORN__HPP__
#define EXTENDED_HORN__HPP__

#include "Horn.hpp"
#include "BndExpl.hpp"
#include "RndLearnerV2.hpp"
#include "RndLearnerV3.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

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

	void combinations(vector<int> &vars1, vector<int> &vars2, vector<vector<int>> c,
		vector<int> vars2Used, vector<vector<vector<int>>> &combs, int pos)
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


	Expr myAbduce(Expr goal, Expr assmp, ExprVector varsNotInc=ExprVector())
	{
		Expr quantified = keepQuantifiers(mkNeg(mk<IMPL>(assmp, goal)), varsNotInc);
		Expr tmp = mkNeg(quantified);

		return tmp;
	}


	class Extended_CHCs : public CHCs
	{
		public:
	    ExprVector srcFactVars;

	    int iter;
	    Expr loopRel;
	    bool iterGrows;
	    Expr numOfIters;
	    vector<int> varsInt;
	    vector<int> varsBool;
	    vector<int> varsArray;
      Expr postLoopBody;
      ExprVector postLoopSrcVars;
      ExprVector postLoopDstVars;

	    Extended_CHCs(ExprFactory &efac, EZ3 &z3, string n, int d = false) : CHCs(efac, z3, n, d) {};

	    Extended_CHCs(const Extended_CHCs &old_CHCs) : CHCs(old_CHCs),
	    	srcFactVars(old_CHCs.srcFactVars), iter(old_CHCs.iter), iterGrows(old_CHCs.iterGrows),
	    	numOfIters(old_CHCs.numOfIters), varsInt(old_CHCs.varsInt), varsBool(old_CHCs.varsBool),
	    	varsArray(old_CHCs.varsArray), postLoopBody(old_CHCs.postLoopBody), postLoopSrcVars(old_CHCs.postLoopSrcVars),
	    	postLoopDstVars(old_CHCs.postLoopDstVars) {}

      Expr getDecl(Expr relation)
			{
				if (!isOpX<TRUE>(relation))
				{
					for (auto it = decls.begin(); it != decls.end(); it++)
					{
						if ((*it)->arg(0) == relation) return *it;
					}
				}
				return NULL;
			}

			void removeDecl(Expr relation)
			{
				Expr decl;
				if (!isOpX<TRUE>(relation))
				{
					for (auto it = decls.begin(); it != decls.end(); it++)
					{
						if ((*it)->arg(0) == relation)
						{
							decls.erase(it);
							return;
						}
					}
				}
			}


	    Expr renameFdecl(Expr e)
	    {
				Expr newName = mkTerm<string>(varname+lexical_cast<string>(e->arg(0)), m_efac);
				ExprVector types(e->args_begin()+1, e->args_end());
				return bind::fdecl(newName, types);
	    }


	    void renameLocVars()
	    {
	    	for (auto &chc : chcs)
	    	{
	    		for (int i = 0; i < chc.locVars.size(); i++)
	    		{
			        Expr var = chc.locVars[i]->arg(0);
	    			var = renameFdecl(var);
	    			chc.body = replaceAll(chc.body, chc.locVars[i], bind::fapp(var));
	    			chc.locVars[i] = bind::fapp(var);
	    		}
	    	}
	    }


		HornRuleExt *getQuery()
		{
			for (auto &chc : chcs)
			{
				if (chc.isQuery) return &chc;
			}
			return NULL;
		}

		HornRuleExt *getFact()
		{
			for (auto &chc : chcs)
			{
				if (chc.isFact) return &chc;
			}
			return NULL;
		}

		void removePreLoop()
		{
			vector<int> cycle = cycles[0];
			HornRuleExt &loop = chcs[cycle[0]];

			HornRuleExt &f = *getFact();

			for (auto it = chcs.begin(); it != chcs.end(); it++)
			{
				if (!it->isFact && !it->isInductive && !it->isQuery)
				{
					if (it->dstRelation == loop.srcRelation)
					{
						HornRuleExt &pl = *it;
						
						Expr body = replaceAll(f.body, f.dstVars, pl.srcVars);
						pl.body = mk<AND>(pl.body, body);
						if (emptyIntersect(pl.body, pl.srcVars)) srcFactVars = pl.dstVars;
						else srcFactVars = pl.srcVars;
						pl.srcVars.clear();
						removeDecl(pl.srcRelation);
						pl.srcRelation = f.srcRelation;
						pl.isFact = true;
						// hack, remove as soon as get a chance
						f.dstRelation = mk<TRUE>(m_efac);

						for (auto it2 = chcs.begin(); it2 != chcs.end(); it2++)
						{
							// only for recognizing certain rule
							if (it2->dstRelation == mk<TRUE>(m_efac)) 
							{
								chcs.erase(it2);
								return;
							}
						}
					}
				}
			}
			srcFactVars = f.dstVars;
		}

		void removePostLoop()
		{
			vector<int> cycle = cycles[0];
			HornRuleExt &loop = chcs[cycle[0]];

			HornRuleExt &q = *getQuery();

			for (auto it = chcs.begin(); it != chcs.end(); it++)
			{
				if (!it->isFact && !it->isInductive && !it->isQuery)
				{
					if (it->srcRelation == loop.srcRelation)
					{
						HornRuleExt &pl = *it;

			      Expr body = replaceAll(q.body, q.srcVars, pl.dstVars);
			      pl.body = mk<AND>(pl.body, body);
						postLoopBody = pl.body;
			      postLoopSrcVars = pl.srcVars;
						if (emptyIntersect(pl.body, pl.dstVars)) postLoopDstVars = pl.srcVars;
			      else postLoopDstVars = pl.dstVars;
			      pl.dstVars.clear();
						removeDecl(pl.dstRelation);
						pl.dstRelation = q.dstRelation;
						pl.isQuery = true;
						// hack, remove as soon as get a chance
						q.srcRelation = mk<FALSE>(m_efac);

						for (auto it2 = chcs.begin(); it2 != chcs.end(); it2++)
						{
							// only for recognizing certain rule
							if (it2->srcRelation == mk<FALSE>(m_efac)) 
							{
								chcs.erase(it2);
								return;
							}
						}
					}
				}
			}
		}

    // to convert CHCs into a forall formula to be taken input directly by freqhorn
    // possibly, add exists formula too
		void serializeFormulas()
		{
			ExprVector v;
			ExprVector vars;

			// assuming only one loop, makes things easier
			Expr e = (*decls.begin())->arg(0);

			for (auto &it : invVarsPrime[e])
			{
				Expr newVar = cloneVar(it, mkTerm<string>('|'+lexical_cast<string>(it)+'|', m_efac));
				v.push_back(newVar);
			}
			concatenateVectors(vars, srcFactVars, v);

			outs() << "(declare-fun " << e << " (";

			for (int i = 0; i < v.size(); i++)
      {
        outs () << u.varType(v[i]);
        if (i != v.size() - 1) outs () << " ";
      }
      outs () << ") Bool)\n";

			for (auto& chc : chcs)
			{
				// outs() << (chc.isFact ? "Fact" : (chc.isQuery ? "Query" : "Inductive")) << ": \n";
				Expr body = chc.body;

				for (auto v : chc.locVars)
				{
					ExprSet s{v};
					body = eliminateQuantifiers(body, s);
				}

				if (!isOpX<TRUE>(chc.srcRelation))
					body = mk<AND>(body, fapp(getDecl(chc.srcRelation), invVars[chc.srcRelation]));

				if (chc.dstRelation != failDecl)
					body = mk<IMPL>(body, fapp(getDecl(chc.dstRelation), v));
				else
					body = mk<IMPL>(body, mk<FALSE>(m_efac));

				body = createQuantifiedFormulaRestr(body, vars);
				u.serialize_formula(body);
			}
		}

    Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
    {
      if (!(init && transition && final)) return mkMPZ(-1, m_efac);
      Expr numer = mk<MINUS>(final, init);

      if (add) numer = mk<PLUS>(numer, add);
      Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, m_efac));

      Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, m_efac), mkMPZ(1, m_efac)));
      return simplifyArithm(numIters);
    }

		bool findInitialValue(int i, Expr init, Expr rel, Expr &initVal)
	    {
	      Expr iter = invVars[rel][i];

	      findExpr<EQ>(iter, init, initVal, true);
	      if (initVal)
	      {
	        Expr newInit;
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
	        	Expr normalized = ineqSimplifier(iter, simplifyArithm(initVal));
	          initVal = normalized->right();
	          // assigns non-primed variables
	          initVal = replaceAll(initVal, invVarsPrime[rel], invVars[rel]);
	          return true;

	        }
	      }
	      return false;
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

    void rulesOfPredicate(Expr decl, vector<HornRuleExt*> &rulesOfP)
    {
      for (auto it = chcs.begin(); it != chcs.end(); it++)
        if (decl == it->dstRelation)
          rulesOfP.push_back(&*it);
    }

		void mergeIterationsFact(HornRuleExt &fact, int num, ExprVector &ssa, BndExpl &bnd, 
			Expr &prefixBody, ExprVector &locVars, bool actualAlign)
		{
		  if (num <= 0) return;

			// ExprVector tempVars;
			// for (int i = 0; i < bnd.bindVars.size(); i++)
			// {
			// 	for (auto &v : bnd.bindVars[i])
			// 	{
			// 		Expr newVar = mkTerm<string>(varname+lexical_cast<string>(v), m_efac);
			// 		newVar = cloneVar(v, newVar);
			// 		conjoinedSSA = replaceAll(conjoinedSSA, v, newVar);
			// 		if (i==0) tempVars.push_back(newVar);
			// 	}
			// }

			// ssa[0] = replaceAll(ssa[0], bnd.bindVars[0], tempVars);
			// ssa[1] = replaceAll(ssa[1], bnd.bindVars[0], tempVars);
      filter(conjoin(ssa, m_efac), IsConst(), inserter(locVars, locVars.begin()));

			ssa[num] = replaceAll(ssa[num], bnd.bindVars[num], fact.dstVars);
			
			prefixBody = conjoin(ssa, m_efac);

			if (actualAlign)
			{
				// fact.body = replaceAll(fact.body, fact.dstVars, bnd.bindVars[0]);
				// fact.body = prefixBody;
				// fact.locVars.insert(fact.locVars.end(), locVars.begin(), locVars.end());

				// in case srcFactVars are empty, we needed the srcFactVars as bnd.bindVars[0]
				// in case srcFactVars are not empty, we just replaced the whole fact with some formula, 
				// initial variables are then bnd.bindVars[0]
				srcFactVars = bnd.bindVars[0];
			}
		}

		void mergeIterationsLoop(HornRuleExt &loop, int num, ExprVector &ssa, BndExpl &bnd)
		{
			if (num <= 0) return;

			ExprSet locVars;
      filter(conjoin(ssa, m_efac), IsConst(), inserter(locVars, locVars.begin()));

			loop.body = replaceAll(loop.body, loop.dstVars, bnd.bindVars[0]);
			ssa[num-1] = replaceAll(ssa[num-1], bnd.bindVars[num], loop.dstVars);

			loop.body = mk<AND>(loop.body, conjoin(ssa, m_efac));
			loop.locVars.insert(loop.locVars.end(), locVars.begin(), locVars.end());
		}


    void createAlignment(int unrollTrans, int unrollFact, int unrollQuery, BndExpl &bnd, 
    	Expr &prefixBody, ExprVector &prefixLocVars, bool actualAlign=true)
		{
			if (actualAlign)
			{
				cout << "Iterations in the loop: " << unrollTrans << "\n";
				cout << "Iterations added to fact: " << unrollFact << "\n";
				cout << "Iterations added to query: " << unrollQuery << "\n";
			}

			vector<int>& cycle = cycles[0];
			HornRuleExt& rule = chcs[cycle[0]];
			auto & prefix = prefixes[0];
			HornRuleExt &prefixRule = chcs[prefix[0]];
			
			vector<int> traceFactUnroll = {prefix[0]}, traceQueryUnroll = {prefix[0]}, traceLoopUnroll = {prefix[0]};
      ExprVector ssa, ssa1, ssa2;

      // ************* FACT UNROLLING ***************

			// merge iterations to the fact, given the unrollFact value
			for (int j = 0; j < unrollFact; j++)
        for (int m = 0; m < cycle.size(); m++)
          traceFactUnroll.push_back(cycle[m]);

      bnd.getSSA(traceFactUnroll, ssa, varname);

      // actually merge fact
      mergeIterationsFact(prefixRule, unrollFact, ssa, bnd, prefixBody, prefixLocVars, actualAlign);


      // ************* QUERY UNROLLING ***************

      // merge iterations to the query, given the unrollquery value
			for (int j = 0; j < unrollQuery; j++)
        for (int m = 0; m < cycle.size(); m++)
          traceQueryUnroll.push_back(cycle[m]);

      bnd.getSSA(traceQueryUnroll, ssa1, varname);
      ssa1.erase(ssa1.begin());

      // actually merge query
      if (unrollQuery > 0)
      {
        postLoopSrcVars = bnd.bindVars[0];
        postLoopDstVars = bnd.bindVars[bnd.bindVars.size()-1];
        postLoopBody = conjoin(ssa1, m_efac);
      }


      // ************* LOOP UNROLLING ***************

      // unroll the inductive rule unrollTrans times
			for (int j = 0; j < unrollTrans-1; j++)
        for (int m = 0; m < cycle.size(); m++)
          traceLoopUnroll.push_back(cycle[m]);

      bnd.getSSA(traceLoopUnroll, ssa2, varname);
      ssa2.erase(ssa2.begin());

      mergeIterationsLoop(rule, unrollTrans-1, ssa2, bnd);
		}

	    bool findTransitionValue(int i, Expr rel, Expr body, Expr& transitionVal)
	    {
	      ExprSet allExprs;
	      Expr allExprsConj, e;
	      bool multipleTransVal = false;

	      Expr a = invVars[rel][i];
	      Expr b = invVarsPrime[rel][i];

	      findExpr<EQ>(b, body, e, true);

	      if (!e) return false;

	      e = ineqSimplifier(b, e);

	      getConjAndDisj(e, allExprs);
	      for (auto &it : allExprs)
	      {
	      	Expr normalized = ineqSimplifier(b, simplifyArithm(it));
	        if (contains(it, a) && isOpX<EQ>(normalized) && normalized->left() == b)
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
	      Expr replacedTrans = replaceAll(transitionVal, invVars[rel], invVarsPrime[rel]);
	      if (!u.implies(body, mk<EQ>(transitionVal, replacedTrans)))
	      {
	        transitionVal = NULL;
	        return false;
	      }

	      return true;
	    }

	    bool findFinalValue(int i, Expr rel, Expr body, Expr& limitVal, Expr& limitEq, Expr& add, bool iterIncreases)
	    {
	      Expr a = invVars[rel][i];
	      Expr b = invVarsPrime[rel][i];

	      Expr gt, ge, lt, le;
	      if (iterIncreases)
	      {
	        findExpr<LT>(a, body, lt, true);
	        findExpr<LEQ>(a, body, le, true);

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
	          add = mkMPZ(1, a->getFactory());
	          le = ineqSimplifier(a, le);
	          if (!(isOpX<AND>(le) || isOpX<OR>(le))) limitEq = le;
	        }
	      }
	      else
	      {
	        findExpr<GT>(a, body, gt);
	        findExpr<GEQ>(a, body, ge);

	        // make sure there is no case where both gt and ge are not null
	        // cannot think of any but could be
	        if (gt)
	        {
	          gt = ineqSimplifier(a, gt);
	          if (!(isOpX<AND>(gt) || isOpX<OR>(gt))) limitEq = gt;
	        }
	        if (ge)
	        {
	          add = mkMPZ(-1, a->getFactory());
	          ge = ineqSimplifier(a, ge);
	          if (!(isOpX<AND>(ge) || isOpX<OR>(ge))) limitEq = ge;
	        }
	      }

	      if (limitEq)
	      {
	        limitVal = limitEq->arg(1);

	        // check if limit value is constant; Eq. 8, section 4
	        Expr replacedLimit = replaceAll(limitVal, invVars[rel], invVarsPrime[rel]);
	        bool constLimitValCheck = bool(u.implies(body, mk<EQ>(limitVal, replacedLimit)));

	        // check the case that iter does not exceed limit value during transition; Eq. 7, section 4
	        bool loopEndCheck = limitEq && !u.isSat(mk<AND>(mkNeg(limitEq), body));

	        if (!constLimitValCheck || !loopEndCheck)
	        {
	          limitVal = NULL;
	          limitEq = NULL;
	          return false;
	        }
	        return true;
	      }
	      return false;
	    }

	    bool findIterators(BndExpl &bnd)
	    {
	      vector<int>& cycle = cycles[0];
	      HornRuleExt& rule = chcs[cycle[0]];

	      Expr pref = bnd.compactPrefix(0);

	      Expr rel = rule.srcRelation;
	      iter = -1;

	      for (int i = 0; i < invVars[rel].size(); i++)
	      {
	        Expr a = invVars[rel][i];
	        Expr b = invVarsPrime[rel][i];

	        bool isAnIter = false;

	        bool iterDecreases = bind::isIntConst(a) && bool(u.implies(rule.body, mk<GT>(a, b)));
	        bool iterIncreases = bind::isIntConst(a) && bool(u.implies(rule.body, mk<LT>(a, b)));

	        if (iterIncreases || iterDecreases)
	        {
	          Expr initVal, transitionVal, limitVal;
	          Expr add, limitEq;

	          bool hasInitVal = findInitialValue(i, pref, rel, initVal);

	          bool hasTransitionVal = findTransitionValue(i, rel, rule.body, transitionVal);

	          bool hasLimitVal = findFinalValue(i, rel, rule.body, limitVal, limitEq, add, iterIncreases);

	          isAnIter = hasInitVal && hasTransitionVal && hasLimitVal;
	          if (isAnIter)
	          {
	            iter = i;
	          	loopRel = rel;
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
	      return (iter >= 0);
	    }

	    void preprocessing()
	    {
  			removePreLoop();
  			
  			prefixes.clear();
				cycles.clear();
				outgs.clear();

				for (int i = 0; i < chcs.size(); i++)
		        outgs[chcs[i].srcRelation].push_back(i);

        hasCycles();

  			removePostLoop();
				renameLocVars();

				// we do it because we have already populated these containers with information with initial chcs,
				// which have now been updated by removing pre and post loop
				// either do this, or never populate with initial state of the chcs
				prefixes.clear();
				cycles.clear();
				outgs.clear();

				for (int i = 0; i < chcs.size(); i++)
		        outgs[chcs[i].srcRelation].push_back(i);

        hasCycles();
	    }
	};
}

#endif
