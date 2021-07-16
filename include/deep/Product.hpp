#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

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


	class Extended_CHCs : public CHCs
	{
		public:
	    ExprVector dstQueryVars;
	    ExprVector srcFactVars;

	    int iter;
	    bool iterGrows;
	    Expr numOfIters;
	    vector<int> varsInt;
	    vector<int> varsBool;
	    vector<int> varsArray;
	    map<Expr, Expr> exprEqualities;

	    Extended_CHCs(ExprFactory &efac, EZ3 &z3, string n) : CHCs(efac, z3, n) {};

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
						// fix, if possible
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

		void removePreLoop()
		{
			int cycleNum = 0;
			vector<int> cycle = cycles[cycleNum];
			HornRuleExt loop = chcs[cycle[0]];
			
			vector<HornRuleExt>::iterator fact, preLoop;
			bool preLoopFound = false;
			for (auto it = chcs.begin(); it != chcs.end(); it++)
			{
				if (it->isFact) 
					fact = it;

				if (!it->isFact && !it->isInductive && !it->isQuery && it->dstRelation == loop.srcRelation) 
				{
					preLoopFound = true;
					preLoop = it;
				}

			}

			if (!preLoopFound) return;
			HornRuleExt &f = *fact, &pl = *preLoop;
			Expr body = replaceAll(f.body, f.dstVars, pl.srcVars);
			pl.body = mk<AND>(pl.body, body);
			srcFactVars = pl.srcVars;
			pl.srcVars.clear();
			removeDecl(pl.srcRelation);
			pl.srcRelation = f.srcRelation;
			pl.isFact = true;

			chcs.erase(fact);
		}

		void removePostLoop()
		{
			int cycleNum = 0;
			vector<int> cycle = cycles[cycleNum];
			HornRuleExt loop = chcs[cycle[0]];
			
			vector<HornRuleExt>::iterator query, postLoop;
			bool postLoopFound = false;
			for (auto it = chcs.begin(); it != chcs.end(); it++)
			{
				if (it->isQuery) 
					query = it;
				
				if (!it->isFact && !it->isInductive && !it->isQuery && it->srcRelation == loop.srcRelation) 
				{
					postLoopFound = true;
					postLoop = it;
				}
			}

			if (!postLoopFound) return;
			HornRuleExt &q = *query, &pl = *postLoop;
			Expr body = replaceAll(q.body, q.srcVars, pl.dstVars);
			pl.body = mk<AND>(pl.body, body);
			dstQueryVars = pl.dstVars;
			pl.dstVars.clear();
			pl.head = q.head;
			removeDecl(pl.dstRelation);
			pl.dstRelation = q.dstRelation;
			pl.isQuery = true;

			chcs.erase(query);
		}


	    // renaming rels in decls and chcs; if to be added, invVars need to be renamed too
		/* void renameRels()
		{
			ExprSet newDcls;
			for (auto it = decls.begin(); it != decls.end(); )
			{
				Expr newDcl = renameFdecl(*it);
				newDcls.insert(newDcl);
				it = decls.erase(it);
			}
			decls.insert(newDcls.begin(), newDcls.end());

			failDecl = mkTerm<string>(varname+lexical_cast<string>(failDecl), m_efac);

			for (auto &chc : chcs)
			{
				if (!chc.isQuery)
				{
					chc.head = renameFdecl(chc.head);
					chc.dstRelation = chc.head->arg(0);
				}
				else 
				{
					chc.head = failDecl;
					chc.dstRelation = failDecl;
				}
				if (!isOpX<TRUE>(chc.srcRelation))
					chc.srcRelation = mkTerm<string>(varname+lexical_cast<string>(chc.srcRelation), m_efac);
			}
		}
*/

		/*void serializeFormulas()
		{
			for (auto& it : chcs)
			{
				ExprVector v;
				Expr q = createQuantifiedFormula(it.body, v);
				u.serialize_formula(q);

				Expr body = it.body;
				for (auto v : it.locVars)
				{
					ExprSet s{v};
					body = eliminateQuantifiers(body, s);
				}
			}
		}*/

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


	    Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
	    {
	      auto &fac = init->getFactory();
	      if (!(init && transition && final)) return mkMPZ(-1, fac);
	      Expr numer = mk<MINUS>(final, init);

	      if (add) numer = mk<PLUS>(numer, add);
	      Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, fac));

	      Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, fac), mkMPZ(1, fac)));
	      return numIters;
	    }

		bool findInitialValue(int i, Expr init, HornRuleExt& rule, Expr &initVal, SMTUtils &u)
	    {
	      Expr iter = rule.srcVars[i];
	      // outs() << "init: " << *init << "\n";

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
	        	Expr normalized = ineqSimplifier(iter, simplifyArithm(initVal));
	          initVal = normalized->right();
	          // assigns non-primed variables
	          initVal = replaceAll(initVal, rule.dstVars, rule.srcVars);
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


	    void rulesOfPredicate(Expr decl, vector<HornRuleExt> &rulesOfP)
	    {
			for (auto it = chcs.begin(); it != chcs.end(); it++)
			{
				if (decl == it->head)
				{
					rulesOfP.push_back(*it);
				}
			}
	    }


		void mergeIterationsFact(HornRuleExt &fact, int num, ExprVector &ssa, BndExpl &bnd, bool actualAlign)
		{
			if (num <= 0) return;

			// case when we do not already have processed a preloop; we need to save variables in srcFactVars
			// in the other case we already have srcFactVars info, the ssa has already done proper unrolling
			// should only work when we are actually aligning and not just checking, as we do not want to 
			// modify srcFactVars if we are not aligning; if not modifying srcFactVars, ssa already has handled
			if (actualAlign && srcFactVars.empty())
			{
				for (int i = 0; i < bnd.bindVars[0].size(); i++)
				{
					Expr newVar = mkTerm<string>(varname+"fact_var_"+lexical_cast<string>(i), fact.body->getFactory());
					newVar = cloneVar(bnd.bindVars[0][i], newVar);

					srcFactVars.push_back(newVar);
				}
			
				ssa[0] = replaceAll(ssa[0], bnd.bindVars[0], srcFactVars);
				ssa[1] = replaceAll(ssa[1], bnd.bindVars[0], srcFactVars);
			}
			ssa[num] = replaceAll(ssa[num], bnd.bindVars[num], fact.dstVars);
		}

		void mergeIterationsLoop(HornRuleExt &loop, int num, ExprVector &ssa, BndExpl &bnd)
		{
			if (num <= 0) return;
			loop.body = replaceAll(loop.body, loop.dstVars, bnd.bindVars[0]);
			ssa[num-1] = replaceAll(ssa[num-1], bnd.bindVars[num], loop.dstVars);
		}

		void mergeIterationsQuery(HornRuleExt *query, int num, ExprVector &ssa, BndExpl &bnd)
		{
			if (num <= 0) return;

			ssa[0] = replaceAll(ssa[0], bnd.bindVars[0], query->srcVars);
			if (dstQueryVars.empty()) 
			{
				for (int i = 0; i < bnd.bindVars[num].size(); i++)
				{
					Expr newVar = mkTerm<string>(varname+"query_var_"+lexical_cast<string>(i), query->body->getFactory());
					newVar = cloneVar(bnd.bindVars[num][i], newVar);

					dstQueryVars.push_back(newVar);
				}
				ssa[num-1] = replaceAll(ssa[num-1], bnd.bindVars[num], dstQueryVars);
				query->body = replaceAll(query->body, query->srcVars, dstQueryVars);
			}
			else
			{
				query->body = replaceAll(query->body, query->srcVars, bnd.bindVars[num]);
			}
		}


		void createAlignment(int unrollTrans, int unrollFact, int unrollQuery, Expr& prefRuleBody, BndExpl &bnd, bool actualAlign=true)
		{
			if (!(unrollTrans == 0 && unrollQuery == 0))
			{
				cout << "Iterations in the loop: " << unrollTrans << "\n";
				cout << "Iterations added to fact: " << unrollFact << "\n";
				cout << "Iterations added to query: " << unrollQuery << "\n";
			}

			vector<int>& cycle = cycles[0];
			HornRuleExt& rule = chcs[cycle[0]];
			auto & prefix = prefixes[0];
			HornRuleExt &prefixRule = chcs[prefix[0]];
			Expr rel = rule.srcRelation;

			HornRuleExt *query;
			for (auto &it : outgs[rel])
				if (chcs[it].isQuery)
					query = &chcs[it];
			
			rel = getDecl(rel);

			prefRuleBody = prefixRule.body;

			// merge iterations to the fact, given the unrollFact value
			vector<int> trace;

			trace.push_back(prefix[0]);

			for (int j = 0; j < unrollFact; j++)
	          for (int m = 0; m < cycle.size(); m++)
	            trace.push_back(cycle[m]);

	        ExprVector ssa;
	        bnd.getSSA(trace, ssa);

		ExprSet factBndVars;
	        filter(conjoin(ssa, m_efac), IsConst(), inserter(factBndVars, factBndVars.begin()));
		
	        // AH: have to push extra vars to locVars
	        mergeIterationsFact(prefixRule, unrollFact, ssa, bnd, actualAlign);
			trace.clear();

			// merge iterations to the query, given the unrollquery value
			trace.push_back(prefix[0]);

			for (int j = 0; j < unrollQuery; j++)
	          for (int m = 0; m < cycle.size(); m++)
	            trace.push_back(cycle[m]);

	        ExprVector ssa1;
	        bnd.getSSA(trace, ssa1);

	        ssa1.erase(ssa1.begin());

			ExprSet queryBndVars;
	        filter(conjoin(ssa1, m_efac), IsConst(), inserter(queryBndVars, queryBndVars.begin()));
		
	        mergeIterationsQuery(query, unrollQuery, ssa1, bnd);

	        trace.clear();

	        // unroll the inductive rule unrollTrans times
			trace.push_back(prefix[0]);

			for (int j = 0; j < unrollTrans-1; j++)
	          for (int m = 0; m < cycle.size(); m++)
	            trace.push_back(cycle[m]);

	        ExprVector ssa2;
	        bnd.getSSA(trace, ssa2);

	        ssa2.erase(ssa2.begin());

			ExprSet ruleBndVars;
	        filter(conjoin(ssa2, m_efac), IsConst(), inserter(ruleBndVars, ruleBndVars.begin()));

	        mergeIterationsLoop(rule, unrollTrans-1, ssa2, bnd);

	        // make required changes to the CHC system
	        if (unrollFact > 0) 
	        {
	        	prefRuleBody = conjoin(ssa, m_efac);
			for (auto &var : srcFactVars) {
				factBndVars.erase(var);
			}
		        for (auto &var : factBndVars)
				{
					Expr new_name = mkTerm<string>(varname+lexical_cast<string>(var), m_efac);
	        		Expr var1 = cloneVar(var, new_name);
	        		prefRuleBody = replaceAll(prefRuleBody, var, var1);
				}
	        }
			if (unrollTrans > 1) 
			{
				Expr addToRule = conjoin(ssa2, m_efac);
		        for (auto &var : ruleBndVars)
				{
					Expr new_name = mkTerm<string>(varname+lexical_cast<string>(var), m_efac);
	        		Expr var1 = cloneVar(var, new_name);
	        		addToRule = replaceAll(addToRule, var, var1);
	        		rule.body = replaceAll(rule.body, var, var1);
	        		rule.locVars.push_back(var1);
				}
				rule.body = mk<AND>(rule.body, addToRule);
			}
			if (unrollQuery > 0) 
			{
				Expr addToQuery = conjoin(ssa1, m_efac);
		        
				for (auto &var : queryBndVars)
				{
					Expr new_name = mkTerm<string>(varname+lexical_cast<string>(var), m_efac);
	        		Expr var1 = cloneVar(var, new_name);
	        		addToQuery = replaceAll(addToQuery, var, var1);
	        		query->locVars.push_back(var1);
				}
				query->body = mk<AND>(query->body, addToQuery);
			}
		}

	    bool findTransitionValue(int i, HornRuleExt& rule, Expr& transitionVal, SMTUtils &u)
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

	    bool findFinalValue(int i, HornRuleExt& rule, Expr& limitVal, Expr& add, bool iterIncreases, SMTUtils &u)
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
	          add = mkMPZ(1, a->getFactory());
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
	          add = mkMPZ(-1, a->getFactory());
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

	    bool findIterators(BndExpl &bnd, int cycleNum)
	    {
	      vector<int>& cycle = cycles[cycleNum];
	      HornRuleExt& rule = chcs[cycle[0]];
	      // vector<int> &prefix = prefixes[cycleNum];
	      // HornRuleExt &prefixRule = chcs[prefix[0]];
	      Expr pref = bnd.compactPrefix(cycleNum);

	      Expr rel = rule.srcRelation;
	      iter = -1;

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
	          bool hasInitVal = findInitialValue(i, pref, rule, initVal, u);

	          bool hasTransitionVal = findTransitionValue(i, rule, transitionVal, u);

	          bool hasLimitVal = findFinalValue(i, rule, limitVal, add, iterIncreases, u);

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
	      return (iter >= 0);
	    }

	    void extraProcessing()
	    {
  			removePreLoop();
				removePostLoop();
				renameLocVars();

				// we do it because we have already populated these containers with information with initial chcs,
				// which have now been updated by removing pre and post loop
				// either do this, or never populate with initial state of the chcs
				wtoCHCs.clear();
				wtoDecls.clear();
				prefixes.clear();
				cycles.clear();
				outgs.clear();

				for (int i = 0; i < chcs.size(); i++)
		        outgs[chcs[i].srcRelation].push_back(i);

				wtoSort();
	    }
	};


	class Product_CHCs : public Extended_CHCs
	{
	public:
	    Extended_CHCs* subRule1;
	    Extended_CHCs* subRule2;

	    Product_CHCs(Extended_CHCs &rules1, Extended_CHCs &rules2, string n) : 
	    	Extended_CHCs(rules1.m_efac, rules1.m_z3, n), subRule1(&rules1), subRule2(&rules2) {};

		void nonRecursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars)
		{
			ExprVector chc1NonRecPart, chc2NonRecPart;
			Expr rel;
			
			getSpecificSrcRelations(chc1.srcRelation, chc1.dstRelation, false, chc1NonRecPart, 0);
			getSpecificSrcRelations(chc2.srcRelation, chc2.dstRelation, false, chc2NonRecPart, 1);

			bool chc1NonRec = !chc1NonRecPart.empty();
			bool chc2NonRec = !chc2NonRecPart.empty();

			if (chc1NonRec)
			{
				product = chc1NonRecPart[0]->arg(0);
				vars.insert(vars.end(), subRule1->invVars[product].begin(), subRule1->invVars[product].end());
				for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
				{
					rel = (*it)->arg(0);
					product = mk<AND>(product, rel);
					vars.insert(vars.end(), subRule1->invVars[rel].begin(), subRule1->invVars[rel].end());
				}
			}

			if (chc2NonRec)
			{
				rel = chc2NonRecPart[0]->arg(0);
				if (!product) product = rel;
				else product = mk<AND>(product, rel);
				vars.insert(vars.end(), subRule2->invVars[rel].begin(), subRule2->invVars[rel].end());
				for (auto it = chc2NonRecPart.begin()+1; it != chc2NonRecPart.end(); it++)
				{
					rel = (*it)->arg(0);
					product = mk<AND>(product, rel);
					vars.insert(vars.end(), subRule2->invVars[rel].begin(), subRule2->invVars[rel].end());
				}
			}
		}


		void getSpecificSrcRelations(Expr srcRelation, Expr dstRelation, bool recursive, ExprVector &partitions, int pos)
		{
			Expr decl;
			if (isOpX<AND>(srcRelation))
			{
				for (int i = 0; i < srcRelation->arity(); i++)
					getSpecificSrcRelations(srcRelation->arg(i), dstRelation, recursive, partitions, i);
			}
			else if (!isOpX<TRUE>(srcRelation))
			{
				if (recursive && srcRelation == dstRelation)
				{
					// todo: remove dependence on this pos variable
					if (pos == 0) decl = subRule1->getDecl(srcRelation);
					else decl = subRule2->getDecl(srcRelation);
					partitions.push_back(decl);
				}
				else if (!recursive && srcRelation != dstRelation)
				{
					if (pos == 0) decl = subRule1->getDecl(srcRelation);
					else decl = subRule2->getDecl(srcRelation);
					partitions.push_back(decl);
				}
			}
		}


		void RTransform(HornRuleExt &chc, ExprVector &transformed, int pos)
		{
			Expr decl;
			if (!chc.isInductive)
			{
				transformed.push_back(bind::fapp(chc.head, chc.dstVars));
			}
			else
			{
				if (pos == 0) decl = subRule1->getDecl(chc.srcRelation);
				else decl = subRule2->getDecl(chc.srcRelation);
				transformed.push_back(bind::fapp(decl, chc.srcVars));
			}
		}


		void recursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars)
		{
			vector<HornRuleExt> nullV;
			ExprVector transformed;

			RTransform(chc1, transformed, 0); RTransform(chc2, transformed, 1);

			// might have to check if there are more than two relation symbols in transformed
			productRelationSymbols(ExprVector{transformed[0]->arg(0), transformed[1]->arg(0)}, 
				product, nullV, false);

			// remove head(C) from body
			if (bind::fapp(chc1.head, chc1.dstVars) == transformed[0] 
				&& bind::fapp(chc2.head, chc2.dstVars) == transformed[1]) 
			{
				product = NULL;
			}
			else 
			{
				vars.insert(vars.end(), transformed[0]->args_begin()+1, transformed[0]->args_end());
				vars.insert(vars.end(), transformed[1]->args_begin()+1, transformed[1]->args_end());

				product = product->arg(0);
			}
		}


		void bodyProduct(HornRuleExt &chc1, HornRuleExt &chc2, HornRuleExt &newProductRule)
		{
			Expr constraintPr, recursivePr, nonRecursivePr;
			ExprVector nonRecursivePrVars, recursivePrVars;

			// constraint product
			constraintPr = mk<AND>(chc1.body, chc2.body);

			// non-recursive part product
			nonRecursiveProduct(chc1, chc2, nonRecursivePr, nonRecursivePrVars);

			// recursive part product
			recursiveProduct(chc1, chc2, recursivePr, recursivePrVars);

			// if (chc1.isInductive && chc2.isInductive) newProductRule.subRelationsBothInductive = true;
			// else newProductRule.subRelationsBothInductive = false;

			newProductRule.body = constraintPr;

			if (nonRecursivePr && recursivePr) 
			{
				newProductRule.srcRelation = mk<AND>(nonRecursivePr, recursivePr);
				concatenateVectors(newProductRule.srcVars, nonRecursivePrVars, recursivePrVars);
			}
			else if (nonRecursivePr) 
			{
				newProductRule.srcRelation = nonRecursivePr;
				newProductRule.srcVars = nonRecursivePrVars;
			}
			else if (recursivePr) 
			{
				newProductRule.srcRelation = recursivePr;
				newProductRule.srcVars = recursivePrVars;
			}
			else 
			{
				newProductRule.srcRelation = mk<TRUE>(m_efac);
				newProductRule.srcVars = ExprVector();
			}
			newProductRule.isFact = (isOpX<TRUE>(newProductRule.srcRelation));
			newProductRule.isQuery = (newProductRule.dstRelation == failDecl);
			newProductRule.isInductive = (recursivePr != NULL);
		}


		void calculateCombinations(vector<vector<HornRuleExt>> &rules, vector<vector<HornRuleExt>> &combinations)
		{
			vector<HornRuleExt> rulesFirstP = rules[0], rulesSecondP = rules[1];

			for (auto it : rulesFirstP)
			{
				for (auto it2 : rulesSecondP)
				{
					combinations.push_back(vector<HornRuleExt>{it, it2});
				}
			}
		}

		void createProductQueries(HornRuleExt &queryPr)
		{
			HornRuleExt *query1, *query2;

			query1 = subRule1->getQuery();
			query2 = subRule2->getQuery();
			queryPr.body = mk<AND>(query1->body, query2->body);

			queryPr.srcRelation = mk<AND>(query1->srcRelation, query2->srcRelation);
			queryPr.dstRelation = mkTerm<string>(lexical_cast<string>(query1->dstRelation) + 
				"*" + lexical_cast<string>(query2->dstRelation), m_efac);

			queryPr.head = bind::fdecl(queryPr.dstRelation, ExprVector{mk<BOOL_TY>(m_efac)});

			// queries do not have dstVars
			queryPr.dstVars = ExprVector();
			concatenateVectors(queryPr.srcVars, query1->srcVars, query2->srcVars);
			concatenateVectors(queryPr.locVars, query1->locVars, query2->locVars);
			
			queryPr.isFact = false;
			queryPr.isQuery = true;
			queryPr.isInductive = false;

			if (!failDecl)
				addFailDecl(queryPr.dstRelation);
		}


	    void calculateProductOfRules(Expr rel1, Expr rel2, vector<HornRuleExt> &rulesOfP)
	    {
			vector<vector<HornRuleExt>> rulesOfPredicates, combinations;
			vector<HornRuleExt> rulesOfCurrentP;

			subRule1->rulesOfPredicate(rel1, rulesOfCurrentP);
			rulesOfPredicates.push_back(rulesOfCurrentP);
			rulesOfCurrentP.clear();

			subRule2->rulesOfPredicate(rel2, rulesOfCurrentP);
			rulesOfPredicates.push_back(rulesOfCurrentP);

			calculateCombinations(rulesOfPredicates, combinations);

			for (auto &it : combinations)
			{
				productOfCHCs(it[0], it[1], rulesOfP);
			}
	    }


		void productRelationSymbols(ExprVector predicates, Expr &predicateP, vector<HornRuleExt> &rulesOfP, 
			bool calculateRulesOfP)
		{
			ExprVector productTypes;
			Expr rel1 = predicates[0], rel2 = predicates[1];

			Expr productRel = mkTerm<string>(lexical_cast<string>(rel1->arg(0)) + "*" + 
				lexical_cast<string>(rel2->arg(0)), m_efac);

			productTypes.insert(productTypes.end(), rel1->args_begin()+1, rel1->args_begin()+rel1->arity()-1);
			productTypes.insert(productTypes.end(), rel2->args_begin()+1, rel2->args_begin()+rel2->arity());

			predicateP = bind::fdecl(productRel, productTypes);
			
			if (calculateRulesOfP) 
				calculateProductOfRules(rel1, rel2, rulesOfP);
		}


		void productOfCHCs(HornRuleExt &chc1, HornRuleExt &chc2, vector<HornRuleExt> &rulesOfP)
		{
			Expr head, body;
			vector<HornRuleExt> nullV;
			vector<ExprVector> nullV1;
			HornRuleExt newProductRule;

			// head product
			productRelationSymbols(ExprVector{chc1.head, chc2.head}, head, nullV, false/*, nullV1*/);
			newProductRule.head = head;
			newProductRule.dstRelation = head->arg(0);
			concatenateVectors(newProductRule.dstVars, chc1.dstVars, chc2.dstVars);
			
			// body product
			bodyProduct(chc1, chc2, newProductRule);

			concatenateVectors(newProductRule.locVars, chc1.locVars, chc2.locVars);

			// do not push if one is inductive and other one is not. Push in all other cases
			if ((newProductRule.isInductive && chc1.isInductive && chc2.isInductive) || !newProductRule.isInductive) 
				rulesOfP.push_back(newProductRule);
		}

		void renamingAsProductRules()
		{
			ExprVector srcVars, dstVars;

			for (auto &chc : chcs) 
			{
				srcVars = chc.srcVars; dstVars = chc.dstVars;
				
				// might add dstVars of one of the CHCs to product locVars twice in some cases, should not be a problem
				concatenateVectors(chc.locVars, srcVars, dstVars);
				chc.srcVars.clear(); chc.dstVars.clear();

				ExprVector dstV;
				for (auto &it : invVars[chc.dstRelation])
				{
					Expr new_name = mkTerm<string> (lexical_cast<string>(it) + "'", m_efac);
					dstV.push_back(cloneVar(it, new_name));
				}

				chc.assignVarsAndRewrite(srcVars, invVars[chc.srcRelation], 
					dstVars, dstV);
			}
		}


		void simplifyRules()
		{
			renamingAsProductRules();

			// extra chcs are not currently being pushed to the chcs, hence this code is not needed
			// but if all chcs were to be computed (like in paper), this code filters out extra rules
			/*for (auto chcIter = chcs.begin(); chcIter != chcs.end(); )
			{   
				bool erased = false;
				bool allowed = (chcIter->isInductive && chcIter->subRelationsBothInductive) || !chcIter->isInductive;

				// it checks if any inductive CHC has only one loop iterating
				// generally we allow that behavior in the product of two CHC systems, we compute them in the algorithm
				// but since we do not need those extra relations, we filter them out here
				if (!allowed)
				{
					chcIter = chcs.erase(chcIter);
					continue;
				}
				chcIter++;
			}*/
		}


		// generates the product of two CHC systems
		// At many places, it is assumed that there are only two systems, 
		// hence the operations done are not generic i.e. for product of more than two CHC systems
		void createProduct()
		{
			vector<HornRuleExt> transformedCHCs;
			vector<HornRuleExt> worklist;
			HornRuleExt C_a;

			HornRuleExt queryPr;

			concatenateVectors(dstQueryVars, subRule1->dstQueryVars, subRule2->dstQueryVars);
			concatenateVectors(srcFactVars, subRule1->srcFactVars, subRule2->srcFactVars);

			// generate product queries
			createProductQueries(queryPr);
			worklist.push_back(queryPr);

			HornRuleExt *query1 = subRule1->getQuery(), *query2 = subRule2->getQuery();

			while (!worklist.empty())
			{
				Expr freshP;
				ExprVector partition;
				vector<HornRuleExt> rulesOfP;
				C_a = worklist[0];
				worklist.erase(worklist.begin());

				// AH: In the original algorithm, the operation PARTITION is used that is defined: 
				// 'operator partition from a set to a set of its disjoint subsets'
				// Here, just one partition created of two symbols because there are only two relation symbols here 

				// argument false for non-recursive; getting non-recursive parts of the srcrelation
				getSpecificSrcRelations(C_a.srcRelation, C_a.dstRelation, false, partition, 0);
				getSpecificSrcRelations(C_a.srcRelation, C_a.dstRelation, false, partition, 1);

				if (partition.size() >= 2) 
				{
					// take product of relation symbols in partition, 
					// true specified if product of rules of relations is to be calculated
					productRelationSymbols(partition, freshP, rulesOfP, true);
					C_a.srcRelation = freshP->arg(0);

					worklist.insert(worklist.end(), rulesOfP.begin(), rulesOfP.end());
				}

				if (isOpX<AND>(C_a.srcRelation))
				{
					// outs() << "Non-linear CHC:\n";
					// C_a.printMemberVars();
				}
				else 
				{
					// if freshP is not NULL, it went into the if-statement (partition.size() >= 2)
					if (freshP) addDecl(freshP);					
					chcs.push_back(C_a);
				}
			}

			// changes variables from _v1_ and _v2_ prefixes to _pr_ with necessary changes, 
			// also disjoins rules to remove redundancy
			simplifyRules();

			for (int i = 0; i < chcs.size(); i++)
				outgs[chcs[i].srcRelation].push_back(i);

			// sort rules
			wtoSort();

			outs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
		}
	};

	inline bool learnInvariantsPr(CHCs &ruleManager, Expr currentMatching)
  {
    EZ3 z3(ruleManager.m_efac);
    BndExpl bnd(ruleManager);

    unsigned maxAttempts = 2000000, to = 10000;
    bool freqs = false, aggp = false, enableDataLearning = true, doElim = false, doDisj = false;
    bool dAllMbp = false, dAddProp = false, dAddDat = false, dStrenMbp = false;

    RndLearnerV3 ds(ruleManager.m_efac, z3, ruleManager, to, freqs, aggp, dAllMbp, dAddProp, dAddDat, dStrenMbp);
    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      Expr rel = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      ExprSet tmp;
      getConj(pref, tmp);
      for (auto & t : tmp)
        if(hasOnlyVars(t, ruleManager.invVars[rel]))
          cands[rel].insert(t);
      ds.mutateHeuristicEq(cands[rel], cands[rel], rel, true);
      ds.initializeAux(bnd, i, pref);
    }
    // if (enableDataLearning) ds.getDataCandidates(cands);
    
    for (auto& dcl: ruleManager.wtoDecls) ds.getSeeds(dcl, cands);
    ds.refreshCands(cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();

    // call bootstrap with option to only consider equalities as candidates for finding invariant
    // also add equalities for variable matchings
    bool check = ds.bootstrap(doDisj, currentMatching, false);
    // if (!check)
    // {
    //   std::srand(std::time(0));
    //   check = ds.synthesize(maxAttempts, doDisj);
    // }
    return check;
  }


    bool findAlignment(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2)
	{
		auto &fac = ruleManager1.m_efac;
		SMTUtils u(fac);
		int cycleNum1 = 0, cycleNum2 = 0;

		vector<int> &cycle1 = ruleManager1.cycles[cycleNum1];
		HornRuleExt &rule1 = ruleManager1.chcs[cycle1[0]];
		vector<int> &prefix1 = ruleManager1.prefixes[cycleNum1];
		HornRuleExt &prefixRule1 = ruleManager1.chcs[prefix1[0]];
		Expr rel1 = rule1.srcRelation;
		int invNum1 = getVarIndex(rel1, ruleManager1.decls);

		vector<int> &cycle2 = ruleManager2.cycles[cycleNum2];
		HornRuleExt &rule2 = ruleManager2.chcs[cycle2[0]];
		vector<int> &prefix2 = ruleManager2.prefixes[cycleNum2];
		HornRuleExt &prefixRule2 = ruleManager2.chcs[prefix2[0]];
		Expr rel2 = rule2.srcRelation;
		int invNum2 = getVarIndex(rel2, ruleManager2.decls);

		BndExpl bnd1(ruleManager1);
		BndExpl bnd2(ruleManager2);

		Expr pref1 = bnd1.compactPrefix(cycleNum1), pref2 = bnd2.compactPrefix(cycleNum2);

		int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;
		outs() << "\n\nassuming iters: " << *rule1.srcVars[iter1] << " and " << *rule2.srcVars[iter2] << "\n";
	    Expr numIters1 = ruleManager1.numOfIters;
	    Expr numIters2 = ruleManager2.numOfIters;
	    //outs() << "numIters: " << *numIters1 << " and " << *numIters2 << "\n";

		vector<vector<vector<int>>> combsArray, combsInt, combsBool, nonIterCombinations, combs1;
		combinationsOfVars(ruleManager1.varsArray, ruleManager2.varsArray, combsArray);
		combinationsOfVars(ruleManager1.varsInt, ruleManager2.varsInt, combsInt);
		combinationsOfVars(ruleManager1.varsBool, ruleManager2.varsBool, combsBool);

		joinVars(combsArray, combsInt, combs1);
		joinVars(combs1, combsBool, nonIterCombinations);

		// fix later
		vector<vector<int>> v{{-1, -1}};
		if (nonIterCombinations.empty()) nonIterCombinations.push_back(v);

		// for (auto elems: nonIterCombinations)
		// {
		//   for (auto elems1 : elems)
		//   {
		//     outs() << "vars: " << *rule1.dstVars[elems1[0]] << " and " << *rule2.dstVars[elems1[1]] << "\n";
		//   }
		//   outs() << "\n\n";
		// }

		// check for all combinations of variables, such that we match same type of variables
		for (auto &comb : nonIterCombinations)
		{

			// create a quantified formula for optimization query
      Expr coef1 = bind::intConst(mkTerm<string>("coef1", fac));
      Expr coef2 = bind::intConst(mkTerm<string>("coef2", fac));

      Expr const1 = bind::intConst(mkTerm<string>("const1", fac));
      Expr const2 = bind::intConst(mkTerm<string>("const2", fac));
      
      Expr minCoef1, minCoef2, minConst1, minConst2;

      Expr quantifiedFla;

      Expr preRelev = mk<TRUE>(fac), preRelev2 = mk<TRUE>(fac);
			Expr iterF = rule1.dstVars[iter1], iterFVal;
			Expr iterS = rule2.dstVars[iter2], iterSVal;

			ruleManager1.findInitialValue(iter1, pref1, rule1, iterFVal, u);
			ruleManager2.findInitialValue(iter2, pref2, rule2, iterSVal, u);

			// add any variables that are needed in the quantified formula
			for (auto &pair : comb)
			{
				// checks if initial values of iterators depend on any variables; also constant values are also added to pre
				// we might as well check that the pair[1] variable is also constant, similar to third check
				if ((contains(iterFVal, rule1.srcVars[pair[0]]) || contains(iterSVal, rule2.srcVars[pair[1]])
				|| u.implies(rule1.body, mk<EQ>(rule1.srcVars[pair[0]], rule1.dstVars[pair[0]]))) 
				&& (!isOpX<ARRAY_TY>(bind::typeOf(rule1.srcVars[pair[0]])))) 
				{
					preRelev = mk<AND>(preRelev, mk<EQ>(rule1.dstVars[pair[0]], rule2.dstVars[pair[1]]));
					preRelev2 = mk<AND>(preRelev2, mk<EQ>(rule1.srcVars[pair[0]], rule2.srcVars[pair[1]]));
				}
			}

	    if (!(numIters1 == mkMPZ(-1, fac) || numIters2 == mkMPZ(-1, fac))) 
	    {
	      Expr coefs = mk<AND>(mk<GT>(coef1, mkMPZ(0, fac)), mk<GT>(coef2, mkMPZ(0, fac)));
	      Expr consts = mk<AND>(mk<GEQ>(const1, mkMPZ(0, fac)), mk<GEQ>(const2, mkMPZ(0, fac)));

	      Expr numIters = bind::intConst(mkTerm<string>("numIters1", fac));
	      Expr numItersP = bind::intConst(mkTerm<string>("numIters2", fac));

	      Expr fla = mk<AND>(mk<EQ>(numIters, numIters1), mk<EQ>(numItersP, numIters2));

	      ExprVector varsIters;
	      
	      // used when local vars are present, extra equalities are needed then
	      /*Expr extraRels;
	      filter(fla, IsConst(), inserter(varsIters, varsIters.begin()));
	     
	    	for (auto &it : varsIters)
	    	{
	    		// outs() << "varsIters: " << *it << "\n";
	    		if (ruleManager1.exprEqualities.find(it) != ruleManager1.exprEqualities.end())
	    		{
	    			if (extraRels) extraRels = mk<AND>(extraRels, ruleManager1.exprEqualities[it]);
	    			else extraRels = ruleManager1.exprEqualities[it];
	    		}

	    		if (ruleManager2.exprEqualities.find(it) != ruleManager2.exprEqualities.end())
	    		{
	    			if (extraRels) extraRels = mk<AND>(extraRels, ruleManager2.exprEqualities[it]);
	    			else extraRels = ruleManager2.exprEqualities[it];
	    		}
	    	}

	    	outs() << "extraRels: " << *extraRels << "\n";

	      Expr newPre = extraRels;*/

	      fla = mk<AND>(preRelev2, fla);
	      Expr implFla = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters, const1)), 
	      	mk<MULT>(coef1, mk<MINUS>(numItersP, const2)));
	      
	      filter(fla, IsConst(), inserter(varsIters, varsIters.begin()));
	      
	      fla = mk<IMPL>(fla, implFla); 

	      quantifiedFla = createQuantifiedFormulaRestr(fla, varsIters);
	      quantifiedFla = mk<AND>(consts, mk<AND>(coefs, quantifiedFla));

	      outs() << "quantifiedFla: " << *quantifiedFla << "\n";

	      Expr constsZero = mk<AND>(mk<EQ>(const1, mkMPZ(0, fac)), mk<EQ>(const2, mkMPZ(0, fac)));
	      Expr const1Zero = mk<EQ>(const1, mkMPZ(0, fac));
	      Expr const2Zero = mk<EQ>(const2, mkMPZ(0, fac));

		
	      Expr model;
	      
	      if (u.isSat(mk<AND>(quantifiedFla, constsZero))) model = u.getModel();
	      else if (u.isSat(mk<AND>(quantifiedFla, const1Zero))) model = u.getModel();
	      else if (u.isSat(mk<AND>(quantifiedFla, const2Zero))) model = u.getModel();
	      else if (u.isSat(quantifiedFla)) model = u.getModel();
	      else 
	      {
	      	outs() << "Not satisfiable\n";
	      	continue;
	      }
	      
	      if (model) 
	      {
	      	// outs() << "model: " << *model << "\n";
					// iterative solving optimization query to get all minmodels
					// verify if I need to find minimum coef1 and coef2 separately
	        Expr minModels = u.getMinModelInts(coef1);

	        findExpr<EQ>(coef1, minModels, minCoef1, true);
	        findExpr<EQ>(coef2, minModels, minCoef2, true);
					findExpr<EQ>(const1, minModels, minConst1, true);
          findExpr<EQ>(const2, minModels, minConst2, true);

          u.isSat(mk<AND>(quantifiedFla, mk<AND>(minCoef1, minCoef2)));

					if (minConst1->right() == mkMPZ(0, fac))
						minModels = u.getMinModelInts(const2);
					else 
						minModels = u.getMinModelInts(const1);
                
					minConst1 = NULL;
          minConst2 = NULL;
          findExpr<EQ>(const1, minModels, minConst1, true);
          findExpr<EQ>(const2, minModels, minConst2, true);

          minCoef1 = minCoef1->right();
          minCoef2 = minCoef2->right();
          minConst1 = minConst1->right();
          minConst2 = minConst2->right();
        }
	else
	{
		outs() << "No satisfying assignment for quantified formula was found\n";
		continue;
	}
      }
      else 
      {
      	outs() << "number of iterations were not found\n";
      	continue;
      }

      outs() << "copy " << *minConst1 << " iterations of loop 1 to fact and query combined\n";
      outs() << "copy " << *minConst2 << " iterations of loop 2 to fact and query combined\n";
      outs() << "we need " << *minCoef1 << " iterations of loop 1 to align\n";
      outs() << "we need " << *minCoef2 << " iterations of loop 2 to align\n";

      int coef1Int = (int)lexical_cast<cpp_int>(minCoef1);
			int const1Int = (int)lexical_cast<cpp_int>(minConst1);
			int coef2Int = (int)lexical_cast<cpp_int>(minCoef2);
			int const2Int = (int)lexical_cast<cpp_int>(minConst2);

			// Currently, it does all combinations to check the number of iterations to be added to fact and query
			vector<int> v1, v2;
			vector<vector<int>> vComb;
			for (int i = 0; i <= const1Int; i++) v1.push_back(i);
			for (int i = 0; i <= const2Int; i++) v2.push_back(i);

			for (auto &it : v1)
				for (auto &it2 : v2)
					vComb.push_back(vector<int>{it, it2});

			 // for (auto it : vComb)
			 // 	outs() << it[0] << " " << const1Int-it[0] << " " << it[1] << " " << const2Int-it[1] << "\n";

			bool impliesEq = false;
			for (auto &it : vComb)
			{
				// check if adding certain iterations to query will make the initial values of iterators equal
				// it is not greedy approach currently
				Expr prefRuleBody1, prefRuleBody2;
				ruleManager1.createAlignment(0, it[0], 0, prefRuleBody1, bnd1, false);
				ruleManager2.createAlignment(0, it[1], 0, prefRuleBody2, bnd2, false);

				Expr tempProdFact = mk<AND>(mk<AND>(prefRuleBody1, prefRuleBody2), preRelev);
				Expr eq = mk<EQ>(iterF, iterS);
				impliesEq = u.implies(tempProdFact, eq);

				if (impliesEq)
				{
					// actual alignment created here
					ruleManager1.createAlignment(coef1Int, it[0], const1Int-it[0], prefRuleBody1, bnd1);
					prefixRule1.body = prefRuleBody1;

					ruleManager2.createAlignment(coef2Int, it[1], const2Int-it[1], prefRuleBody2, bnd2);
					prefixRule2.body = prefRuleBody2;

					// break out of the loop if for any alignment, we have iterators initially equal;
					// consequently, all remaining iterations are added to query; 
					// support checking other combinations
					break;
				}
			}


			// if iterator values do not match for any number of iterations, no alignment found
			if (!impliesEq) continue;


			HornRuleExt *query1 = ruleManager1.getQuery(), *query2 = ruleManager2.getQuery();

			if (ruleManager1.srcFactVars.empty()) ruleManager1.srcFactVars = prefixRule1.dstVars;
			if (ruleManager2.srcFactVars.empty()) ruleManager2.srcFactVars = prefixRule2.dstVars;
			if (ruleManager1.dstQueryVars.empty()) ruleManager1.dstQueryVars = query1->srcVars;
			if (ruleManager2.dstQueryVars.empty()) ruleManager2.dstQueryVars = query2->srcVars;

			Expr init1 = prefixRule1.body, init2 = prefixRule2.body;

			Expr pre;
			bool skipComb = false;
			if (comb[0][0] != -1)
			{
				for (auto &pair : comb)
				{
					Expr var1 = ruleManager1.srcFactVars[pair[0]];
					Expr var2 = ruleManager2.srcFactVars[pair[1]];

					if ((!u.hasOneModel(var1, init1) && !u.hasOneModel(var2, init2)) 
						|| (u.hasOneModel(var1, init1) && u.hasOneModel(var2, init2)))
					{
						if (!pre) pre = mk<EQ>(var1, var2);
						else pre = mk<AND>(pre, mk<EQ>(var1, var2));
					}
					else
					{
						skipComb = true;
						break;
					}

				}
				if (skipComb) continue;
			}
			else pre = mk<TRUE>(fac);

			// create postcondition
			Expr post;
			post = replaceAll(pre, ruleManager1.srcFactVars, ruleManager1.dstQueryVars);
			post = replaceAll(post, ruleManager2.srcFactVars, ruleManager2.dstQueryVars);

			Expr negPost = mkNeg(post);

			// create the product 
			Product_CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_");

		    // product of two CHC systems
			ruleManagerProduct.createProduct();

			HornRuleExt *fact, *query, *ind;
			for (auto &it : ruleManagerProduct.chcs)
			{
				it.printMemberVars();
				if (it.isFact) fact = &it;
				if (it.isQuery) query = &it;
				if (it.isInductive) ind = &it;
			}
			fact->body = mk<AND>(fact->body, pre);
			query->body = simplifyBool(mk<AND>(query->body, negPost));

			outs() << "fact: " << *fact->body << "\n";
			outs() << "query: " << *query->body << "\n";

			outs () << "   check fact sanity:  "  << bool(u.isSat(fact->body)) << "\n";
			outs () << "   check query sanity:  "  << bool(u.isSat(query->body)) << "\n";
			outs () << "   check ind sanity:  "  << bool(u.isSat(ind->body)) << "\n";

			outs() << "------------------------CREATING ALIGNED PROGRAM DONE-----------------------------\n\n";

			Expr currentMatching = mk<TRUE>(fac);
			int sz = rule1.srcVars.size();
			for (auto &pair : comb)
			{
				Expr eq = mk<EQ>(ind->srcVars[pair[0]], ind->srcVars[sz+pair[1]]);
				currentMatching = mk<AND>(currentMatching, eq);
			}

			// GF: hack to create pairs (to revisit) -- visited, works well
			for (int i = 0; i < sz; i++)
				if (bind::typeOf(ind->srcVars[i]) == bind::typeOf(ind->srcVars[sz + i]))
					currentMatching = mk<AND>(currentMatching, mk<EQ>(ind->srcVars[i], (ind->srcVars[sz + i])));

			// call the function with all default values for arguments that are not relevant
			// probably, do a cleaner way of calling the function
		    if (learnInvariantsPr(ruleManagerProduct, currentMatching)) return true;
		}
		return false;
	}


	// Create an aligned product program
	inline void createProductAligned(const char *chcfileSrc, const char *chcfileDst)
	{
		ExprFactory m_efac;
		EZ3 z3(m_efac);

		Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_");
		ruleManagerSrc.parse(string(chcfileSrc), false);

		Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_");
		ruleManagerDst.parse(string(chcfileDst), false);

		ruleManagerSrc.extraProcessing();
		ruleManagerDst.extraProcessing();

		BndExpl bndSrc(ruleManagerSrc);
		BndExpl bndDst(ruleManagerDst);

		// if no iterator was found, the tool exits stating non-equivalence. Support more
		for (int i = 0; i < ruleManagerSrc.cycles.size(); i++) 
		{
			bool iterFound = ruleManagerSrc.findIterators(bndSrc, i);
			if (!iterFound) 
			{
				outs() << "no iterator was found for program 1. programs are not equivalent\n";
				exit(0);
			}
		}

		for (int i = 0; i < ruleManagerDst.cycles.size(); i++) 
		{
			bool iterFound = ruleManagerDst.findIterators(bndDst, i);
			if (!iterFound) 
			{
				outs() << "no iterator was found  for program 2. programs are not equivalent\n";
				exit(0);
			}
		}

		bool equiv = findAlignment(ruleManagerSrc, ruleManagerDst);
		if (equiv) outs() << "\nprograms are equivalent\n";
		else outs() << "programs are not equivalent\n";
  };


  	// create a product with no alignment
	inline void createProductBase(const char *chcfileSrc, const char *chcfileDst)
	{
		ExprFactory m_efac;
		EZ3 z3(m_efac);

		SMTUtils u(m_efac);

		Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_");
		ruleManagerSrc.parse(string(chcfileSrc));

		Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_");
		ruleManagerDst.parse(string(chcfileDst));

		Product_CHCs ruleManagerProduct(ruleManagerSrc, ruleManagerDst, "_pr_");

		// create precondition and postcondition
		vector<int> &cycle1 = ruleManagerSrc.cycles[0];
		HornRuleExt &rule1 = ruleManagerSrc.chcs[cycle1[0]];
		vector<int> &prefix1 = ruleManagerSrc.prefixes[0];
		HornRuleExt &prefixRule1 = ruleManagerSrc.chcs[prefix1[0]];
		Expr rel1 = rule1.srcRelation;
		int invNum1 = getVarIndex(rel1, ruleManagerSrc.decls);
		Expr init1 = prefixRule1.body;
		
		vector<int> &cycle2 = ruleManagerDst.cycles[0];
		HornRuleExt &rule2 = ruleManagerDst.chcs[cycle2[0]];
		vector<int> &prefix2 = ruleManagerDst.prefixes[0];
		HornRuleExt &prefixRule2 = ruleManagerDst.chcs[prefix1[0]];
		Expr rel2 = rule2.srcRelation;
		int invNum2 = getVarIndex(rel2, ruleManagerDst.decls);
		Expr init2 = prefixRule2.body;

		Expr pre;
		for (int i = 0; i < rule1.srcVars.size(); i++)
		{
			Expr var = rule1.srcVars[i];
			Expr var1 = rule2.srcVars[i];

			if ((!u.hasOneModel(var, init1) && !u.hasOneModel(var1, init2)) 
				|| (u.hasOneModel(var, init1) && u.hasOneModel(var1, init2)))
			{
				if (!pre) pre = mk<EQ>(rule1.dstVars[i], rule2.dstVars[i]);
				else pre = mk<AND>(pre, mk<EQ>(rule1.dstVars[i], rule2.dstVars[i]));
			}
			else
			{
				outs() << "programs are not equivalent\n";
				return;
			}
		}

		Expr post;
		post = replaceAll(pre, rule1.dstVars, rule1.srcVars); 
		post = replaceAll(post, rule2.dstVars, rule2.srcVars); 
		Expr negPost = mkNeg(post);

	    // product of two CHC systems
		ruleManagerProduct.createProduct();

		HornRuleExt *fact, *query;
		for (auto &it : ruleManagerProduct.chcs)
		{
			if (it.isFact) fact = &it;
			if (it.isQuery) query = &it;
		}
		fact->body = mk<AND>(fact->body, pre);
		query->body = simplifyBool(mk<AND>(query->body, negPost));

		if (learnInvariantsPr(ruleManagerProduct, mk<TRUE>(m_efac)))
			outs() << "programs are equivalent\n";
		else
			outs() << "programs are not equivalent\n";
  };
}

#endif
