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
	    ExprVector dstQueryVars;
	    ExprVector srcFactVars;

	    int iter;
	    bool iterGrows;
	    Expr numOfIters;
	    vector<int> varsInt;
	    vector<int> varsBool;
	    vector<int> varsArray;
	    // map<Expr, Expr> exprEqualities;

	    Extended_CHCs(ExprFactory &efac, EZ3 &z3, string n) : CHCs(efac, z3, n) {};

	    Extended_CHCs(const Extended_CHCs &old_CHCs) : CHCs(old_CHCs), dstQueryVars(old_CHCs.dstQueryVars),
	    	srcFactVars(old_CHCs.srcFactVars), iter(old_CHCs.iter), iterGrows(old_CHCs.iterGrows), 
	    	numOfIters(old_CHCs.numOfIters), varsInt(old_CHCs.varsInt), varsBool(old_CHCs.varsBool), 
	    	varsArray(old_CHCs.varsArray) {}

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

		void fixLoopGuard(ExprVector lastIterVars)
		{
			// works in the case of vectorization, verify for generic alignment
			int cycleNum = 0;
			vector<int> &cycle = cycles[cycleNum];
			HornRuleExt &rule = chcs[cycle[0]];

			HornRuleExt *query = getQuery();
			Expr limitEq, dummyExp;
			ExprVector varsNotInc, varsNotInc1;
			ExprSet conjs;

			Expr remainingIters = query->body;

			// because query might also have variables with same names
			Expr loopIter = eliminateQuantifiers(rule.body, rule.locVars);

			for (int i = 0; i < rule.dstVars.size(); i++)
			{
				Expr var = rule.dstVars[i];
				Expr newVar = mkTerm<string>("loc"+lexical_cast<string>(var), m_efac);
				newVar = cloneVar(var, newVar);
				loopIter = replaceAll(loopIter, var, newVar);
				remainingIters = replaceAll(remainingIters, query->srcVars[i], newVar);
				// for case where only one iter was added to query 
				// in that case, when srcVars of query were replaced by renamed vars to conjoin one iter of loop and 
				// whole query to be used as the assumption, the lastIterVars still contained srcVars. But whole formula
				// does not contain variables in lastIterVars. hence, they need to be updated too. 
				// find a better way to handle this  
				if (lastIterVars[i] == query->srcVars[i]) lastIterVars[i] = newVar;
			}
			Expr allIters = mk<AND>(loopIter, remainingIters);

			findFinalValue(iter, rule, dummyExp, limitEq, dummyExp, iterGrows, u);
			Expr goal = replaceAll(limitEq, rule.srcVars, lastIterVars);
			filter(limitEq, bind::IsConst(), inserter(varsNotInc, varsNotInc.begin()));
			filter(goal, bind::IsConst(), inserter(varsNotInc1, varsNotInc1.begin()));
			for (auto &var : varsNotInc)
				varsNotInc1.push_back(var);
			allIters = keepQuantifiers(allIters, varsNotInc1);
			getConj(allIters, conjs);
			Expr assump = mk<TRUE>(m_efac);
			for (auto &conj : conjs)
			{
				if (isOpX<EQ>(conj)) 
					assump = mk<AND>(assump, conj);
			}
			
			Expr newGuard = myAbduce(goal, assump, varsNotInc);
			
			rule.body = mk<AND>(rule.body, newGuard);
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

		/*void getExprEqualities(Expr var, HornRuleExt& rule)
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
	    }*/


	    Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
	    {
	      auto &fac = init->getFactory();
	      if (!(init && transition && final)) return mkMPZ(-1, fac);
	      Expr numer = mk<MINUS>(final, init);

	      if (add) numer = mk<PLUS>(numer, add);
	      Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, fac));

	      Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, fac), mkMPZ(1, fac)));
	      return simplifyArithm(numIters);
	    }

		bool findInitialValue(int i, Expr init, HornRuleExt& rule, Expr &initVal, SMTUtils &u)
	    {
	      Expr iter = rule.srcVars[i];
	      // outs() << "init: " << *init << "\n";

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


		void createAlignment(int unrollTrans, int unrollFact, int unrollQuery, Expr& prefRuleBody, 
			ExprVector& prefRuleLocVars, ExprVector& lastIterVars, BndExpl &bnd, bool actualAlign=true)
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
		
      mergeIterationsFact(prefixRule, unrollFact, ssa, bnd, actualAlign);
			trace.clear();

			// merge iterations to the query, given the unrollquery value
			trace.push_back(prefix[0]);

			for (int j = 0; j < unrollQuery; j++)
        for (int m = 0; m < cycle.size(); m++)
          trace.push_back(cycle[m]);

      ExprVector ssa1;
      bnd.getSSA(trace, ssa1);

	if (unrollQuery > 0)
	{
		if (unrollQuery == 1) lastIterVars = query->srcVars;
		else 
		{
			for (auto &var : bnd.bindVars[unrollQuery-1])
			{
				Expr newVar = mkTerm<string>(varname+lexical_cast<string>(var), m_efac);
				newVar = cloneVar(var, newVar);
				lastIterVars.push_back(newVar);
			}
		}
	}

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
				// for (auto &var : srcFactVars) {
				// 	factBndVars.erase(var);
				// }
        for (auto &var : factBndVars)
				{
					Expr new_name = mkTerm<string>(varname+lexical_cast<string>(var), m_efac);
      		Expr var1 = cloneVar(var, new_name);
      		prefRuleBody = replaceAll(prefRuleBody, var, var1);
      		prefRuleLocVars.push_back(var1);
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
	      Expr replacedTrans = replaceAll(transitionVal, rule.srcVars, rule.dstVars);
	      if (!u.implies(rule.body, mk<EQ>(transitionVal, replacedTrans)))
	      {
	        transitionVal = NULL;
	        return false;
	      }

	      // outs() << "transitionVal: " << *transitionVal << "\n";
	      return true;
	    }

	    bool findFinalValue(int i, HornRuleExt& rule, Expr& limitVal, Expr& limitEq, Expr& add, bool iterIncreases, SMTUtils &u)
	    {
	      Expr a = rule.srcVars[i];
	      Expr b = rule.dstVars[i];

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

	        // check if limit value is constant; Eq. 8, section 4
	        Expr replacedLimit = replaceAll(limitVal, rule.srcVars, rule.dstVars);
	        bool constLimitValCheck = bool(u.implies(rule.body, mk<EQ>(limitVal, replacedLimit)));
	        
	        // check the case that iter does not exceed limit value during transition; Eq. 7, section 4
	        bool loopEndCheck = limitEq && !u.isSat(mk<AND>(mkNeg(limitEq), rule.body));

	        if (!constLimitValCheck || !loopEndCheck)
	        {
	          limitVal = NULL;
	          limitEq = NULL;
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
	      Expr pref = bnd.compactPrefix(cycleNum);

	      Expr rel = rule.srcRelation;
	      iter = -1;

	      int invNum = getVarIndex(rel, decls);

	      for (int i = 0; i < rule.srcVars.size(); i++)
	      {
	        Expr a = rule.srcVars[i];
	        Expr b = rule.dstVars[i];
	        bool isAnIter = false;

	        bool iterDecreases = bind::isIntConst(a) && bool(u.implies(rule.body, mk<GT>(a, b)));
	        bool iterIncreases = bind::isIntConst(a) && bool(u.implies(rule.body, mk<LT>(a, b)));

	        if (iterIncreases || iterDecreases)
	        {
	          Expr initVal, transitionVal, limitVal;
	          Expr add, limitEq;

	          // AH: handle the case where it is iterator but any of values are not available
	          bool hasInitVal = findInitialValue(i, pref, rule, initVal, u);

	          bool hasTransitionVal = findTransitionValue(i, rule, transitionVal, u);

	          bool hasLimitVal = findFinalValue(i, rule, limitVal, limitEq, add, iterIncreases, u);

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
}

#endif
