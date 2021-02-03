#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"
#include "RndLearnerV3.hpp"
#include "../ae/SMTUtils.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

	void productOfCHCs(HornRuleExt &, HornRuleExt &, vector<HornRuleExt> &, CHCs &);

	void productRelationSymbols(ExprVector, Expr &, vector<HornRuleExt> &, CHCs &, bool, vector<ExprVector> &);


	void removeCHC(Expr srcRelation, Expr dstRelation, CHCs &rules)
	{
		for (auto it = rules.chcs.begin(); it != rules.chcs.end(); it++)
		{
			if (it->srcRelation == srcRelation && it->dstRelation == dstRelation)
			{
				rules.chcs.erase(it);

				// this might not be the best location to remove decls; recheck
				rules.removeDecl(srcRelation);
				rules.removeDecl(dstRelation);
			}
		}
	}


	void getSpecificSrcRelations(Expr rel, Expr dstRelation, bool recursive, ExprVector &partitions, CHCs &rules)
	{
		Expr decl;
		if (isOpX<AND>(rel))
		{
			for (auto it = rel->args_begin(); it != rel->args_end(); it++)
			{
				getSpecificSrcRelations(*it, dstRelation, recursive, partitions, rules);
			}
		}
		else if (!isOpX<TRUE>(rel))
		{
			if (recursive && rel == dstRelation)
			{
				rules.getDecl(rel, decl);
				partitions.push_back(decl);
			}
			else if (!recursive && rel != dstRelation)
			{
				rules.getDecl(rel, decl);
				partitions.push_back(decl);
			}
		}
	}


	void nonRecursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars, CHCs &rules)
	{
		ExprVector chc1NonRecPart, chc2NonRecPart;
		Expr rel;
		
		getSpecificSrcRelations(chc1.srcRelation, chc1.dstRelation, false, chc1NonRecPart, rules);
		getSpecificSrcRelations(chc2.srcRelation, chc2.dstRelation, false, chc2NonRecPart, rules);

		bool chc1NonRec = !chc1NonRecPart.empty();
		bool chc2NonRec = !chc2NonRecPart.empty();

		if (chc1NonRec)
		{
			product = chc1NonRecPart[0]->arg(0);
			vars.insert(vars.end(), rules.invVars[product].begin(), rules.invVars[product].end());
			for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
			{
				rel = (*it)->arg(0);
				product = mk<AND>(product, rel);
				vars.insert(vars.end(), rules.invVars[rel].begin(), rules.invVars[rel].end());
			}
		}

		if (chc2NonRec)
		{
			rel = chc2NonRecPart[0]->arg(0);
			if (!product) product = rel;
			else product = mk<AND>(product, rel);
			vars.insert(vars.end(), rules.invVars[rel].begin(), rules.invVars[rel].end());
			for (auto it = chc2NonRecPart.begin()+1; it != chc2NonRecPart.end(); it++)
			{
				rel = (*it)->arg(0);
				product = mk<AND>(product, rel);
				vars.insert(vars.end(), rules.invVars[rel].begin(), rules.invVars[rel].end());
			}
		}
	}


	void RTransform(HornRuleExt &chc, ExprVector &transformed, CHCs &rules)
	{
		Expr decl;
		if (!chc.isInductive)
		{
			transformed.push_back(bind::fapp(chc.head, chc.dstVars));
		}
		else
		{
			rules.getDecl(chc.srcRelation, decl);
			transformed.push_back(bind::fapp(decl, chc.srcVars));
		}
	}


	void recursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars, CHCs &rules)
	{
		vector<HornRuleExt> nullV;
		vector<ExprVector> nullV1;
		ExprVector transformed;

		RTransform(chc1, transformed, rules); RTransform(chc2, transformed, rules);

		// might have to check if there are more than two relation symbols in transformed
		productRelationSymbols(ExprVector{transformed[0]->arg(0), transformed[1]->arg(0)}, 
			product, nullV, rules, false, nullV1);

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


	void productBody(HornRuleExt &chc1, HornRuleExt &chc2, CHCs &rules, HornRuleExt &newProductRule)
	{
		Expr constraintPr, recursivePr, nonRecursivePr;
		ExprVector nonRecursivePrVars, recursivePrVars;

		// constraint product
		constraintPr = mk<AND>(chc1.body, chc2.body);

		// non-recursive part product
		nonRecursiveProduct(chc1, chc2, nonRecursivePr, nonRecursivePrVars, rules);

		// recursive part product
		recursiveProduct(chc1, chc2, recursivePr, recursivePrVars, rules);

		if (chc1.isInductive && chc2.isInductive) newProductRule.subRelationsBothInductive = true;
		else newProductRule.subRelationsBothInductive = false;

		newProductRule.body = constraintPr;

		if (nonRecursivePr && recursivePr) {
			newProductRule.srcRelation = mk<AND>(nonRecursivePr, recursivePr);
			concatenateVectors(newProductRule.srcVars, nonRecursivePrVars, recursivePrVars);
		}
		else if (nonRecursivePr) {
			newProductRule.srcRelation = nonRecursivePr;
			newProductRule.srcVars = nonRecursivePrVars;
		}
		else if (recursivePr) {
			newProductRule.srcRelation = recursivePr;
			newProductRule.srcVars = recursivePrVars;
		}
		else {
			newProductRule.srcRelation = mk<TRUE>(rules.m_efac);
			newProductRule.srcVars = ExprVector();
		}
		newProductRule.isFact = (isOpX<TRUE>(newProductRule.srcRelation));
		newProductRule.isQuery = (newProductRule.dstRelation == rules.failDecl);
		newProductRule.isInductive = (recursivePr != NULL);
	}


	void getQueries(vector<HornRuleExt> &chcs1, vector<HornRuleExt> &chcs2, vector<vector<HornRuleExt>> &queries)
	{
		for (auto it = chcs1.begin(); it != chcs1.end(); it++)
		{
			if (it->isQuery) queries[0].push_back(*it);
		}

		for (auto it = chcs2.begin(); it != chcs2.end(); it++)
		{
			if (it->isQuery) queries[1].push_back(*it);
		}
	}


	void calculateCombinations(vector<vector<HornRuleExt>> &rules, vector<vector<HornRuleExt>> &combinations)
	{
		// assumption: rules has only two vectors, one for rules of each predicate
		vector<HornRuleExt> rulesFirstP = rules[0], rulesSecondP = rules[1];

		for (auto it : rulesFirstP)
		{
			for (auto it2 : rulesSecondP)
			{
				combinations.push_back(vector<HornRuleExt>{it, it2});
			}
		}
	}

	void createProductQueries(vector<vector<HornRuleExt>> &queries, vector<HornRuleExt> &queriesPr, CHCs &rules)
	{
		vector<vector<HornRuleExt>> combinations;
		calculateCombinations(queries, combinations);

		HornRuleExt query1, query2, queryPr;

		for (auto &it : combinations)
		{
			query1 = it[0];
			query2 = it[1];
			queryPr.body = mk<AND>(query1.body, query2.body);

			queryPr.srcRelation = mk<AND>(query1.srcRelation, query2.srcRelation);
			queryPr.dstRelation = mkTerm<string>(lexical_cast<string>(query1.dstRelation) + 
				"*" + lexical_cast<string>(query2.dstRelation), queryPr.body->getFactory());

			if (rules.productRelsToSrcDst.find(queryPr.dstRelation) == rules.productRelsToSrcDst.end())
				rules.productRelsToSrcDst[queryPr.dstRelation] = ExprVector{query1.dstRelation, query2.dstRelation};
			
			queryPr.head = bind::fdecl(queryPr.dstRelation, ExprVector{mk<BOOL_TY>(rules.m_efac)});

			// queries do not have dstVars
			queryPr.dstVars = ExprVector();
			concatenateVectors(queryPr.srcVars, query1.srcVars, query2.srcVars);
			concatenateVectors(queryPr.locVars, query1.locVars, query2.locVars);

			queryPr.isFact = false;
			queryPr.isQuery = true;
			queryPr.isInductive = false;

			if (!rules.failDecl)
				rules.addFailDecl(queryPr.dstRelation);

			queriesPr.push_back(queryPr);
		}
	}


	void productRelationSymbols(ExprVector predicates, Expr &predicateP, vector<HornRuleExt> &rulesOfP, 
		CHCs &rules, bool calculateRulesOfP, vector<ExprVector> &toRemoveCHCs)
	{
		ExprVector productTypes;
		vector<vector<HornRuleExt>> rulesOfPredicates, combinations;
		vector<HornRuleExt> rulesOfCurrentP;

		Expr rel1 = predicates[0], rel2 = predicates[1];

		rules.getDecl(rel1, rel1); rules.getDecl(rel2, rel2);

		// might have to do more handling, probably outside this method
		if (!isFdecl(rel1) || !isFdecl(rel2)) return;

		Expr productRel = mkTerm<string>(lexical_cast<string>(rel1->arg(0)) + "*" + 
			lexical_cast<string>(rel2->arg(0)), rules.m_efac);

		if (rules.productRelsToSrcDst.find(productRel) == rules.productRelsToSrcDst.end())
			rules.productRelsToSrcDst[productRel] = ExprVector{rel1->arg(0), rel2->arg(0)};

		for (int i = 1; i < rel1->arity()-1; i++) 
			productTypes.push_back(rel1->arg(i));

		for (int i = 1; i < rel2->arity(); i++) 
			productTypes.push_back(rel2->arg(i));

		predicateP = bind::fdecl(productRel, productTypes);
		
		if (calculateRulesOfP) 
		{
			// errs() << "Rules of relation: " << *rel1->arg(0) << "\n";
			rules.rulesOfPredicate(rel1, rulesOfCurrentP);

			for (auto &it : rulesOfCurrentP) 
			{
				toRemoveCHCs.push_back(ExprVector{it.srcRelation, it.dstRelation});
				// rules.print(it);
			}

			rulesOfPredicates.push_back(rulesOfCurrentP);

			rulesOfCurrentP.clear();

			// errs() << "Rules of relation: " << *rel2->arg(0) << "\n";
			rules.rulesOfPredicate(rel2, rulesOfCurrentP);

			for (auto &it : rulesOfCurrentP) 
			{
				toRemoveCHCs.push_back(ExprVector{it.srcRelation, it.dstRelation});
				// rules.print(it);
			}

			rulesOfPredicates.push_back(rulesOfCurrentP);

			calculateCombinations(rulesOfPredicates, combinations);

			for (auto &it : combinations)
			{
				productOfCHCs(it[0], it[1], rulesOfP, rules);
			}
		}
	}


	void productOfCHCs(HornRuleExt &chc1, HornRuleExt &chc2, vector<HornRuleExt> &rulesOfP, CHCs &rules)
	{
		Expr head, body;
		vector<HornRuleExt> nullV;
		vector<ExprVector> nullV1;
		HornRuleExt newProductRule;

		// head product
		productRelationSymbols(ExprVector{chc1.head, chc2.head}, head, nullV, rules, false, nullV1);
		newProductRule.head = head;
		newProductRule.dstRelation = head->arg(0);
		concatenateVectors(newProductRule.dstVars, chc1.dstVars, chc2.dstVars);
		
		// body product
		productBody(chc1, chc2, rules, newProductRule);

		concatenateVectors(newProductRule.locVars, chc1.locVars, chc2.locVars);

		// errs() << "Taking product of two CHCs: \n";
		// rules.print(chc1);
		// rules.print(chc2);
		// errs() << "The product is: \n";
		// rules.print(newProductRule);
		// errs() << "\n";

		// do not push if one is inductive and other one is not. Push in all other cases
		// make sure this condition is correct generically
		// if (!((!chc1.isInductive && chc2.isInductive) || (!chc2.isInductive && chc1.isInductive)))
		rulesOfP.push_back(newProductRule);
	}

	void renamingAsProductRules(CHCs &rules)
	{
		ExprVector srcVars, dstVars;

		for (auto &chc : rules.chcs) 
		{
			srcVars = chc.srcVars; dstVars = chc.dstVars;
			
			// might add dstVars of one of the CHCs to product locVars twice in some cases, should not be a problem
			concatenateVectors(chc.locVars, srcVars, dstVars);
			chc.srcVars.clear(); chc.dstVars.clear();

			chc.assignVarsAndRewrite(srcVars, rules.invVars[chc.srcRelation], 
				dstVars, rules.invVars[chc.dstRelation]);
		}

	}

	void simplifyRules(CHCs &rules)
	{
		vector<HornRuleExt*> rulesToKeep;
		Expr propagated, tmp;

		renamingAsProductRules(rules);

		for (auto chcIter = rules.chcs.begin(); chcIter != rules.chcs.end(); )
		{   
			bool erased = false;
			bool allowed = (chcIter->isInductive && chcIter->subRelationsBothInductive) || !chcIter->isInductive;

			// it checks if any inductive CHC has only one loop iterating
			// generally we allow that behavior in the product of two CHC systems, we compute them in the algorithm
			// but since we do not need those extra relations, we filter them out here
			if (!allowed)
			{
				chcIter = rules.chcs.erase(chcIter);
				continue;
			}

			// outs() << "is inductive: " << chcIter->isInductive << ", is fact: " << chcIter->isFact << "\n";
			// for (auto& it : chcIter->locVars)
			// {
			//     // outs() << "eliminating: " << *it << "\n";
			//     ExprSet vars{it};
			//     chcIter->body = eliminateQuantifiers(chcIter->body, vars);    
			//     // outs() << "body: " << *chcIter->body << "\n";
			// }
			// if (!chcIter->isFact)
			// {
			//     ExprSet vars(chcIter->locVars.begin(), chcIter->locVars.end());
			//     chcIter->body = eliminateQuantifiers(chcIter->body, vars);
			//     chcIter->locVars.clear();
			// }

			// outs() << "after QE: " << *chcIter->body << "\n";

			// uniqueizeSelects(chcIter->body);

			for (auto it : rulesToKeep)
			{
				if (chcIter->srcRelation == it->srcRelation && chcIter->dstRelation == it->dstRelation)
				{
					it->body = mk<OR>(it->body, chcIter->body);

					// it->locVars.insert(it->locVars.end(), chcIter->locVars.begin(), chcIter->locVars.end());

					chcIter = rules.chcs.erase(chcIter);
					erased = true;
					break;
				}
			}
			if (!erased)
			{
				rulesToKeep.push_back(&(*chcIter));
				chcIter++;
			}
		}
	}

	// generates the product of two CHC systems
	// At many places, it is assumed that there are only two systems, 
	// hence the operations done are not generic i.e. for product of more than two CHC systems
	void Product(CHCs &product, vector<vector<HornRuleExt>> &queries)
	{
		vector<HornRuleExt> transformedCHCs;
		vector<HornRuleExt> worklist;
		HornRuleExt C_a;
		vector<ExprVector> toRemoveCHCs;

		vector<HornRuleExt> queriesPr;

		// generate product queries
		createProductQueries(queries, queriesPr, product);

		worklist = queriesPr;

		for (auto &it : queries) 
			for (auto &it2 : it)
				toRemoveCHCs.push_back(ExprVector{it2.srcRelation, it2.dstRelation});

		while (!worklist.empty())
		{
			Expr freshP;
			ExprVector partition;
			vector<HornRuleExt> rulesOfP;
			C_a = worklist[0];
			worklist.erase(worklist.begin());

			// errs() << "current worklist item popped: \n";
			// product.print(C_a);

			// AH: In the original algorithm, the operation PARTITION is used that is defined: 
			// 'operator partition from a set to a set of its disjoint subsets'
			// I just create one partition of two symbols because there are only two relation symbols here 

			// argument false for non-recursive; getting non-recursive parts of the srcrelation
			getSpecificSrcRelations(C_a.srcRelation, C_a.dstRelation, false, partition, product);

			if (partition.size() >= 2) 
			{
				// errs() << "Non-recursive partition is: " << *partition[0]->arg(0) 
				//     << " and " << *partition[1]->arg(0) << "\n";

				productRelationSymbols(partition, freshP, rulesOfP, product, true, toRemoveCHCs);

				C_a.srcRelation = freshP->arg(0);

				// errs() << "We push rules of p " << *C_a.srcRelation << " to worklist:\n";
				worklist.insert(worklist.end(), rulesOfP.begin(), rulesOfP.end());
				// for (auto it : rulesOfP)
				//     product.print(it);
			}

			if (isOpX<AND>(C_a.srcRelation))
			{
				errs() << "Non-linear CHC:\n";
				product.print(C_a);
			}
			else 
			{
				// if freshP is not NULL, itwent into the if-statement (partition.size() >= 2)
				if (freshP) product.addDecl(freshP);
				
				product.chcs.push_back(C_a);
				
				// errs() << "Updated CHC added to CHCs: \n";
				// product.print(C_a);
				// errs() << "\n";
			}
		}

		for (auto &it : toRemoveCHCs)
		{
			removeCHC(it[0], it[1], product);
		}

		// for (auto &hr : product.chcs)
		// 	hr.printMemberVars();

		// changes variables from _v1_ and _v2_ prefixes to _pr_ with necessary changes, 
		// also disjoins rules to remove redundancy
		simplifyRules(product);

		for (int i = 0; i < product.chcs.size(); i++)
			product.outgs[product.chcs[i].srcRelation].push_back(i);

		product.wtoSort();

		// errs() << "\nFinal system:\n";
		// product.print();

		// errs() << "Printing all rules and member vars:\n";
		// for (auto &hr : product.chcs) {
		// 	hr.printMemberVars();
			
			// creates an encoding of formula and prints to stdout
			/*ExprVector v;
			Expr q = createQuantifiedFormula(hr.body, v);
			SMTUtils su(hr.body->getFactory());
			su.serialize_formula(q);*/
		// }
		errs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
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


	void mergeIterationsFact(HornRuleExt &fact, int num, ExprVector &ssa, BndExpl &bnd)
	{
		if (num <= 0) return;
		ssa[0] = replaceAll(fact.body, fact.dstVars, bnd.bindVars[0]);
		ssa[num] = replaceAll(ssa[num], bnd.bindVars[num], fact.dstVars);
	}

	void mergeIterationsLoop(HornRuleExt &loop, int num, ExprVector &ssa, BndExpl &bnd)
	{
		if (num <= 0) return;
		loop.body = replaceAll(loop.body, loop.dstVars, bnd.bindVars[0]);
		ssa[num] = replaceAll(ssa[num], bnd.bindVars[num], loop.dstVars);
	}

	void createAlignment(CHCs &ruleManager, int coef, int constt)
	{
		// cout << "coef: " << coef << "\n";
		// cout << "const: " << constt << "\n";

		vector<int>& cycle = ruleManager.cycles[0];
		HornRuleExt& rule = ruleManager.chcs[cycle[0]];
		auto & prefix = ruleManager.prefixes[0];
		HornRuleExt &prefixRule = ruleManager.chcs[prefix[0]];
		Expr rel = rule.srcRelation;
		ruleManager.getDecl(rel, rel);

		BndExpl bnd(ruleManager);

		vector<int> trace;

		trace.push_back(prefix[0]);

		for (int j = 0; j < constt; j++)
          for (int m = 0; m < cycle.size(); m++)
            trace.push_back(cycle[m]);

        ExprVector ssa;
        bnd.getSSA(trace, ssa);


        mergeIterationsFact(prefixRule, constt, ssa, bnd);
        // for (auto it : ssa)
        // {
        // 	outs() << "unrolling: " << *it << "\n";
        // }

		trace.clear();

		trace.push_back(prefix[0]);

		for (int j = 0; j < coef-1; j++)
          for (int m = 0; m < cycle.size(); m++)
            trace.push_back(cycle[m]);

        ExprVector ssa1;
        bnd.getSSA(trace, ssa1);
        
        mergeIterationsLoop(rule, coef-1, ssa1, bnd);
        ssa1.erase(ssa1.begin());

        if (constt > 0) prefixRule.body = conjoin(ssa, ruleManager.m_efac);
		if (coef > 1) rule.body = mk<AND>(rule.body, conjoin(ssa1, ruleManager.m_efac));

        // prefixRule.printMemberVars();
        // rule.printMemberVars();
	}

	bool findAlignment(CHCs &ruleManager1, CHCs &ruleManager2, SMTUtils &u)
	{
		auto &fac = ruleManager1.m_efac;

		vector<int> &cycle1 = ruleManager1.cycles[0];
		HornRuleExt &rule1 = ruleManager1.chcs[cycle1[0]];
		vector<int> &prefix1 = ruleManager1.prefixes[0];
		HornRuleExt &prefixRule1 = ruleManager1.chcs[prefix1[0]];
		Expr rel1 = rule1.srcRelation;
		int invNum1 = getVarIndex(rel1, ruleManager1.decls);
		Expr init1 = prefixRule1.body;

		vector<int> &cycle2 = ruleManager2.cycles[0];
		HornRuleExt &rule2 = ruleManager2.chcs[cycle2[0]];
		vector<int> &prefix2 = ruleManager2.prefixes[0];
		HornRuleExt &prefixRule2 = ruleManager2.chcs[prefix2[0]];
		Expr rel2 = rule2.srcRelation;
		int invNum2 = getVarIndex(rel2, ruleManager2.decls);
		Expr init2 = prefixRule2.body;

		int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;

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
		//     errs() << "vars: " << *rule1.dstVars[elems1[0]] << " and " << *rule2.dstVars[elems1[1]] << "\n";
		//   }
		//   errs() << "\n\n";
		// }

		for (auto &comb : nonIterCombinations)
		{
			Expr pre;
			bool skipComb = false;
			if (comb[0][0] != -1)
			{
				for (auto &pair : comb)
				{
					Expr var = rule1.srcVars[pair[0]];
					Expr var1 = rule2.srcVars[pair[1]];

					if ((!u.hasOneModel(var, init1) && !u.hasOneModel(var1, init2)) 
						|| (u.hasOneModel(var, init1) && u.hasOneModel(var1, init2)))
					{
						// errs() << "pair: " << pair[0] << " " << pair[1] << "\n";
						if (!pre) pre = mk<EQ>(rule1.dstVars[pair[0]], rule2.dstVars[pair[1]]);
						else pre = mk<AND>(pre, mk<EQ>(rule1.dstVars[pair[0]], rule2.dstVars[pair[1]]));
					}
					else
					{
						skipComb = true;
						break;
					}

				}
				if (skipComb) continue;

				// prefixRule.body = mk<AND>(prefixRule.body, pre);
			}
			else pre = mk<TRUE>(fac);
			// outs() << "pre: " << *pre << "\n";

			Expr e = replaceAll(pre, rule1.dstVars, rule1.srcVars);
			Expr post = replaceAll(e, rule2.dstVars, rule2.srcVars);
			Expr negPost = mkNeg(post);
			// outs() << "post: " << *post << "\n";

            // errs() << "\n\nassuming iters: " << *rule1.srcVars[iter1] << " and " << *rule2.srcVars[iter2] << "\n";
            Expr numIters1 = ruleManager1.numOfIters;
            Expr numIters2 = ruleManager2.numOfIters;
            // outs() << "numIters: " << *numIters1 << " and " << *numIters2 << "\n";

            Expr coef1 = bind::intConst(mkTerm<string>("coef1", fac));
            Expr coef2 = bind::intConst(mkTerm<string>("coef2", fac));

            Expr const1 = bind::intConst(mkTerm<string>("const1", fac));
            Expr const2 = bind::intConst(mkTerm<string>("const2", fac));
            
            Expr minCoef1, minCoef2, minConst1, minConst2;

            Expr quantifiedFla;

            if (!(numIters1 == mkMPZ(-1, fac) || numIters2 == mkMPZ(-1, fac))) 
            {
              Expr coefs = mk<AND>(mk<GT>(coef1, mkMPZ(0, fac)), mk<GT>(coef2, mkMPZ(0, fac)));
              Expr consts = mk<AND>(mk<GEQ>(const1, mkMPZ(0, fac)), mk<GEQ>(const2, mkMPZ(0, fac)));

              Expr numIters = bind::intConst(mkTerm<string>("numIters1", fac));
              Expr numItersP = bind::intConst(mkTerm<string>("numIters2", fac));

              Expr fla = mk<AND>(mk<EQ>(numIters, numIters1), mk<EQ>(numItersP, numIters2));

              // outs() << "fla: " << *fla << "\n";

              ExprVector varsIters;
              Expr extraRels;

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

            	// outs() << "extraRels: " << *extraRels << "\n";

              Expr newPre = extraRels;

              for (auto &p : comb)
              {
                Expr v = rule1.srcVars[p[0]];
                Expr v1 = rule2.srcVars[p[1]];
                if (!isOpX<ARRAY_TY>(bind::typeOf(v)))
                {
                  if (newPre) newPre = mk<AND>(newPre, mk<EQ>(v, v1));
                  else newPre = mk<EQ>(v, v1);
                }
              }

              if (!newPre) newPre = mk<TRUE>(fac);
              // newPre = mk<AND>(newPre, mk<AND>(rule1.body, rule2.body));

              fla = mk<AND>(newPre, fla);
              Expr implFla = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters, const1)), 
              	mk<MULT>(coef1, mk<MINUS>(numItersP, const2)));
              
              // outs() << "fla: " << *fla << "\n";
              varsIters.clear();
              filter(fla, IsConst(), inserter(varsIters, varsIters.begin()));
              
              fla = mk<IMPL>(fla, implFla); 

              quantifiedFla = createQuantifiedFormulaRestr(fla, varsIters);
              quantifiedFla = mk<AND>(consts, mk<AND>(coefs, quantifiedFla));

              Expr constsZero = mk<AND>(mk<EQ>(const1, mkMPZ(0, fac)), mk<EQ>(const2, mkMPZ(0, fac)));
              Expr const1Zero = mk<EQ>(const1, mkMPZ(0, fac));
              Expr const2Zero = mk<EQ>(const2, mkMPZ(0, fac));

              // outs() << "quantifiedFla 1 and 2: " << *mk<AND>(quantifiedFla, constsZero) << "\n";
              
              // ruleManager1.u.serialize_formula(quantifiedFla);

              Expr model;
              if (u.isSat(mk<AND>(quantifiedFla, constsZero))) model = u.getModel();
              else if (u.isSat(mk<AND>(quantifiedFla, const1Zero))) model = u.getModel();
              else if (u.isSat(mk<AND>(quantifiedFla, const2Zero))) model = u.getModel();
              else if (u.isSat(quantifiedFla)) model = u.getModel();
              else outs() << "Not satisfiable\n";

              if (model) 
              {
                // outs() << "model: " << *model << "\n";
                Expr minModels = u.getMinModelInts(coef1);
                // outs() << "minModels: " << *minModels << "\n";

                findExpr<EQ>(coef1, minModels, minCoef1, true);
                findExpr<EQ>(coef2, minModels, minCoef2, true);
                findExpr<EQ>(const1, minModels, minConst1, true);
                findExpr<EQ>(const2, minModels, minConst2, true);

                Expr vals = mk<AND>(minCoef1, minCoef2);

                u.isSat(mk<AND>(quantifiedFla, vals));

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
            }
            else outs() << "number of iterations were not found\n";


            // outs() << "copy " << *minConst1 << " iterations of loop 1 to fact\n";
            // outs() << "copy " << *minConst2 << " iterations of loop 2 to fact\n";
            // outs() << "we need " << *minCoef1 << " iterations of loop 1 to align\n";
            // outs() << "we need " << *minCoef2 << " iterations of loop 2 to align\n";

            int coef1Int = (int)lexical_cast<cpp_int>(minCoef1);
			int const1Int = (int)lexical_cast<cpp_int>(minConst1);
			int coef2Int = (int)lexical_cast<cpp_int>(minCoef2);
			int const2Int = (int)lexical_cast<cpp_int>(minConst2);

      if (const1Int != 0) const1Int++;
      if (const2Int != 0) const2Int++;
      outs () << const1Int << " " << const2Int << "\n";
			createAlignment(ruleManager1, coef1Int, const1Int);
			createAlignment(ruleManager2, coef2Int, const2Int);

			CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_");

		    vector<vector<HornRuleExt>> queries(2);

		    // get queries of both systems
		    getQueries(ruleManager1.chcs, ruleManager2.chcs, queries);

		    if (queries[0].empty() || queries[1].empty())
		    {
		        outs() << "Product can not be found.\n";
		        continue;
		    }

		    // product of two CHC systems
			Product(ruleManagerProduct, queries);

			HornRuleExt *fact, *query, *ind;
			for (auto &it : ruleManagerProduct.chcs)
			{
				if (it.isFact) fact = &it;
				if (it.isQuery) query = &it;
				if (it.isInductive) ind = &it;
			}
			fact->body = mk<AND>(fact->body, pre);
			query->body = simplifyBool(mk<AND>(query->body, negPost));

      outs () << "   check fact sanity:  "  << bool(u.isSat(fact->body)) << "\n";
      outs () << "   check query sanity:  "  << bool(u.isSat(query->body)) << "\n";
      outs () << "   check ind sanity:  "  << bool(u.isSat(ind->body)) << "\n";

			outs() << "------------------------CREATING ALIGNED PROGRAM DONE-----------------------------\n\n";

//      ruleManagerProduct.print();
			// for (auto &it : ruleManagerProduct.chcs)
			// {
			// 	it.printMemberVars();
			// }

			Expr currentMatching;
			int sz = rule1.srcVars.size();
			for (auto &pair : comb)
			{
				Expr eq = mk<EQ>(ind->srcVars[pair[0]], ind->srcVars[sz+pair[1]]);
				if (currentMatching) currentMatching = mk<AND>(currentMatching, eq);
				else currentMatching = eq;
			}

			// outs() << "currentMatching: " << *currentMatching << "\n";

		    if (learnInvariantsPr(ruleManagerProduct, 2000000, false, false, currentMatching)) return true;
		}
		return false;
	}

	inline void createProduct(const char *chcfileSrc, const char *chcfileDst)
	{
		ExprFactory m_efac;
		EZ3 z3(m_efac);

		CHCs ruleManagerSrc(m_efac, z3, "_v1_");
		ruleManagerSrc.parse(string(chcfileSrc));

		// CHCs ruleManagerSrcOrig(m_efac, z3, "_v1_");
		// ruleManagerSrcOrig.parse(string(chcfileSrc));

		/*outs() << "eliminateQuantifiers:\n";
		for (auto it : ruleManagerSrc.chcs)
		{
			// ExprVector v;
			// Expr q = createQuantifiedFormula(it.body, v);
			// SMTUtils su(it.body->getFactory());
			// su.serialize_formula(q);
			outs() << "is inductive: " << it.isInductive << ", is fact: " << it.isFact << "\n";
			Expr body = it.body;
			for (auto v : it.locVars)
			{
				outs() << "eliminating: " << *v << "\n";
				ExprSet s{v};
				body = eliminateQuantifiers(body, s);
				outs() << "body: " << *body << "\n";
			}
		}*/

		// for (auto it : ruleManagerSrc.chcs) it.printMemberVars();

		CHCs ruleManagerDst(m_efac, z3, "_v2_");
		ruleManagerDst.parse(string(chcfileDst));

		// CHCs ruleManagerDstOrig(m_efac, z3, "_v2_");
		// ruleManagerDstOrig.parse(string(chcfileDst));
		
		// for (auto it : ruleManagerDst.chcs) it.printMemberVars();

		ruleManagerSrc.findIterators();
		ruleManagerDst.findIterators();

		bool equiv = findAlignment(ruleManagerSrc, ruleManagerDst, ruleManagerSrc.u);
		if (equiv) outs() << "programs are equivalent\n";
		else outs() << "programs are not equivalent\n";

		/*CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_");

	    vector<vector<HornRuleExt>> queries(2);

	    // get queries of both systems
	    getQueries(ruleManager1.chcs, ruleManager2.chcs, queries);

	    if (queries[0].empty() || queries[1].empty())
	    {
	        outs() << "Product can not be found.\n";
	        continue;
	    }

	    // product of two CHC systems
		Product(ruleManagerProduct, queries);

		learnInvariantsPr(ruleManagerProduct, 2000000, false, false, currentMatching);*/
  };
}

#endif
