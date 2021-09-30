#ifndef EQUIVALENCE__HPP__
#define EQUIVALENCE__HPP__

#include "Extended_Horn.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

	class Product_CHCs : public Extended_CHCs
	{
	public:
	    Extended_CHCs* subRule1;
	    Extended_CHCs* subRule2;

	    Product_CHCs(Extended_CHCs &rules1, Extended_CHCs &rules2, string n, int d = false) : 
	    	Extended_CHCs(rules1.m_efac, rules1.m_z3, n, d), subRule1(&rules1), subRule2(&rules2) {};

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
			for (auto &chc : chcs) 
			{
				ExprVector srcVars = chc.srcVars, dstVars = chc.dstVars;
				
				// might add dstVars of one of the CHCs to product locVars twice in some cases, should not be a problem
				concatenateVectors(chc.locVars, srcVars, dstVars);
				chc.srcVars.clear(); chc.dstVars.clear();

				ExprSet eqs;
				chc.assignVarsAndRewrite(srcVars, invVars[chc.srcRelation], dstVars, invVarsPrime[chc.dstRelation], eqs);
				chc.body = mk<AND>(chc.body, conjoin(eqs, m_efac));

				// for srcFactVars and dstQueryVars, we might add unnecessary relations to the body, 
				// also the locVars might contain duplicate variables. Fix later
				if (chc.isFact)
				{
					ExprVector prodVars = invVars[chc.dstRelation];
					for (int i = 0; i < srcFactVars.size(); i++)
						chc.body = mk<AND>(chc.body, mk<EQ>(srcFactVars[i], prodVars[i]));
					chc.locVars.insert(chc.locVars.end(), srcFactVars.begin(), srcFactVars.end());
					srcFactVars = prodVars;
				}

				if (chc.isQuery)
				{
					ExprVector prodVarsPrime = invVarsPrime[chc.srcRelation];
					for (int i = 0; i < dstQueryVars.size(); i++)
						chc.body = mk<AND>(chc.body, mk<EQ>(dstQueryVars[i], prodVarsPrime[i]));
					chc.locVars.insert(chc.locVars.end(), dstQueryVars.begin(), dstQueryVars.end());
					dstQueryVars = prodVarsPrime;
				}

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

			concatenateVectors(srcFactVars, subRule1->srcFactVars, subRule2->srcFactVars);
			concatenateVectors(dstQueryVars, subRule1->dstQueryVars, subRule2->dstQueryVars);

			HornRuleExt queryPr;

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
    unsigned maxAttempts = 2000000, to = 10000;
    bool freqs = false, aggp = false, enableDataLearning = false, doElim = true, doDisj = false;
    bool dAllMbp = false, dAddProp = false, dAddDat = false, dStrenMbp = false, dSee = true;
    int debug = 0, doProp = 0, mbpEqs = 0, mut = 0;

	  if (doDisj && (!dAddProp && !dAddDat))
	    dAddDat = true;

	  if (doDisj && doProp == 0) doProp = 1;
	  if (dAllMbp || dAddProp || dAddDat || dStrenMbp) doDisj = true;
	  if (doDisj) 
	  {
	  	if (!dSee)
	      dSee = true;
	  	enableDataLearning = true;
	  }
    
    EZ3 z3(ruleManager.m_efac);
    BndExpl bnd(ruleManager, to, debug);

    RndLearnerV3 ds(ruleManager.m_efac, z3, ruleManager, to, freqs, aggp, mut, 
    								doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, to, debug);

    map<Expr, ExprSet> cands;
    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr dcl = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      if (ds.initializedDecl(dcl)) continue;
      ds.initializeDecl(dcl);
      if (!dSee) continue;

      Expr pref = bnd.compactPrefix(i);
      ExprSet tmp;
      getConj(pref, tmp);
      for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[dcl]))
          cands[dcl].insert(t);

      if (mut > 0) ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
      ds.initializeAux(cands[dcl], bnd, i, pref);
    }

    if (enableDataLearning) ds.getDataCandidates(cands);

    for (auto & dcl: ruleManager.wtoDecls)
    {
      for (int i = 0; i < doProp; i++)
        for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
      ds.addCandidates(dcl, cands[dcl]);
      ds.prepareSeeds(dcl, cands[dcl]);
    }

    // call bootstrap with option to only consider equalities as candidates for finding invariant
    // also add equalities for variable matchings
    bool check = ds.bootstrap(currentMatching, true);
    return check && ds.verifySolution(currentMatching);

    /*ds.calculateStatistics();
    ds.deferredPriorities();
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, doDisj);*/
  }


  bool getAlignmentVals(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, Expr pre, vector<int> &vals)
  {
  	auto &fac = ruleManager1.m_efac;
		SMTUtils u(fac);
		int cycleNum1 = 0, cycleNum2 = 0;

		vector<int> &cycle1 = ruleManager1.cycles[cycleNum1];
		HornRuleExt &rule1 = ruleManager1.chcs[cycle1[0]];

		vector<int> &cycle2 = ruleManager2.cycles[cycleNum2];
		HornRuleExt &rule2 = ruleManager2.chcs[cycle2[0]];

  	int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;
  	outs() << "\n\nassuming iters: " << *rule1.srcVars[iter1] << " and " << *rule2.srcVars[iter2] << "\n";
    Expr numIters1 = ruleManager1.numOfIters;
    Expr numIters2 = ruleManager2.numOfIters;
    outs() << "numIters: " << *numIters1 << " and " << *numIters2 << "\n";

    if (numIters1 == mkMPZ(-1, fac) || numIters2 == mkMPZ(-1, fac)) 
    {
    	outs() << "number of iterations were not found\n";
    	return false; 
    }

  	// create a quantified formula for optimization query
    Expr coef1 = bind::intConst(mkTerm<string>("coef1", fac));
    Expr coef2 = bind::intConst(mkTerm<string>("coef2", fac));

    Expr const1 = bind::intConst(mkTerm<string>("const1", fac));
    Expr const2 = bind::intConst(mkTerm<string>("const2", fac));
    
    Expr minCoef1, minCoef2, minConst1, minConst2;

    Expr quantifiedFla;

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

    fla = mk<AND>(pre, fla);
    Expr implFla = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters, const1)), 
    	mk<MULT>(coef1, mk<MINUS>(numItersP, const2)));
    
    filter(fla, IsConst(), inserter(varsIters, varsIters.begin()));
    
    fla = mk<IMPL>(fla, implFla); 

    quantifiedFla = createQuantifiedFormulaRestr(fla, varsIters);
    quantifiedFla = mk<AND>(consts, mk<AND>(coefs, quantifiedFla));

    outs() << "quantifiedFla: " << quantifiedFla << "\n";

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
    	return false;
    }
    
    if (model) 
    {
    	// outs() << "model: " << model << "\n";
			// iterative solving optimization query to get all minmodels
      minCoef1 = u.getMinModel(coef1);
    	quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef1, minCoef1));
      u.isSat(quantifiedFla);
      minCoef2 = u.getMinModel(coef2);
    	quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef2, minCoef2));
      u.isSat(quantifiedFla);
      minConst1 = u.getMinModel(const1);
      quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(const1, minConst1));
      u.isSat(quantifiedFla);
      minConst2 = u.getMinModel(const2);
    }
		else
		{
			outs() << "No satisfying assignment for quantified formula was found\n";
			return false;
		}

    outs() << "copy " << minConst1 << " iterations of loop 1 to fact and query combined\n";
    outs() << "copy " << minConst2 << " iterations of loop 2 to fact and query combined\n";
    outs() << "we need " << minCoef1 << " iterations of loop 1 to align\n";
    outs() << "we need " << minCoef2 << " iterations of loop 2 to align\n";

    vals.push_back((int)lexical_cast<cpp_int>(minCoef1));
    vals.push_back((int)lexical_cast<cpp_int>(minConst1));
    vals.push_back((int)lexical_cast<cpp_int>(minCoef2));
    vals.push_back((int)lexical_cast<cpp_int>(minConst2));

    return true;
  }

  bool alignPrograms(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, vector<vector<int>> &combVars, int debug)
	{
		auto &fac = ruleManager1.m_efac;
		SMTUtils u(fac);
		int cycleNum1 = 0, cycleNum2 = 0;

		vector<int> &cycle1 = ruleManager1.cycles[cycleNum1];
		HornRuleExt &rule1 = ruleManager1.chcs[cycle1[0]];
		vector<int> &prefix1 = ruleManager1.prefixes[cycleNum1];
		HornRuleExt &prefixRule1 = ruleManager1.chcs[prefix1[0]];

		vector<int> &cycle2 = ruleManager2.cycles[cycleNum2];
		HornRuleExt &rule2 = ruleManager2.chcs[cycle2[0]];
		vector<int> &prefix2 = ruleManager2.prefixes[cycleNum2];
		HornRuleExt &prefixRule2 = ruleManager2.chcs[prefix2[0]];

		BndExpl bnd1(ruleManager1, debug);
		BndExpl bnd2(ruleManager2, debug);

		Expr pref1 = bnd1.compactPrefix(cycleNum1), pref2 = bnd2.compactPrefix(cycleNum2);

		int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;

		Expr iterFVal, iterSVal;

		ruleManager1.findInitialValue(iter1, pref1, rule1, iterFVal, u);
		ruleManager2.findInitialValue(iter2, pref2, rule2, iterSVal, u);

		Expr preForEqualityCheck = mk<TRUE>(fac), preForQuantifiedFla = mk<TRUE>(fac);
		
		// checks if initial values of iterators depend on any variables; also constant values are also added to pre
		// we might as well check that the pair[1] variable is also constant, similar to third check
		// arrays are not added because they make it difficult for solver to find solution
		if (combVars[0][0] != -1)
		{
			for (auto &pair : combVars)
			{
				Expr var1Src = rule1.srcVars[pair[0]];
				Expr var2Src = rule2.srcVars[pair[1]];
				Expr var1Dst = rule1.dstVars[pair[0]];
				Expr var2Dst = rule2.dstVars[pair[1]];

				// check if for any pair, one has a model in prefix and other one does not;
				// if we encounter such scenario, we cannot argue about equivalence in terms of such pair
				if ((u.hasOneModel(var1Src, pref1) || u.hasOneModel(var2Src, pref2)) 
					&& !(u.hasOneModel(var1Src, pref1) && u.hasOneModel(var2Src, pref2))) return false;

				// we create here the pre required for quantified formula and pre to check equality of iters later
				// we do not want to add arrays to any of the pre version
				if (!isOpX<ARRAY_TY>(bind::typeOf(var1Src)))
				{
					// if any pair of vars the initial values of iters are depending, we want to add the 
					// equality constraint for that var pair; we need this for both pre versions; 
					// we also want to add any constants e.g. count, that will be required in the quantified formula
					// we do not need this for pre to check equality of iters, but it does not hurt to add
					if (contains(iterFVal, var1Src) || contains(iterSVal, var2Src) 
						|| u.implies(rule1.body, mk<EQ>(var1Src, var1Dst)) || u.implies(rule2.body, mk<EQ>(var2Src, var2Dst)))
					{
						preForEqualityCheck = mk<AND>(preForEqualityCheck, mk<EQ>(var1Dst, var2Dst));
						preForQuantifiedFla = mk<AND>(preForQuantifiedFla, mk<EQ>(var1Src, var2Src));
					}
				}
			}
		}

		vector<int> alignmentVals;
		if (!getAlignmentVals(ruleManager1, ruleManager2, preForQuantifiedFla, alignmentVals)) return false;
		
		int coef1Int = alignmentVals[0];
		int const1Int = alignmentVals[1];
		int coef2Int = alignmentVals[2];
		int const2Int = alignmentVals[3];

		// Currently, it does all combinations to check the number of iterations to be added to fact and query
		vector<int> v1, v2;
		vector<vector<int>> possibleFactQueryAligns;
		for (int i = 0; i <= const1Int; i++) v1.push_back(i);
		for (int i = 0; i <= const2Int; i++) v2.push_back(i);

		for (auto &it : v1)
			for (auto &it2 : v2)
				possibleFactQueryAligns.push_back(vector<int>{it, it2});

		 // for (auto it : possibleFactQueryAligns)
		 // 	outs() << it[0] << " " << const1Int-it[0] << " " << it[1] << " " << const2Int-it[1] << "\n";

		Expr iterF = rule1.dstVars[iter1];
		Expr iterS = rule2.dstVars[iter2];

		ExprVector dummy;

		bool impliesEq = false;
		for (auto &possibleAlign : possibleFactQueryAligns)
		{
			// check if adding certain iterations to query will make the initial values of iterators equal
			// it is not greedy approach currently
			Expr prefRuleBody1, prefRuleBody2;
			ruleManager1.createAlignment(0, possibleAlign[0], 0, prefRuleBody1, dummy, dummy, bnd1, false);
			ruleManager2.createAlignment(0, possibleAlign[1], 0, prefRuleBody2, dummy, dummy, bnd2, false);

			Expr tempProdFact = mk<AND>(mk<AND>(prefRuleBody1, prefRuleBody2), preForEqualityCheck);
			Expr eq = mk<EQ>(iterF, iterS);
			impliesEq = bool(u.implies(tempProdFact, eq));

			if (impliesEq)
			{
				ExprVector prefRuleLocVars1, prefRuleLocVars2;
				ExprVector lastIterVars1, lastIterVars2;
				// actual alignment created here
				ruleManager1.createAlignment(coef1Int, possibleAlign[0], const1Int-possibleAlign[0], prefRuleBody1, 
					prefRuleLocVars1, lastIterVars1, bnd1);
				prefixRule1.body = prefRuleBody1;
				std::copy(prefRuleLocVars1.begin(), prefRuleLocVars1.end(), std::back_inserter(prefixRule1.locVars));
				
				ruleManager2.createAlignment(coef2Int, possibleAlign[1], const2Int-possibleAlign[1], prefRuleBody2, 
					prefRuleLocVars2, lastIterVars2, bnd2);
				prefixRule2.body = prefRuleBody2;
				std::copy(prefRuleLocVars2.begin(), prefRuleLocVars2.end(), std::back_inserter(prefixRule2.locVars));

				if (const1Int-possibleAlign[0] > 0)
					ruleManager1.fixLoopGuard(lastIterVars1);

				if (const2Int-possibleAlign[1] > 0)
					ruleManager2.fixLoopGuard(lastIterVars2);

				// break out of the loop if for any alignment, we have iterators initially equal;
				// consequently, all remaining iterations are added to query; 
				// support checking other combinations
				break;
			}

		}

		HornRuleExt *query1 = ruleManager1.getQuery(), *query2 = ruleManager2.getQuery();

		if (ruleManager1.srcFactVars.empty()) ruleManager1.srcFactVars = prefixRule1.dstVars;
		if (ruleManager2.srcFactVars.empty()) ruleManager2.srcFactVars = prefixRule2.dstVars;
		if (ruleManager1.dstQueryVars.empty()) ruleManager1.dstQueryVars = query1->srcVars;
		if (ruleManager2.dstQueryVars.empty()) ruleManager2.dstQueryVars = query2->srcVars;

		// if impliesEq is false, iterator values do not match for any number of iterations and no alignment found
		return impliesEq;
	}


	void createMultipleCombinationsForVars(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2
			, vector<vector<vector<int>>> &nonIterCombinations)
	{
		vector<vector<vector<int>>> combsArray, combsInt, combsBool, combs1;
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
	}


	bool checkEquivalence(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, vector<vector<int>> &combVars)
	{
		int debug = 0;
		// create the product CHC system 
		Product_CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_", debug-2);

	    // product of two CHC systems
		ruleManagerProduct.createProduct();

		// create pre and post conditions
		Expr pre = mk<EQ>(ruleManager1.srcFactVars[ruleManager1.iter], ruleManager2.srcFactVars[ruleManager2.iter]); 
		Expr post = mk<EQ>(ruleManager1.dstQueryVars[ruleManager1.iter], ruleManager2.dstQueryVars[ruleManager2.iter]);
		if (combVars[0][0] != -1)
		{
			for (auto &pair : combVars)
			{
				pre = mk<AND>(pre, mk<EQ>(ruleManager1.srcFactVars[pair[0]], ruleManager2.srcFactVars[pair[1]]));
				post = mk<AND>(post, mk<EQ>(ruleManager1.dstQueryVars[pair[0]], ruleManager2.dstQueryVars[pair[1]]));
			}
		}

		Expr negPost = mkNeg(post);

		HornRuleExt *fact, *query, *ind;
		for (auto &it : ruleManagerProduct.chcs)
		{
			// it.printMemberVars();
			if (it.isFact) fact = &it;
			if (it.isQuery) query = &it;
			if (it.isInductive) ind = &it;
		}
		fact->body = mk<AND>(fact->body, pre);
		query->body = simplifyBool(mk<AND>(query->body, negPost));
		// ruleManagerProduct.serializeFormulas();

		// outs() << "fact: " << *fact->body << "\n";
		// outs() << "query: " << *query->body << "\n";

		auto &fac = ruleManagerProduct.m_efac;
		SMTUtils u(fac);

		outs () << "   check fact sanity:  "  << bool(u.isSat(fact->body)) << "\n";
		outs () << "   check query sanity:  "  << bool(u.isSat(query->body)) << "\n";
		outs () << "   check ind sanity:  "  << bool(u.isSat(ind->body)) << "\n";

		outs() << "------------------------CREATING ALIGNED PRODUCT DONE-----------------------------\n\n";

		Expr currentMatching = mk<TRUE>(fac);
		int sz = ind->srcVars.size()/2;

		// for (auto chc: ruleManagerProduct.chcs)
			// u.serialize_formula2(chc.body);

		// GF: hack to create pairs (to revisit) -- visited, works well
		for (int i = 0; i < sz; i++)
			if (bind::typeOf(ind->srcVars[i]) == bind::typeOf(ind->srcVars[sz + i]))
				currentMatching = mk<AND>(currentMatching, mk<EQ>(ind->srcVars[i], (ind->srcVars[sz + i])));

		// call the function with all default values for arguments that are not relevant
		// probably, do a cleaner way of calling the function
	    return learnInvariantsPr(ruleManagerProduct, currentMatching);
	}


	// check equivalence of programs with alignment
	inline void checkEquivalenceWithAligning(const char *chcfileSrc, const char *chcfileDst)
	{
		ExprFactory m_efac;
		EZ3 z3(m_efac);

		int debug = 0;
		Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-2);
		ruleManagerSrc.parse(string(chcfileSrc));

		Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_", debug-2);
		ruleManagerDst.parse(string(chcfileDst));

		ruleManagerSrc.extraProcessing();
		ruleManagerDst.extraProcessing();

		BndExpl bndSrc(ruleManagerSrc, debug);
		BndExpl bndDst(ruleManagerDst, debug);

		// if no iterator was found, the tool exits stating non-equivalence. Support more
		for (int i = 0; i < ruleManagerSrc.cycles.size(); i++) 
		{
			bool iterFound = ruleManagerSrc.findIterators(bndSrc, i);
			if (!iterFound) 
			{
				outs() << "no iterator was found for program 1. programs are not equivalent\n";
				return;
			}
		}

		for (int i = 0; i < ruleManagerDst.cycles.size(); i++) 
		{
			bool iterFound = ruleManagerDst.findIterators(bndDst, i);
			if (!iterFound) 
			{
				outs() << "no iterator was found for program 2. programs are not equivalent\n";
				return;
			}
		}

		vector<vector<vector<int>>> nonIterCombinations;
		createMultipleCombinationsForVars(ruleManagerSrc, ruleManagerDst, nonIterCombinations);

		bool aligned;
		// check for all combinations of variables, such that we match same type of variables
		for (auto &comb : nonIterCombinations)
		{
			Extended_CHCs ruleManagerSrcCopy = ruleManagerSrc, ruleManagerDstCopy = ruleManagerDst;
			aligned = alignPrograms(ruleManagerSrcCopy, ruleManagerDstCopy, comb, debug);
			if (aligned) 
			{
				if (checkEquivalence(ruleManagerSrcCopy, ruleManagerDstCopy, comb)) 
				{
					outs() << "\nprograms are equivalent\n";
					return;
				}
			}
		}
		outs() << "\nprograms are not equivalent\n";
  };


  	// check equivalence of programs with no alignment
	inline void checkEquivalenceWithoutAligning(const char *chcfileSrc, const char *chcfileDst)
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
