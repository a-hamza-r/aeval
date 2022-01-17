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

			getSpecificSrcRelations(chc1.srcRelation, chc1.dstRelation, false, chc1NonRecPart);
			getSpecificSrcRelations(chc2.srcRelation, chc2.dstRelation, false, chc2NonRecPart);

			bool chc1NonRec = !chc1NonRecPart.empty();
			bool chc2NonRec = !chc2NonRecPart.empty();

			if (chc1NonRec)
			{
				product = chc1NonRecPart[0];
				vars.insert(vars.end(), subRule1->invVars[product].begin(), subRule1->invVars[product].end());
				for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
				{
					rel = *it;
					product = mk<AND>(product, rel);
					vars.insert(vars.end(), subRule1->invVars[rel].begin(), subRule1->invVars[rel].end());
				}
			}

			if (chc2NonRec)
			{
				rel = chc2NonRecPart[0];
				if (!product) product = rel;
				else product = mk<AND>(product, rel);
				vars.insert(vars.end(), subRule2->invVars[rel].begin(), subRule2->invVars[rel].end());
				for (auto it = chc2NonRecPart.begin()+1; it != chc2NonRecPart.end(); it++)
				{
					rel = *it;
					product = mk<AND>(product, rel);
					vars.insert(vars.end(), subRule2->invVars[rel].begin(), subRule2->invVars[rel].end());
				}
			}
		}


		void getSpecificSrcRelations(Expr srcRelation, Expr dstRelation, bool recursive, ExprVector &partitions)
		{
			Expr decl;
			if (isOpX<AND>(srcRelation))
			{
				for (int i = 0; i < srcRelation->arity(); i++)
					getSpecificSrcRelations(srcRelation->arg(i), dstRelation, recursive, partitions);
			}
			else if (!isOpX<TRUE>(srcRelation))
			{
				if ((recursive && srcRelation == dstRelation) || (!recursive && srcRelation != dstRelation))
					partitions.push_back(srcRelation);
			}
		}


		void RTransform(HornRuleExt &chc, ExprVector &transformed, int pos)
		{
			Expr decl;
			if (!chc.isInductive)
			{
				if (pos == 0) decl = subRule1->getDecl(chc.dstRelation);
				else decl = subRule2->getDecl(chc.dstRelation);
				transformed.push_back(bind::fapp(decl, chc.dstVars));
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

			RTransform(chc1, transformed, 0);	RTransform(chc2, transformed, 1);

			// might have to check if there are more than two relation symbols in transformed
			productRelationSymbols(ExprVector{transformed[0]->left()->left(), transformed[1]->left()->left()},
				product, nullV, false);

			// remove head(C) from body
			if (bind::fapp(transformed[0]->left(), chc1.dstVars) == transformed[0]
				&& bind::fapp(transformed[1]->left(), chc2.dstVars) == transformed[1])
			{
				product = NULL;
			}
			else
			{
				vars.insert(vars.end(), transformed[0]->args_begin()+1, transformed[0]->args_end());
				vars.insert(vars.end(), transformed[1]->args_begin()+1, transformed[1]->args_end());

				product = product->left();
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
      // GF: refactored: used to be too complicated for such a simple algorithm
			vector<HornRuleExt*> rules1, rules2;
			subRule1->rulesOfPredicate(rel1, rules1);
      subRule2->rulesOfPredicate(rel2, rules2);
      assert(rules1.size() == rules2.size());

      for (auto &it1 : rules1)
        for (auto &it2 : rules2)
          productOfCHCs(*it1, *it2, rulesOfP);
    }


		void productRelationSymbols(ExprVector predicates, Expr &predicateP, vector<HornRuleExt> &rulesOfP,
			bool calculateRulesOfP)
		{
			ExprVector productTypes;
			Expr rel1 = predicates[0], rel2 = predicates[1];

			Expr decl1 = subRule1->getDecl(rel1), decl2 = subRule2->getDecl(rel2);

			Expr productRel = mkTerm<string>(lexical_cast<string>(rel1) + "*" +
				lexical_cast<string>(rel2), m_efac);

			productTypes.insert(productTypes.end(), decl1->args_begin()+1, decl1->args_begin()+decl1->arity()-1);
			productTypes.insert(productTypes.end(), decl2->args_begin()+1, decl2->args_begin()+decl2->arity());

			predicateP = bind::fdecl(productRel, productTypes);

			if (calculateRulesOfP)
				calculateProductOfRules(rel1, rel2, rulesOfP);
		}


		void productOfCHCs(HornRuleExt &chc1, HornRuleExt &chc2, vector<HornRuleExt> &rulesOfP)
		{
      // GF: use the global `debug` option for all such prints
      outs () << "  product of two CHCs: "
          << chc1.srcRelation << " -> " << chc1.dstRelation << " and "
          << chc2.srcRelation << " -> " << chc2.dstRelation << "\n";
			Expr head, body;
			vector<HornRuleExt> nullV;
			vector<ExprVector> nullV1;
			HornRuleExt newProductRule;

			// head product
			productRelationSymbols(ExprVector{chc1.dstRelation, chc2.dstRelation}, head, nullV, false/*, nullV1*/);
			newProductRule.dstRelation = head->left();
			concatenateVectors(newProductRule.dstVars, chc1.dstVars, chc2.dstVars);

			// body product
			bodyProduct(chc1, chc2, newProductRule);

			concatenateVectors(newProductRule.locVars, chc1.locVars, chc2.locVars);

			// do not push if one is inductive and other one is not. Push in all other cases
			if ((newProductRule.isInductive && chc1.isInductive && chc2.isInductive) || !newProductRule.isInductive)
				rulesOfP.push_back(newProductRule);
		}

		void assignVarsAndRewrite()
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

				// for srcFactVars, we might add unnecessary relations to the body,
				// also the locVars might contain duplicate variables. Fix later
				if (chc.isFact)
				{
					ExprVector prodVars = invVars[chc.dstRelation];
					for (int i = 0; i < srcFactVars.size(); i++)
						chc.body = mk<AND>(chc.body, mk<EQ>(srcFactVars[i], prodVars[i]));
					chc.locVars.insert(chc.locVars.end(), srcFactVars.begin(), srcFactVars.end());
					srcFactVars = prodVars;
				}
			}
		}


		// generates the product of two CHC systems
		// At many places, it is assumed that there are only two systems,
		// hence the operations done are not generic i.e. for product of more than two CHC systems
		void createProduct()
		{
			vector<HornRuleExt> worklist;
			HornRuleExt C_a;

			concatenateVectors(srcFactVars, subRule1->srcFactVars, subRule2->srcFactVars);

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
        C_a = worklist[0];                     // GF: you should avoid copying here
				worklist.erase(worklist.begin());

				// AH: In the original algorithm, the operation PARTITION is used that is defined:
				// 'operator partition from a set to a set of its disjoint subsets'
				// Here, just one partition created of two symbols because there are only two relation symbols here

				// argument false for non-recursive; getting non-recursive parts of the srcrelation
				getSpecificSrcRelations(C_a.srcRelation, C_a.dstRelation, false, partition);
				getSpecificSrcRelations(C_a.srcRelation, C_a.dstRelation, false, partition);

				if (partition.size() >= 2)
				{
					// take product of relation symbols in partition,
					// true specified if product of rules of relations is to be calculated
					productRelationSymbols(partition, freshP, rulesOfP, true);
					C_a.srcRelation = freshP->left();

					worklist.insert(worklist.end(), rulesOfP.begin(), rulesOfP.end());
				}

				if (!isOpX<AND>(C_a.srcRelation))
				{
					// if freshP is not NULL, it went into the if-statement (partition.size() >= 2)
					if (freshP) addDecl(freshP);
					chcs.push_back(C_a);
				}
			}

			// changes variables from _v1_ and _v2_ prefixes to _pr_ with necessary changes
			assignVarsAndRewrite();

			for (int i = 0; i < chcs.size(); i++)
				outgs[chcs[i].srcRelation].push_back(i);

			// sort rules
			wtoSort();

			outs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
		}
	};


	class Equivalence
	{
		private:
			ExprFactory &m_efac;
	    EZ3 &m_z3;
			Extended_CHCs ruleManager1;
			Extended_CHCs ruleManager2;
			SMTUtils u;
			Expr phi;
			int itersOutLoopR1;
			int itersOutLoopR2;
			int itersInLoopR1;
			int itersInLoopR2;

		public:
			vector<vector<int>> pairings;
			unsigned maxAttempts;
			unsigned to;
			bool freqs;
			bool aggp;
			int dat;
			int mut;
			bool doElim;
			bool doArithm;
			bool doDisj;
			int doProp;
			int mbpEqs;
			bool dAllMbp;
			bool dAddProp;
			bool dAddDat;
			bool dStrenMbp;
			int dFwd;
			bool dRec;
			bool dGenerous;
			int debug;
			bool dSee;

			Equivalence(Extended_CHCs r1, Extended_CHCs r2, ExprFactory &efac, EZ3 &z3,
				vector<vector<int>> combs, unsigned _maxAttempts, unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut,
				bool _doElim, bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp, bool _dAddProp, bool _dAddDat,
				bool _dStrenMbp, int _dFwd, bool _dRec, bool _dGenerous, bool _dSee, int _debug) :
				m_efac(efac), m_z3(z3), u(efac, _to), ruleManager1(r1), ruleManager2(r2), pairings(combs),
				maxAttempts(_maxAttempts), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
				doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp), mbpEqs(_mbpEqs), dAllMbp(_dAllMbp),
				dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec),
				dGenerous(_dGenerous), dSee(_dSee), debug(_debug)
			 {}

	bool learnInvariantsPr(CHCs &ruleManager, ExprSet& currentMatching, unsigned maxAttempts,
		unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
		bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp, bool dAddDat,
		bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee)
  {

    if (debug > 4) ruleManager.print(true);
    BndExpl bnd(ruleManager, to, debug);

    RndLearnerV3 ds(ruleManager.m_efac, ruleManager.m_z3, ruleManager, to, freqs, aggp, mut, dat,
    								doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, to, debug);

    map<Expr, ExprSet> cands;
    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr dcl = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      if (ds.initializedDecl(dcl)) continue;
      ds.initializeDecl(dcl);
      cands[dcl] = currentMatching;  // adding the matching explicitly

      // GF: most likely, you won't need any of these,
      //     so I disabled it to improve performance.
      //     In case some bench requires a specific invariant,
      //     try to enable gradually.

			auto & chc = ruleManager.chcs[ruleManager.prefixes[i][0]];
			if (chc.dstRelation == dcl)
				for (auto & v : chc.dstVars)
				{
					if (containsOp<ARRAY_TY>(v)) continue;
					ExprVector tmp = {v};
					getConj(replaceAll(keepQuantifiers(chc.body, tmp),
						 chc.dstVars, ruleManager.invVars[dcl]), cands[dcl]);
				}
			// GF: if the code above takes significant time, make it parametric

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

    if (dat > 0) ds.getDataCandidates(cands);

    for (auto & dcl: ruleManager.wtoDecls)
    {
      for (int i = 0; i < doProp; i++)
        for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
      ds.addCandidates(dcl, cands[dcl]);
      ds.prepareSeeds(dcl, cands[dcl]);
    }

    // call bootstrap with option to only consider equalities as candidates for finding invariant
    // also add equalities for variable matchings
    bool check = ds.bootstrap();
    return check && ds.verifySolution(currentMatching);
  }


  bool getAlignmentVals(ExprSet& pre, Expr rel1, Expr rel2)
  {

  	int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;

  	outs() << "\n\nassuming iters: "
  		<< ruleManager1.invVars[rel1][iter1] << " and " << ruleManager2.invVars[rel2][iter2] << "\n";

    Expr numIters1 = ruleManager1.numOfIters;
    Expr numIters2 = ruleManager2.numOfIters;
    outs() << "numIters: " << numIters1 << " and " << numIters2 << "\n";

    if (numIters1 == mkMPZ(-1, m_efac) || numIters2 == mkMPZ(-1, m_efac))
    {
    	outs() << "number of iterations were not found\n";
    	return false;
    }

  	// create a quantified formula for optimization query
    Expr coef1 = bind::intConst(mkTerm<string>("coef1", m_efac));
    Expr coef2 = bind::intConst(mkTerm<string>("coef2", m_efac));

    Expr const1 = bind::intConst(mkTerm<string>("const1", m_efac));
    Expr const2 = bind::intConst(mkTerm<string>("const2", m_efac));

    Expr minCoef1, minCoef2, minConst1, minConst2, quantifiedFla;

    Expr coefs = mk<AND>(mk<GT>(coef1, mkMPZ(0, m_efac)), mk<GT>(coef2, mkMPZ(0, m_efac)));
    Expr consts = mk<AND>(mk<GEQ>(const1, mkMPZ(0, m_efac)), mk<GEQ>(const2, mkMPZ(0, m_efac)));

    Expr numIters = bind::intConst(mkTerm<string>("numIters1", m_efac));
    Expr numItersP = bind::intConst(mkTerm<string>("numIters2", m_efac));

    ExprVector varsIters;
    Expr implFla = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters, const1)),
    	mk<MULT>(coef1, mk<MINUS>(numItersP, const2)));

		for (auto it = pre.begin(); it != pre.end(); )
			if (emptyIntersect(*it, numIters1) &&
				  emptyIntersect(*it, numIters2)) it = pre.erase(it);
			else ++it;

		pre.insert(mk<EQ>(numIters, numIters1));
		pre.insert(mk<EQ>(numItersP, numIters2));

    filter(conjoin(pre, m_efac), IsConst(), inserter(varsIters, varsIters.begin()));

    Expr fla = mk<IMPL>(conjoin(pre, m_efac), implFla);

    quantifiedFla = createQuantifiedFormulaRestr(fla, varsIters);
    quantifiedFla = mk<AND>(consts, mk<AND>(coefs, quantifiedFla));

		ExprMap c1, c2, c12, m1, m2, m12;
		for (auto &c : {const1, const2}) c12[c] = mkMPZ(0, m_efac);
		c1[const1] = mkMPZ(0, m_efac);
		c2[const2] = mkMPZ(0, m_efac);

    Expr model = NULL;
    if (true == u.isSat(replaceAll(quantifiedFla, c12))) model = u.getModel();
    else if (true == u.isSat(replaceAll(quantifiedFla, c1))) model = u.getModel();
    else if (true == u.isSat(replaceAll(quantifiedFla, c2))) model = u.getModel();
    else if (true == u.isSat(quantifiedFla)) model = u.getModel();
		if (model == NULL)
    {
			outs() << "No satisfying assignment for quantified formula was found\n";
			return false;
    }

		// iterative solving optimization query to get all minmodels

  	ExprMap mp;	ExprSet s{coef1, coef2, const1, const2};

  	u.getOptModel<LT>(s, mp, coef1);
  	minCoef1 = mp[coef1];
  	quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef1, minCoef1));
    u.isSat(quantifiedFla);

  	u.getOptModel<LT>(s, mp, coef2);
  	minCoef2 = mp[coef2];
  	quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef2, minCoef2));
  	u.isSat(quantifiedFla);

  	u.getOptModel<LT>(s, mp, const1);
  	minConst1 = mp[const1];
  	quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(const1, minConst1));
  	u.isSat(quantifiedFla);

  	u.getOptModel<LT>(s, mp, const2);
  	minConst2 = mp[const2];

    itersInLoopR1 = (int)lexical_cast<cpp_int>(minCoef1);
    itersOutLoopR1 = (int)lexical_cast<cpp_int>(minConst1);
    itersInLoopR2 = (int)lexical_cast<cpp_int>(minCoef2);
    itersOutLoopR2 = (int)lexical_cast<cpp_int>(minConst2);

    outs() << "copy " << itersOutLoopR1 << " iterations of loop 1 to fact and query combined\n";
    outs() << "copy " << itersOutLoopR2 << " iterations of loop 2 to fact and query combined\n";
    outs() << "we need " << itersInLoopR1 << " iterations of loop 1 to align\n";
    outs() << "we need " << itersInLoopR2 << " iterations of loop 2 to align\n";

    return true;
  }

  bool initialSanityChecks()
  {
  	BndExpl bnd1(ruleManager1, debug);
		BndExpl bnd2(ruleManager2, debug);

  	Expr pref1 = bnd1.compactPrefix(0), pref2 = bnd2.compactPrefix(0);

  	for (int i = 0; i < ruleManager1.invVars[ruleManager1.loopRel].size(); i++)
		{
			Expr var1 = ruleManager1.invVars[ruleManager1.loopRel][i];
			Expr var2 = ruleManager2.invVars[ruleManager2.loopRel][i];

			// check if for any pair, one has a model in prefix and other one does not;
			// if we encounter such scenario, we cannot argue about equivalence in terms of such pair
			if (!((!u.hasOneModel(var1, pref1) && !u.hasOneModel(var2, pref2))
				|| (u.hasOneModel(var1, pref1) && u.hasOneModel(var2, pref2))))
			{
				return false;
			}
		}
		return true;
  }

  bool alignPrograms()
	{
		vector<int> &cycle1 = ruleManager1.cycles[0];
		HornRuleExt &rule1 = ruleManager1.chcs[cycle1[0]];
		vector<int> &prefix1 = ruleManager1.prefixes[0];
		HornRuleExt &prefixRule1 = ruleManager1.chcs[prefix1[0]];

		vector<int> &cycle2 = ruleManager2.cycles[0];
		HornRuleExt &rule2 = ruleManager2.chcs[cycle2[0]];
		vector<int> &prefix2 = ruleManager2.prefixes[0];
		HornRuleExt &prefixRule2 = ruleManager2.chcs[prefix2[0]];

		BndExpl bnd1(ruleManager1, debug);
		BndExpl bnd2(ruleManager2, debug);

		Expr pref1 = bnd1.compactPrefix(0), pref2 = bnd2.compactPrefix(0);

		int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;

		Expr iterFVal, iterSVal;

		ruleManager1.findInitialValue(iter1, pref1, rule1.srcRelation, iterFVal);
		ruleManager2.findInitialValue(iter2, pref2, rule2.srcRelation, iterSVal);

		ExprSet preForEqualityCheck, preForQuantifiedFla;

		// checks if initial values of iterators depend on any variables; also constant values are also added to pre
		// we might as well check that the pair[1] variable is also constant, similar to third check
		// arrays are not added because they make it difficult for solver to find solution
		if (pairings[0][0] != -1)
		{
			for (auto &pair : pairings)
			{
				Expr var1Src = rule1.srcVars[pair[0]];
				Expr var2Src = rule2.srcVars[pair[1]];
				Expr var1Dst = rule1.dstVars[pair[0]];
				Expr var2Dst = rule2.dstVars[pair[1]];

				// we create here the pre required for quantified formula and pre to check equality of iters later
				// we do not want to add arrays to any of the pre version
				if (!isOpX<ARRAY_TY>(bind::typeOf(var1Src)))
				{
				// 	// if any pair of vars the initial values of iters are depending, we want to add the
				// 	// equality constraint for that var pair; we need this for both pre versions;
				// 	// we also want to add any constants e.g. count, that will be required in the quantified formula
				// 	// we do not need this for pre to check equality of iters, but it does not hurt to add
				//
				// 	if (contains(iterFVal, var1Src) || contains(iterSVal, var2Src)
				// 		|| u.implies(rule1.body, mk<EQ>(var1Src, var1Dst)) || u.implies(rule2.body, mk<EQ>(var2Src, var2Dst)))
				// 	{
						preForEqualityCheck.insert(mk<EQ>(var1Dst, var2Dst));
						preForQuantifiedFla.insert(mk<EQ>(var1Src, var2Src));
				// 	}
				}
			}
		}

		if (!getAlignmentVals(preForQuantifiedFla, rule1.srcRelation, rule2.srcRelation)) return false;

		// Currently, it does all combinations to check the number of iterations to be added to fact and query
		vector<int> v1, v2;
		vector<vector<int>> possibleFactQueryAligns;
		for (int i = 0; i <= itersOutLoopR1; i++) v1.push_back(i);
		for (int i = 0; i <= itersOutLoopR2; i++) v2.push_back(i);

		for (auto &it : v1)
			for (auto &it2 : v2)
				possibleFactQueryAligns.push_back(vector<int>{it, it2});

		Expr iterF = rule1.dstVars[iter1];
		Expr iterS = rule2.dstVars[iter2];

		ExprVector dummy;

		bool impliesEq = false;
		for (auto &possibleAlign : possibleFactQueryAligns)
		{
 			// check if adding certain iterations to query will make the initial values of iterators equal
			// it is not greedy approach currently
			Expr prefRuleBody1, prefRuleBody2;
			ruleManager1.createAlignment(0, possibleAlign[0], 0, prefRuleBody1, dummy, bnd1, false);
			ruleManager2.createAlignment(0, possibleAlign[1], 0, prefRuleBody2, dummy, bnd2, false);

			preForEqualityCheck.insert(prefRuleBody1);
			preForEqualityCheck.insert(prefRuleBody2);

			Expr eq = mk<EQ>(iterF, iterS);
			impliesEq = bool(u.implies(mk<AND>(prefRuleBody1, prefRuleBody2), eq));

			if (impliesEq)
			{
				ExprVector prefRuleLocVars1, prefRuleLocVars2;
				// actual alignment created here
				ruleManager1.createAlignment(itersInLoopR1, possibleAlign[0], itersOutLoopR1-possibleAlign[0], prefRuleBody1,
					prefRuleLocVars1, bnd1);
				prefixRule1.body = prefRuleBody1;
				std::copy(prefRuleLocVars1.begin(), prefRuleLocVars1.end(), std::back_inserter(prefixRule1.locVars));

				ruleManager2.createAlignment(itersInLoopR2, possibleAlign[1], itersOutLoopR2-possibleAlign[1], prefRuleBody2,
					prefRuleLocVars2, bnd2);
				prefixRule2.body = prefRuleBody2;
				std::copy(prefRuleLocVars2.begin(), prefRuleLocVars2.end(), std::back_inserter(prefixRule2.locVars));

				// break out of the loop if for any alignment, we have iterators initially equal;
				// consequently, all remaining iterations are added to query;
				// support checking other combinations
				break;
			}

		}

		HornRuleExt *query1 = ruleManager1.getQuery(), *query2 = ruleManager2.getQuery();

		if (ruleManager1.srcFactVars.empty()) ruleManager1.srcFactVars = prefixRule1.dstVars;
		if (ruleManager2.srcFactVars.empty()) ruleManager2.srcFactVars = prefixRule2.dstVars;

    ExprVector &postSrc1 = ruleManager1.postLoopSrcVars;
    ExprVector &postDst1 = ruleManager1.postLoopDstVars;
    ExprVector &postSrc2 = ruleManager2.postLoopSrcVars;
    ExprVector &postDst2 = ruleManager2.postLoopDstVars;
    Expr postBody1 = ruleManager1.postLoopBody;
    Expr postBody2 = ruleManager2.postLoopBody;

    if (!impliesEq || postDst1.empty()) return impliesEq;

    Expr post = mk<EQ>(postDst1[ruleManager1.iter], postDst2[ruleManager2.iter]);
    ExprVector postSrc;
    concatenateVectors(postSrc, postSrc1, postSrc2);
    phi = myAbduce(post, mk<AND>(postBody1, postBody2), postSrc);
    phi = replaceAll(phi, postSrc1, query1->srcVars);
    phi = replaceAll(phi, postSrc2, query2->srcVars);

    return impliesEq;
	}


	bool checkEquivalence(bool innerLoop)
	{
		// create the product CHC system
		Product_CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_", debug-2);

	    // product of two CHC systems
		ruleManagerProduct.createProduct();

    assert(ruleManagerProduct.chcs.size() == 3);

    HornRuleExt *q1 = ruleManager1.getQuery(), *q2 = ruleManager2.getQuery();
    HornRuleExt *f1 = ruleManager1.getFact(), *f2 = ruleManager2.getFact();

    // create pre and post conditions
		Expr pre = mk<TRUE>(m_efac);
		Expr post;
		if (ruleManager1.iter >= 0)
			post = mk<EQ>(q1->srcVars[ruleManager1.iter], q2->srcVars[ruleManager2.iter]);
		else
			post = mk<TRUE>(m_efac);
		if (pairings[0][0] != -1)
		{
			for (auto &pair : pairings)
			{
				if (ruleManager1.srcFactVars.empty() || ruleManager2.srcFactVars.empty())
					pre = mk<AND>(pre, mk<EQ>(f1->dstVars[pair[0]], f2->dstVars[pair[1]]));
				else
					pre = mk<AND>(pre, mk<EQ>(ruleManager1.srcFactVars[pair[0]], ruleManager2.srcFactVars[pair[1]]));
				post = mk<AND>(post, mk<EQ>(q1->srcVars[pair[0]], q2->srcVars[pair[1]]));
			}
		}

		Expr negPost = mkNeg(post);

		HornRuleExt *fact, *query, *ind;
		for (auto &it : ruleManagerProduct.chcs)
		{
			if (it.isFact) fact = &it;
			if (it.isQuery) query = &it;
			if (it.isInductive) ind = &it;
		}
		fact->body = mk<AND>(fact->body, pre);

		if (phi)
    {
      ExprVector q, qprime;
      ExprSet lin;
      concatenateVectors(q, q1->srcVars, q2->srcVars);
      query->srcVars.clear();
      query->assignVarsAndRewrite(q, ruleManagerProduct.invVars[query->srcRelation],
        qprime, ruleManagerProduct.invVarsPrime[query->dstRelation], lin);
      query->body = simplifyBool(mk<AND>(simplifyBool(mkNeg(phi)), conjoin(lin, m_efac)));
    }
    else
      query->body = simplifyBool(mk<AND>(query->body, negPost));

    ExprSet currentMatching;
		int sz = ind->srcVars.size()/2;

		for (int i = 0; i < sz; i++)
			if (bind::typeOf(ind->srcVars[i]) == bind::typeOf(ind->srcVars[sz + i]))
				currentMatching.insert(mk<EQ>(ind->srcVars[i], (ind->srcVars[sz + i])));

		if (!innerLoop)
		{
			Expr srcEq = conjoin(currentMatching, m_efac);
			Expr dstEq = replaceAll(srcEq, ind->srcVars, ind->dstVars);
		  ind->body = mk<AND>(ind->body, mk<IMPL>(srcEq, dstEq));
		}

    // GF: local vars seem incomplete here. To fix
    for (auto &chc : ruleManagerProduct.chcs)
    	chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);

    // ruleManagerProduct.print(true);

		outs () << "   check fact sanity:  "  << bool(u.isSat(fact->body)) << "\n";
		outs () << "   check query sanity:  "  << bool(u.isSat(query->body)) << "\n";
		outs () << "   check ind sanity:  "  << bool(u.isSat(ind->body)) << "\n";

		outs() << "------------------------PRODUCT CREATED-----------------------------\n\n";

		// call the function with all default values for arguments that are not relevant
		// probably, do a cleaner way of calling the function
	    return learnInvariantsPr(ruleManagerProduct, currentMatching, maxAttempts, to, freqs,
	    	aggp, dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat,
	    	dStrenMbp, dFwd, dRec, dGenerous, dSee);
		}

	};

	void createNonIterCombs(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2,
		vector<vector<vector<int>>> &nonIterCombs)
	{
		vector<vector<vector<int>>> combsArray, combsInt, combsBool, combs1;
		combinationsOfVars(ruleManager1.varsArray, ruleManager2.varsArray, combsArray);
		combinationsOfVars(ruleManager1.varsInt, ruleManager2.varsInt, combsInt);
		combinationsOfVars(ruleManager1.varsBool, ruleManager2.varsBool, combsBool);

		joinVars(combsArray, combsInt, combs1);
		joinVars(combs1, combsBool, nonIterCombs);

		// fix later
		vector<vector<int>> v{{-1, -1}};
		if (nonIterCombs.empty()) nonIterCombs.push_back(v);
	}


  bool checkEquivalenceSingleLoop(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, bool doAlign,
			unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
      bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
      bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug, bool innerLoop)
  {

		ruleManager1.preprocessing();
		ruleManager2.preprocessing();


		BndExpl bndSrc(ruleManager1, debug);
		BndExpl bndDst(ruleManager2, debug);

		// if no iterator was found, the tool exits stating non-equivalence. Support more
    bool iterFound = ruleManager1.findIterators(bndSrc);
    if (innerLoop && !iterFound)
    {
      outs() << "no iterator was found for program 1. programs are not equivalent\n";
      return false;
    }

    iterFound = ruleManager2.findIterators(bndDst);
    if (innerLoop && !iterFound)
    {
      outs() << "no iterator was found for program 2. programs are not equivalent\n";
      return false;
    }

		vector<vector<vector<int>>> nonIterCombs;
		createNonIterCombs(ruleManager1, ruleManager2, nonIterCombs);

		// check for all combinations of variables, such that we match same type of variables
		for (auto &pairings : nonIterCombs)
		{
      Equivalence eq(ruleManager1, ruleManager2, ruleManager1.m_efac, ruleManager1.m_z3, pairings, maxAttempts, to, freqs,
					aggp, dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat,
					dStrenMbp, dFwd, dRec, dGenerous, dSee, debug);

      if (innerLoop && !eq.initialSanityChecks()) return false;
      if (innerLoop && doAlign && !eq.alignPrograms()) return false;
			if (eq.checkEquivalence(innerLoop))
			{
				outs() << "\ncurrent loop is equivalent\n";
				return true;
			}
		}
		outs() << "\ncurrent loop is not equivalent\n";
		return false;
  }


  void constructNewRuleManager(Extended_CHCs &newRM, Extended_CHCs &oldRM, Expr loop, bool addTransition)
	{
    newRM.chcs.clear();

    Expr newName1 = mkTerm<string>("newInv1", oldRM.m_efac);
  	Expr newName2 = mkTerm<string>("newInv2", oldRM.m_efac);
  	ExprVector types;
  	for (auto &v : oldRM.invVars[loop])
  		types.push_back(v->last()->last());
  	types.push_back(mk<BOOL_TY>(oldRM.m_efac));
  	Expr f1 = fdecl(newName1, types);
  	Expr f2 = fdecl(newName2, types);
  	Expr fAppl1 = fapp(f1, oldRM.invVars[loop]);
  	Expr fAppl2 = fapp(f2, oldRM.invVarsPrime[loop]);

  	newRM.addDecl(f1);
  	newRM.addDecl(f2);

  	for (auto it = oldRM.wtoCHCs.begin(); it != oldRM.wtoCHCs.end(); )
    {
      auto chc = *(*it);
      if (loop == chc.srcRelation || loop == chc.dstRelation)
      {
        if (chc.srcRelation != loop)
        {
          chc.srcRelation = newName1;
          chc.srcVars = oldRM.invVars[loop];
          chc.isFact = false;

		    	newRM.chcs.push_back(HornRuleExt());
          HornRuleExt &hr = newRM.chcs.back();
		      hr.dstVars = newRM.invVarsPrime[newName1];
		      hr.srcRelation = mk<TRUE>(oldRM.m_efac);
		      hr.dstRelation = newName1;
		      hr.isFact = true;
		      hr.isQuery = false;
		      hr.isInductive = false;
		      hr.body = mk<TRUE>(oldRM.m_efac);
        }

        if (chc.dstRelation != loop)
        {
          chc.dstRelation = newName2;
          chc.dstVars = oldRM.invVarsPrime[loop];
          chc.isQuery = false;

		    	newRM.chcs.push_back(HornRuleExt());
          HornRuleExt &hr = newRM.chcs.back();
		      hr.srcVars = newRM.invVars[newName2];
		      hr.srcRelation = newName2;
		      hr.dstRelation = newRM.failDecl;
		      hr.isFact = false;
		      hr.isQuery = true;
		      hr.isInductive = false;
		      hr.body = mk<TRUE>(oldRM.m_efac);
        }

        newRM.chcs.push_back(chc);
        oldRM.wtoCHCs.erase(it);
  	  }
      else it++;
    }

    if (addTransition)
    {
    	newRM.chcs.push_back(HornRuleExt());
      HornRuleExt &hr = newRM.chcs.back();
      hr.srcVars = newRM.invVars[loop];
      hr.dstVars = newRM.invVarsPrime[loop];
      hr.srcRelation = loop;
      hr.dstRelation = loop;
      hr.isFact = false;
      hr.isQuery = false;
      hr.isInductive = true;
      hr.body = mk<TRUE>(oldRM.m_efac);
    }

    newRM.cycles.clear();
    newRM.prefixes.clear();
    newRM.outgs.clear();

    for (int i = 0; i < newRM.chcs.size(); i++)
      newRM.outgs[newRM.chcs[i].srcRelation].push_back(i);

    newRM.hasCycles();
	}


  bool checkEquivalence(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, bool doAlign,
			unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
      bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
      bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
	{
    assert(ruleManager1.cycles.size() == ruleManager2.cycles.size());

    for (int i = 0; i < ruleManager1.cycles.size(); i++)
    {
      Expr loop1 = ruleManager1.chcs[ruleManager1.cycles[i][0]].srcRelation;
      Expr loop2 = ruleManager2.chcs[ruleManager2.cycles[i][0]].srcRelation;
    	outs() << "currently processing: " << loop1 << " and " << loop2 << "\n";

      Extended_CHCs newRuleManager1 = ruleManager1, newRuleManager2 = ruleManager2;
      if (ruleManager1.cycles.size() > 1)
      {
	    	constructNewRuleManager(newRuleManager1, ruleManager1, loop1, i>0);
	    	constructNewRuleManager(newRuleManager2, ruleManager2, loop2, i>0);
      }

		  if (!checkEquivalenceSingleLoop(newRuleManager1, newRuleManager2, doAlign, maxAttempts, to, freqs, aggp,
		  	dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec,
		  	dGenerous, dSee, debug, i <= 0))
			  return false;
	  }
    return true;
  }




	// check equivalence of programs
	inline void checkEquivalenceOfPrograms(const char *chcfileSrc, const char *chcfileDst, bool doAlign,
			unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
			bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp, bool dAddDat,
			bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
	{
		ExprFactory m_efac;
		EZ3 z3(m_efac);

		Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-2);
		Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_", debug-2);

		if (!ruleManagerSrc.parse(string(chcfileSrc), doElim, doArithm)) return;
		if (!ruleManagerDst.parse(string(chcfileDst), doElim, doArithm)) return;

		if (checkEquivalence(ruleManagerSrc, ruleManagerDst, doAlign, maxAttempts, to, freqs, aggp, dat, mut, doElim,
			doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, debug))
      outs() << "\nprograms are equivalent\n";
    else
      outs() << "\nprograms are not equivalent\n";
  };
}

#endif
