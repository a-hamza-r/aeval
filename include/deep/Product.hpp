#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"
#include "RndLearnerV2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

    void productOfCHCs(HornRuleExt, HornRuleExt, vector<HornRuleExt> &, CHCs &);

    void productRelationSymbols(ExprVector, Expr &, vector<HornRuleExt> &, CHCs &, bool);

    void equivalenceTask(vector<HornRuleExt> &chcs1, vector<HornRuleExt> &chcs2, ExprFactory &m_efac)
    {
        // getInductiveRules(chcs1, chcs2);

        // learnInvariants2(ruleManagerDst, NULL, 2000000, 0, 3, 3, false, false);
        ExprVector candidates;
        
        ExprVector srcArrayVars1, dstArrayVars1, srcArrayVars2, dstArrayVars2;
        ExprVector srcBvVars1, dstBvVars1, srcBvVars2, dstBvVars2;
        ExprVector srcBoolVars1, dstBoolVars1, srcBoolVars2, dstBoolVars2;
        for (int i = 0; i < chcs1.size(); i++) {
            if (chcs1[i].isInductive && chcs2[i].isInductive)
            {
                chcs1[i].getTypeVars<ARRAY_TY>(srcArrayVars1, dstArrayVars1);
                chcs1[i].getTypeVars<BVSORT>(srcBvVars1, dstBvVars1);
                chcs1[i].getTypeVars<BOOL_TY>(srcBoolVars1, dstBoolVars1);

                chcs2[i].getTypeVars<ARRAY_TY>(srcArrayVars2, dstArrayVars2);
                chcs2[i].getTypeVars<BVSORT>(srcBvVars2, dstBvVars2);
                chcs2[i].getTypeVars<BOOL_TY>(srcBoolVars2, dstBoolVars2);

                for (auto it = srcBvVars1.begin(); it != srcBvVars1.end(); it++) {
                    errs() << **it << ", its type: " << *bind::typeOf(*it) << "\n";
                    errs() << bv::width(bind::typeOf(*it)) << "\n";
                    // errs() << bv::width(*it) << "\n";
                }


                // int numBvToCmp = srcBvVars.size() - srcArrayVars.size();
                Expr pre = mk<TRUE>(m_efac);
                for (auto it = srcBvVars1.begin(); it != srcBvVars1.end(); it++)
                {
                    for (auto it2 = srcBvVars2.begin(); it2 != srcBvVars2.end(); it2++)
                    {
                        pre = mk<AND>(pre, mk<EQ>(*it, *it2));
                    }
                }

                Expr post = mk<TRUE>(m_efac);
                for (auto it = dstBvVars1.begin(); it != dstBvVars1.end(); it++)
                {
                    for (auto it2 = dstBvVars2.begin(); it2 != dstBvVars2.end(); it2++)
                    {
                        post = mk<AND>(post, mk<EQ>(*it, *it2));
                    }
                }
                post = mk<NEG>(post);

                errs() << "post: " << *post << "\n";

                for (auto it = srcArrayVars1.begin(); it != srcArrayVars1.end(); it++)
                {
                    for (auto it2 = srcArrayVars2.begin(); it2 != srcArrayVars2.end(); it2++)
                    {
                        // pre = mk<AND>(post, )
                    }
                }
            }
        }
    }


    void nonRecursiveProduct(HornRuleExt chc1, HornRuleExt chc2, Expr &product, CHCs &rules)
    {
        bool chc1NonRec = !chc1.isFact && !chc1.isInductive;
        bool chc2NonRec = !chc2.isFact && !chc2.isInductive;

        // todo: have to check whether the chc is non-linear
        if (chc1NonRec && chc2NonRec)
        {
            product = mk<AND>(chc1.srcRelation, chc2.srcRelation);
        }
        else if (chc1NonRec)
        {
            product = chc1.srcRelation;
        }
        else if (chc2NonRec)
        {
            product = chc2.srcRelation;
        }
    }


    void RTransform(HornRuleExt chc, Expr &transformed, CHCs &rules)
    {
        if (!chc.isInductive)
        {
            transformed = chc.head;

            // chc.srcRelation = mk<AND>(chc.srcRelation, chc.dstRelation);

            // // srcVars also have primed variables now
            // chc.srcVars.insert(chc.srcVars.end(), chc.dstVars.begin(), chc.dstVars.end()); 
        
            // // do I now change it to !fact && inductive? 
            // chc.isFact = false;
            // chc.isInductive = true;
            // chc.printMemberVars();
        }
        else
        {
            rules.getDecl(chc.srcRelation, transformed);
        }
    }


    void recursiveProduct(HornRuleExt chc1, HornRuleExt chc2, Expr &product, CHCs &rules)
    {
        Expr transform1, transform2;
        vector<HornRuleExt> nullV;

        // I am not changing the original system by transforming 
        RTransform(chc1, transform1, rules); RTransform(chc2, transform2, rules);

        productRelationSymbols(ExprVector{transform1, transform2}, product, nullV, rules, false);

        if (product) product = product->arg(0);
    }


    void productBody(HornRuleExt chc1, HornRuleExt chc2, CHCs &rules, HornRuleExt &newProductRule)
    {
        Expr constraintPr, recursivePr, nonRecursivePr;

        // constraint product
        constraintPr = mk<AND>(chc1.body, chc2.body);

        // non-recursive part product
        nonRecursiveProduct(chc1, chc2, nonRecursivePr, rules);

        // recursive part product
        recursiveProduct(chc1, chc2, recursivePr, rules);

        // remove head C from body
        // if (recursivePr == newProductRule.head->arg(0)) recursivePr = NULL;

        newProductRule.body = constraintPr;

        if (nonRecursivePr && recursivePr) {
            newProductRule.srcRelation = mk<AND>(nonRecursivePr, recursivePr);
            newProductRule.isFact = false;
            newProductRule.isQuery = false;
            // errs() << "nonRecursivePr: " << *nonRecursivePr << "\n";
            // errs() << "recursivePr: " << *recursivePr << "\n";
            // errs() << "head: " << *newProductRule.head << "\n";
        }
        else if (nonRecursivePr) {
            newProductRule.srcRelation = nonRecursivePr;
            // errs() << "nonRecursivePr: " << *nonRecursivePr << "\n";
            // errs() << "head: " << *newProductRule.head << "\n";
        }
        else if (recursivePr) {
            newProductRule.srcRelation = recursivePr;
            // errs() << "recursivePr: " << *recursivePr << "\n";
            // errs() << "head: " << *newProductRule.head << "\n";
        }
    }


    void rulesOfPredicate(vector<HornRuleExt> &allRules, Expr &predicateDecl, vector<HornRuleExt> &rulesOfP)
    {
        for (auto it = allRules.begin(); it != allRules.end(); it++)
        {
            if (predicateDecl == it->head)
            {
                rulesOfP.push_back(*it);
            }
        }
    }


    void getNonRecPartsPartitioned(HornRuleExt chc, ExprVector &partitions, CHCs rules)
    {
        // chc.printMemberVars();
        Expr decl;
        if (isOpX<AND>(chc.srcRelation))
        {
            for (auto it = chc.srcRelation->args_begin(); it != chc.srcRelation->args_end(); it++)
            {
                rules.getDecl(*it, decl);
                partitions.push_back(decl);
            }
        }
    }


    void getQueryRules(vector<HornRuleExt> chcs, vector<HornRuleExt> &queries)
    {
        for (auto it = chcs.begin(); it != chcs.end(); it++)
        {
            if (it->isQuery) queries.push_back(*it);
        }
    }


    void createProductQuery(vector<HornRuleExt> queries, HornRuleExt &queryPr)
    {
        HornRuleExt query1 = *queries.begin();
        HornRuleExt query2 = *(queries.begin()+1);
        queryPr.body = mk<AND>(query1.body, query2.body);

        queryPr.srcRelation = mk<AND>(query1.srcRelation, query2.srcRelation);
        queryPr.dstRelation = mkTerm<string>(lexical_cast<string>(query1.dstRelation) + 
            "*" + lexical_cast<string>(query2.dstRelation), queryPr.body->getFactory());
        
        queryPr.head = bind::fdecl(queryPr.dstRelation, ExprVector{mk<BOOL_TY>(queryPr.body->getFactory())});

        concatenateVectors(queryPr.srcVars, query1.srcVars, query2.srcVars);
        concatenateVectors(queryPr.dstVars, query1.dstVars, query2.dstVars);
        concatenateVectors(queryPr.locVars, query1.locVars, query2.locVars);

        queryPr.isFact = false;
        queryPr.isQuery = true;
        queryPr.isInductive = false;
    }


    void calculateCombinations(vector<vector<HornRuleExt>> rules, vector<vector<HornRuleExt>> &combinations)
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


    void productRelationSymbols(ExprVector predicates, Expr &predicateP, vector<HornRuleExt> &rulesP, 
        CHCs &rules, bool calculateRulesOfP)
    {
        Expr rel, relDecl, productRel = mkTerm<string>("", rules.m_efac);
        ExprVector productTypes;
        vector<vector<HornRuleExt>> rulesOfPredicates, combinations;

        for (auto it = predicates.begin(); it != predicates.end(); it++)
        {
            rel = *it;
            if (!isFdecl(rel)) {
                rules.getDecl(rel, relDecl);
                if (!isFdecl(relDecl))
                {
                    predicateP = NULL;
                    rulesP = vector<HornRuleExt>();
                    return;
                }
                rel = relDecl;
            }

            productRel = mkTerm<string>(lexical_cast<string>(productRel)+lexical_cast<string>(rel->arg(0)) + 
                "*", rules.m_efac);
            for (int i = 1; i < rel->arity()-1; i++) 
                productTypes.push_back(rel->arg(i));

            if (calculateRulesOfP) 
            {
                vector<HornRuleExt> rulesOfCurrentP;
                rulesOfPredicate(rules.chcs, rel, rulesOfCurrentP);

                rulesOfPredicates.push_back(rulesOfCurrentP);
            }
        }
        productTypes.push_back(mk<BOOL_TY>(rules.m_efac));

        predicateP = bind::fdecl(productRel, productTypes);
        // todo: also insert predicateP in appropriate DS in the product CHCs

        if (calculateRulesOfP) 
        {
            calculateCombinations(rulesOfPredicates, combinations);

            for (auto &it : combinations)
            {
                productOfCHCs(it[0], it[1], rulesP, rules);
            }
        }
    }


    void productOfCHCs(HornRuleExt chc1, HornRuleExt chc2, vector<HornRuleExt> &rulesP, CHCs &rules)
    {
        Expr head, body;
        vector<HornRuleExt> nullV;
        HornRuleExt newProductRule;

        // head product
        productRelationSymbols(ExprVector{chc1.head, chc2.head}, head, nullV, rules, false);
        
        newProductRule.head = head;
        newProductRule.dstRelation = head->arg(0);

        // body product
        productBody(chc1, chc2, rules, newProductRule);

    }


    void removeCHC(HornRuleExt chc, CHCs &rules)
    {
        for (auto it = rules.chcs.begin(); it != rules.chcs.end(); it++)
        {
            // errs() << "checking " << *chc.srcRelation << " against " << *it->srcRelation << "\n";
            if (it->srcRelation == chc.srcRelation && it->dstRelation == chc.dstRelation)
            {
                rules.chcs.erase(it);
            }
        }

        // might have to remove the chc function relations from invVars and decls
    }


    void transformCHC(HornRuleExt chc, vector<HornRuleExt> rulesP, CHCs &rules)
    {
        removeCHC(chc, rules);
        rules.chcs.insert(rules.chcs.end(), rulesP.begin(), rulesP.end());

        HornRuleExt C_aPrime;
        Expr predicate;
        C_aPrime.body = chc.body;
        C_aPrime.head = chc.head;
        C_aPrime.dstRelation = chc.dstRelation;

        ExprVector predicates;
        vector<HornRuleExt> nullV;

        if (isOpX<AND>(chc.srcRelation))
        {
            predicates.push_back(chc.srcRelation->arg(0));
            predicates.push_back(chc.srcRelation->arg(1));
        }
        else 
        {
            predicates.push_back(chc.srcRelation);
        }

        productRelationSymbols(predicates, predicate, nullV, rules, false);

        if (predicate) C_aPrime.srcRelation = predicate->arg(0);
        // errs() << *C_aPrime.srcRelation << "\n";

        // todo: fill remaining member variables of C_aPrime (HornRuleExt), 
            // also appropriate members in rules (CHCs)
    }


    // generates the product of two CHC systems
    // At many places, it is assumed that there are only two systems, 
    // hence the operations done are not generic i.e. for product of more than two CHC systems
    void Product(CHCs &product)
    {
        vector<HornRuleExt> queries, rulesP;
        Expr freshP;
        getQueryRules(product.chcs, queries);

        if (queries.empty())
        {
            outs() << "Product can not be found.\n";
            exit(0);
        }

        HornRuleExt queryPr;

        createProductQuery(queries, queryPr);

        vector<HornRuleExt> transformedCHCs;
        vector<HornRuleExt> worklist;
        ExprVector partitions;
        HornRuleExt C_a;

        worklist.push_back(queryPr);

        while (!worklist.empty())
        {
            C_a = worklist[0];
            worklist.erase(worklist.begin());

            // AH: In the original algorithm, the operation PARTITION is used that is defined: 
            // 'operator partition from a set to a set of its disjoint subsets'
            // I do not make any partitions because there are only two relation symbols here
            getNonRecPartsPartitioned(C_a, partitions, product);

            productRelationSymbols(partitions, freshP, rulesP, product, true);

            // errs() << "freshP: " << *freshP << "\n";
            // for (auto it : rulesP)
            // {
            //     product.print(it);
            // }

            errs() << "transform: \n";
            product.print(C_a);
            transformCHC(C_a, rulesP, product);
        }

    }


	inline void createProduct(const char *chcfileSrc, const char *chcfileDst)
  	{
    	ExprFactory m_efac;
	    EZ3 z3(m_efac);

	    CHCs ruleManagerSrc(m_efac, z3, "_v1_");
	    ruleManagerSrc.parse(string(chcfileSrc));

	    CHCs ruleManagerDst(m_efac, z3, "_v2_");
	    ruleManagerDst.parse(string(chcfileDst));

	    for (auto it = ruleManagerSrc.chcs.begin(); it != ruleManagerSrc.chcs.end(); it++) {
	    	it->printMemberVars();
	    }

		// for (auto it = ruleManagerDst.chcs.begin(); it != ruleManagerDst.chcs.end(); it++) {
	 //    	it->printMemberVars();
	 //    }

	    // auto chcs1 = ruleManagerSrc.chcs;
	    // auto chcs2 = ruleManagerDst.chcs;

	    // equivalenceTask(chcs1, chcs2, m_efac);

        CHCs ruleManagerProduct(ruleManagerSrc, ruleManagerDst, "_pr_");

	    Product(ruleManagerProduct);
  };
}

#endif
