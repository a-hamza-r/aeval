#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"
#include "RndLearnerV2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

    void productOfCHCs(HornRuleExt &, HornRuleExt &, vector<HornRuleExt> &, CHCs &);

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


    void nonRecursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars, CHCs &rules)
    {
        ExprVector chc1NonRecPart, chc2NonRecPart;
        if (isOpX<AND>(chc1.srcRelation))
        {
            for (auto it = chc1.srcRelation->args_begin(); it != chc1.srcRelation->args_end(); it++)
            {
                // errs() << "checking: " << **it << "\n";
                if (*it != chc1.dstRelation)
                {
                    chc1NonRecPart.push_back(*it);
                }
            }
        }
        else 
        {
            if (chc1.srcRelation != chc1.dstRelation && !chc1.isFact)
            {
                chc1NonRecPart.push_back(chc1.srcRelation);
            }
        }

        if (isOpX<AND>(chc2.srcRelation))
        {
            for (auto it = chc2.srcRelation->args_begin(); it != chc2.srcRelation->args_end(); it++)
            {
                // errs() << "checking: " << **it << "\n";
                if (*it != chc2.dstRelation)
                {
                    chc2NonRecPart.push_back(*it);
                }
            }
        }
        else 
        {
            if (chc2.srcRelation != chc2.dstRelation && !chc2.isFact)
            {
                chc2NonRecPart.push_back(chc2.srcRelation);
            }
        }

        // for (auto it : chc1NonRecPart) errs() << *it << "\n";
        // for (auto it : chc2NonRecPart) errs() << *it << "\n";

        bool chc1NonRec = !chc1NonRecPart.empty();
        bool chc2NonRec = !chc2NonRecPart.empty();

        // todo: have to check whether the chc is non-linear
        if (chc1NonRec && chc2NonRec)
        {
            product = chc1NonRecPart[0];
            rules.getInvVars(chc1NonRecPart[0], vars);
            for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
            {
                product = mk<AND>(product, *it);
                rules.getInvVars(*it, vars);
            }
            for (auto it = chc2NonRecPart.begin(); it != chc2NonRecPart.end(); it++)
            {
                product = mk<AND>(product, *it);
                rules.getInvVars(*it, vars);
            }
        }
        else if (chc1NonRec)
        {
            product = chc1NonRecPart[0];
            rules.getInvVars(chc1NonRecPart[0], vars);
            for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
            {
                product = mk<AND>(product, *it);
                rules.getInvVars(*it, vars);
            }
        }
        else if (chc2NonRec)
        {
            product = chc2NonRecPart[0];
            rules.getInvVars(chc2NonRecPart[0], vars);
            for (auto it = chc2NonRecPart.begin()+1; it != chc2NonRecPart.end(); it++)
            {
                product = mk<AND>(product, *it);
                rules.getInvVars(*it, vars);
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
            if (isOpX<AND>(chc.srcRelation))
            {
                for (auto it = chc.srcRelation->args_begin(); it != chc.srcRelation->args_end(); it++)
                {
                    if (*it == chc.dstRelation)
                    {
                        rules.getDecl(*it, decl);
                        transformed.push_back(bind::fapp(decl, chc.srcVars));
                    }
                }
            }
            else 
            {
                rules.getDecl(chc.srcRelation, decl);
                transformed.push_back(bind::fapp(decl, chc.srcVars));
            }
        }
    }


    void recursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars,
        CHCs &rules)
    {
        vector<HornRuleExt> nullV;
        ExprVector transformed;

        RTransform(chc1, transformed, rules); RTransform(chc2, transformed, rules);

        productRelationSymbols(ExprVector{transformed[0]->arg(0), transformed[1]->arg(0)}, 
            product, nullV, rules, false);

        // remove head C from body
        if (bind::fapp(chc1.head, chc1.dstVars) == transformed[0] 
            && bind::fapp(chc2.head, chc2.dstVars) == transformed[1]) 
        {
            product = NULL;
        }
        else 
        {
            vars.insert(vars.end(), transformed[0]->args_begin()+1, transformed[0]->args_end());
            vars.insert(vars.end(), transformed[1]->args_begin()+1, transformed[1]->args_end());

            rules.addDecl2(product, vars);

            product = product->arg(0);
        }
    }


    void productBody(HornRuleExt &chc1, HornRuleExt &chc2, CHCs &rules, HornRuleExt &newProductRule)
    {
        Expr constraintPr, recursivePr, nonRecursivePr;
        ExprVector nonRecursivePrVars, recursivePrVars;

        // constraint product
        constraintPr = mk<AND>(chc1.body, chc2.body);

        // errs() << "constraintPr: " << *constraintPr << "\n";

        // non-recursive part product
        nonRecursiveProduct(chc1, chc2, nonRecursivePr, nonRecursivePrVars, rules);
        // errs() << "nonRecursivePr: " << *nonRecursivePr << "\n";

        // recursive part product
        recursiveProduct(chc1, chc2, recursivePr, recursivePrVars, rules);

        newProductRule.body = constraintPr;

        concatenateVectors(newProductRule.locVars, chc1.locVars, chc2.locVars);

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
        newProductRule.isFact = (nonRecursivePr == NULL && recursivePr == NULL);
        newProductRule.isQuery = (newProductRule.dstRelation == rules.failDecl);
        newProductRule.isInductive = (recursivePr != NULL);
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


    void getNonRecParts(Expr rel, Expr dstRelation, ExprVector &partitions, CHCs &rules)
    {
        // chc.printMemberVars();
        Expr decl;
        if (isOpX<AND>(rel))
        {
            for (auto it = rel->args_begin(); it != rel->args_end(); it++)
            {
                getNonRecParts(*it, dstRelation, partitions, rules);
            }
        }
        else 
        {
            if (rel != dstRelation)
            {
                rules.getDecl(rel, decl);
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


    void createProductQuery(vector<HornRuleExt> queries, HornRuleExt &queryPr, CHCs &rules)
    {
        HornRuleExt query1 = queries[0];
        HornRuleExt query2 = queries[1];
        queryPr.body = mk<AND>(query1.body, query2.body);

        queryPr.srcRelation = mk<AND>(query1.srcRelation, query2.srcRelation);
        queryPr.dstRelation = mkTerm<string>(lexical_cast<string>(query1.dstRelation) + 
            "*" + lexical_cast<string>(query2.dstRelation), queryPr.body->getFactory());
        
        queryPr.head = bind::fdecl(queryPr.dstRelation, ExprVector{mk<BOOL_TY>(queryPr.body->getFactory())});

        rules.addFailDecl(queryPr.dstRelation);

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


    void productRelationSymbols(ExprVector predicates, Expr &predicateP, vector<HornRuleExt> &rulesOfP, 
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
                    rulesOfP.clear();
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
                // errs() << "rules of current p: " << *rel << "\n";
                vector<HornRuleExt> rulesOfCurrentP;
                rulesOfPredicate(rules.chcs, rel, rulesOfCurrentP);

                // for (auto it2 : rulesOfCurrentP)
                //     rules.print(it2);

                rulesOfPredicates.push_back(rulesOfCurrentP);
            }
        }
        productTypes.push_back(mk<BOOL_TY>(rules.m_efac));

        predicateP = bind::fdecl(productRel, productTypes);

        if (calculateRulesOfP) 
        {
            calculateCombinations(rulesOfPredicates, combinations);

            for (auto &it : combinations)
            {
                // errs() << "product of these: \n";
                // rules.print(it[0]);
                // rules.print(it[1]);
                productOfCHCs(it[0], it[1], rulesOfP, rules);
            }
        }
    }


    void productOfCHCs(HornRuleExt &chc1, HornRuleExt &chc2, vector<HornRuleExt> &rulesOfP, CHCs &rules)
    {
        // errs() << "New product\n";
        Expr head, body;
        vector<HornRuleExt> nullV;
        HornRuleExt newProductRule;
        ExprVector vars;

        // head product
        productRelationSymbols(ExprVector{chc1.head, chc2.head}, head, nullV, rules, false);
        
        newProductRule.head = head;
        newProductRule.dstRelation = head->arg(0);

        // errs() << "head: " << *newProductRule.head << "\n";
        concatenateVectors(newProductRule.dstVars, chc1.dstVars, chc2.dstVars);

        // so that we do not add new declarations with primed variables
        rules.getInvVars(chc1.dstRelation, vars);
        rules.getInvVars(chc2.dstRelation, vars);

        rules.addDecl2(newProductRule.head, vars);

        // for (auto it : rules.decls)
        //     errs() << *it << "\n";

        // body product
        productBody(chc1, chc2, rules, newProductRule);
        
        // errs() << "two systems: \n";
        // rules.print(chc1);
        // rules.print(chc2);
        // errs() << "product is: \n";
        // rules.print(newProductRule);

        rulesOfP.push_back(newProductRule);
    }


    void removeCHC(Expr srcRelation, Expr dstRelation, CHCs &rules)
    {
        // if (isOpX<AND>(srcRelation))
        // {
        //     for (auto it = srcRelation->args_begin(); it != srcRelation->args_end(); it++)
        //     {
        //         removeCHC(*it, dstRelation, rules);
        //     }
        //     return;
        // }

        for (auto it = rules.chcs.begin(); it != rules.chcs.end(); it++)
        {
            // errs() << "checking " << *srcRelation << " against " << *it->srcRelation << "\n";
            // errs() << "checking " << *dstRelation << " against " << *it->dstRelation << "\n";
            if (it->srcRelation == srcRelation && it->dstRelation == dstRelation)
            {
                // errs() << "erasing " << *srcRelation << " " << *dstRelation << "\n";
                rules.chcs.erase(it);
            }
        }

        // might have to remove the chc function relations from invVars and decls
    }


    void updateSystem(HornRuleExt chc, vector<HornRuleExt> rulesOfP, CHCs &rules)
    {
        removeCHC(chc.srcRelation, chc.dstRelation, rules);
        
        rules.chcs.insert(rules.chcs.end(), rulesOfP.begin(), rulesOfP.end());

        Expr predicate;
        ExprVector vars;

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

        if (predicate) chc.srcRelation = predicate->arg(0);
        rules.getInvVars(predicates[0], vars);
        rules.getInvVars(predicates[1], vars);

        chc.srcVars.clear();
        chc.srcVars = vars;

        rules.chcs.push_back(chc);

        // errs() << "modified chc: \n";
        // rules.print(chc); 

        // todo: fill remaining member variables of newCHC (HornRuleExt), 
            // also appropriate members in rules (CHCs)
    }


    // generates the product of two CHC systems
    // At many places, it is assumed that there are only two systems, 
    // hence the operations done are not generic i.e. for product of more than two CHC systems
    void Product(CHCs &product)
    {
        vector<HornRuleExt> queries;
        Expr freshP;

        // get queries of both systems
        getQueryRules(product.chcs, queries);

        if (queries.empty())
        {
            outs() << "Product can not be found.\n";
            exit(1);
        }

        HornRuleExt queryPr;

        // generate product query
        createProductQuery(queries, queryPr, product);

        // errs() << "Product query: ";
        // product.print(queryPr);

        vector<HornRuleExt> transformedCHCs;
        vector<HornRuleExt> worklist;
        HornRuleExt C_a;

        worklist.push_back(queryPr);

        while (!worklist.empty())
        {
            ExprVector partitions;
            vector<HornRuleExt> rulesOfP;
            C_a = worklist[0];
            worklist.erase(worklist.begin());

            // errs() << "current worklist item: \n";
            // product.print(C_a);

            // AH: In the original algorithm, the operation PARTITION is used that is defined: 
            // 'operator partition from a set to a set of its disjoint subsets'
            // I just create one partition of two symbols because there are only two relation symbols here 
            getNonRecParts(C_a.srcRelation, C_a.dstRelation, partitions, product);

            if (partitions.size() < 2)
                continue;
            // errs() << "partition: " << *partitions[0] << "\n";
            // errs() << "partition: " << *partitions[1] << "\n";

            productRelationSymbols(partitions, freshP, rulesOfP, product, true);

            // errs() << "freshP: " << *freshP << "\n";

            updateSystem(C_a, rulesOfP, product);

            // errs() << "pushed to rules p: \n";
            for (auto it : rulesOfP)
            {
                worklist.push_back(it);
                // product.print(it);
            }
            rulesOfP.clear();
            // errs() << "printing all the rules\n";
            // for (auto it : product.chcs)
            // {
            //     product.print(it);
            // }
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

	    // for (auto it = ruleManagerSrc.chcs.begin(); it != ruleManagerSrc.chcs.end(); it++) {
	    // 	it->printMemberVars();
	    // }

		// for (auto it = ruleManagerDst.chcs.begin(); it != ruleManagerDst.chcs.end(); it++) {
	 //    	it->printMemberVars();
	 //    }

        CHCs ruleManagerProduct(ruleManagerSrc, ruleManagerDst, "_pr_");

        // product of two CHC systems
	    Product(ruleManagerProduct);

	    // auto chcs1 = ruleManagerSrc.chcs;
	    // auto chcs2 = ruleManagerDst.chcs;

	    // equivalenceTask(chcs1, chcs2, m_efac);
  };
}

#endif
