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

    void equivalenceTask(vector<HornRuleExt> &chcs1, vector<HornRuleExt> &chcs2, ExprFactory &m_efac)
    {
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
            if (!product) product = chc2NonRecPart[0]->arg(0);
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


    void recursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, Expr &product, ExprVector &vars,
        CHCs &rules)
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
            rulesOfPredicate(rules.chcs, rel1, rulesOfCurrentP);

            for (auto &it : rulesOfCurrentP) 
            {
                toRemoveCHCs.push_back(ExprVector{it.srcRelation, it.dstRelation});
                // rules.print(it);
            }

            rulesOfPredicates.push_back(rulesOfCurrentP);

            rulesOfCurrentP.clear();

            // errs() << "Rules of relation: " << *rel2->arg(0) << "\n";
            rulesOfPredicate(rules.chcs, rel2, rulesOfCurrentP);

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
        if (!((!chc1.isInductive && chc2.isInductive) || (!chc2.isInductive && chc1.isInductive)))
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
        bool erased;
        Expr propagated, tmp;

        renamingAsProductRules(rules);

        for (auto chcIter = rules.chcs.begin(); chcIter != rules.chcs.end(); )
        {   
            erased = false;

            ExprSet vars(chcIter->locVars.begin(), chcIter->locVars.end());
            chcIter->body = eliminateQuantifiers(chcIter->body, vars);
            chcIter->locVars.clear();

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

        // check if it's faster to remove duplicates in previous loop or in separate loop
        /*for (auto &it : rules.chcs)
        {
            ExprSet s(it.locVars.begin(), it.locVars.end());
            it.locVars.assign(s.begin(), s.end());
        }*/
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
        {
            for (auto &it2 : it)
            {
                toRemoveCHCs.push_back(ExprVector{it2.srcRelation, it2.dstRelation});
            }
        }

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

            // argument false for non-recursive
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

        for (auto &hr : product.chcs)
            hr.printMemberVars();

        // changes variables from _v1_ and _v2_ prefixes to _pr_ with necessary changes, 
        // also disjoins rules to remove redundancy
        simplifyRules(product);

        for (int i = 0; i < product.chcs.size(); i++)
            product.outgs[product.chcs[i].srcRelation].push_back(i);

        product.wtoSort();

        errs() << "\nFinal system:\n";
        product.print();

        errs() << "Printing all rules and member vars:\n";
        for (auto &hr : product.chcs) {
            hr.printMemberVars();
            
            // creates an encoding of formula and prints to stdout
            /*ExprVector v;
            Expr q = createQuantifiedFormula(hr.body, v);
            SMTUtils su(hr.body->getFactory());
            su.serialize_formula(q);*/
        }
        errs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
    }


	inline void createProduct(const char *chcfileSrc, const char *chcfileDst)
  	{
    	ExprFactory m_efac;
	    EZ3 z3(m_efac);

	    CHCs ruleManagerSrc(m_efac, z3, "_v1_");
	    ruleManagerSrc.parse(string(chcfileSrc));

	    CHCs ruleManagerDst(m_efac, z3, "_v2_");
	    ruleManagerDst.parse(string(chcfileDst));

        CHCs ruleManagerProduct(ruleManagerSrc, ruleManagerDst, "_pr_");

        vector<vector<HornRuleExt>> queries(2);

        // get queries of both systems
        getQueries(ruleManagerSrc.chcs, ruleManagerDst.chcs, queries);

        if (queries.empty())
        {
            outs() << "Product can not be found.\n";
            exit(1);
        }

        // product of two CHC systems
	    Product(ruleManagerProduct, queries);

        learnInvariantsPr(ruleManagerProduct, 2000000, false, false, true, vector<string>());
  };
}

#endif
