#ifndef EQUIVALENCE__HPP__
#define EQUIVALENCE__HPP__

#include "Extended_Horn.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

    class Product_CHCs : public Extended_CHCs
    {
        private:
            Extended_CHCs* subRule1;
            Extended_CHCs* subRule2;

        public:
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
                queryPr.body = simplifyBool(mk<AND>(query1->body, query2->body));

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
                }
            }


            // generates the product of two CHC systems
            // At many places, it is assumed that there are only two systems,
            // hence the operations done are not generic i.e. for product of more than two CHC systems
            void createProduct()
            {
                vector<HornRuleExt> worklist;
                HornRuleExt C_a;
                HornRuleExt queryPr;

                HornRuleExt *query1 = subRule1->getQuery(), *query2 = subRule2->getQuery();
                if (!query1 || !query2)
                {
                    errs() << "Creating product system requires that input CHC system have query CHCs\n";
                    exit(0);
                }

                // generate product queries
                createProductQueries(queryPr);
                worklist.push_back(queryPr);

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
                loopRel = chcs[cycles[0][0]].srcRelation;

                outs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
            }
    };


    class EquivalenceInPaper 
    {
        private:
            ExprFactory &m_efac;
            EZ3 &m_z3;
            Extended_CHCs &source;
            Extended_CHCs &target;
            SMTUtils u;
            int itersOutLoopR1;
            int itersOutLoopR2;
            int itersInLoopR1;
            int itersInLoopR2;


        public:
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
            vector<vector<int>> pairings;
            ExprSet mapping;

        EquivalenceInPaper(Extended_CHCs &r1, Extended_CHCs &r2,
                unsigned _maxAttempts, unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut,
                bool _doElim, bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp, bool _dAddProp, bool _dAddDat,
                bool _dStrenMbp, int _dFwd, bool _dRec, bool _dGenerous, bool _dSee, int _debug, vector<vector<int>> &_pairings) :
            m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to), 
            source(r1), target(r2),
            maxAttempts(_maxAttempts), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
            doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp), mbpEqs(_mbpEqs), dAllMbp(_dAllMbp),
            dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec),
            dGenerous(_dGenerous), dSee(_dSee), debug(_debug), pairings(_pairings)
        {}

        /*
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
        */

        bool findIterators() {
            source.preprocessing();
            target.preprocessing();
            bool bothItersFound = source.findIterators(true) && target.findIterators(true);
            outs() << "source iter: " << source.iter << "\n";
            outs() << "target iter: " << target.iter << "\n";
            return bothItersFound;
        }

        bool getAlignmentVals(ExprSet& pre)
        {
            /*
               int iter1 = source.iter, iter2 = target.iter;
               Expr rel1 = source.loopRel, rel2 = target.loopRel;

               outs() << "\n\nassuming iters: "
               << source.invVars[rel1][iter1] << " and " << target.invVars[rel2][iter2] << "\n";
               */

            Expr numIters1 = source.numOfIters;
            Expr numIters2 = target.numOfIters;
            //outs() << "numIters: " << numIters1 << " and " << numIters2 << "\n";

            if (numIters1 == mkMPZ(-1, m_efac) || numIters2 == mkMPZ(-1, m_efac))
            {
                outs() << "number of iterations were not found\n";
                return false;
            }

            outs() << "numIters source: " << numIters1 << "\n";
            outs() << "numIters target: " << numIters1 << "\n";
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

            //outs() << "Quantified formula: " << quantifiedFla << "\n";

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

        bool alignPrograms()
        {
            const vector<int> &cycle1 = source.cycles[0];
            HornRuleExt &rule1 = source.chcs[cycle1[0]];
            const vector<int> &prefix1 = source.prefixes[0];
            HornRuleExt &prefixRule1 = source.chcs[prefix1[0]];

            const vector<int> &cycle2 = target.cycles[0];
            HornRuleExt &rule2 = target.chcs[cycle2[0]];
            const vector<int> &prefix2 = target.prefixes[0];
            HornRuleExt &prefixRule2 = target.chcs[prefix2[0]];

            BndExpl bnd1(source, debug);
            BndExpl bnd2(target, debug);

            Expr pref1 = bnd1.compactPrefix(0), pref2 = bnd2.compactPrefix(0);
            int iter1 = source.iter, iter2 = target.iter;
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
                        preForEqualityCheck.insert(mk<EQ>(var1Dst, var1Dst));
                        preForQuantifiedFla.insert(mk<EQ>(var1Src, var2Src));
                    }
                }
            }

            if (!getAlignmentVals(preForQuantifiedFla)) return false;

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

            bool impliesEq = false;
            for (auto &possibleAlign : possibleFactQueryAligns)
            {
                ExprSet equalityChecks = preForEqualityCheck;
                Expr prefixBody1 = prefixRule1.body, prefixBody2 = prefixRule2.body;

                // check if adding certain iterations to query will make the initial values of iterators equal
                // it is not greedy approach currently
                source.createAlignment(0, possibleAlign[0], 0, bnd1, prefixBody1, false);
                target.createAlignment(0, possibleAlign[1], 0, bnd2, prefixBody2, false);

                equalityChecks.insert(prefixBody1);
                equalityChecks.insert(prefixBody2);

                Expr eq = mk<EQ>(iterF, iterS);
                impliesEq = bool(u.implies(conjoin(equalityChecks, m_efac), eq));

                if (impliesEq)
                {
                    Expr prefixBody1 = prefixRule1.body, prefixBody2 = prefixRule2.body;
                    // actual alignment created here
                    source.createAlignment(itersInLoopR1, possibleAlign[0], itersOutLoopR1-possibleAlign[0], bnd1, prefixBody1);
                    prefixRule1.body = prefixBody1;

                    target.createAlignment(itersInLoopR2, possibleAlign[1], itersOutLoopR2-possibleAlign[1], bnd2, prefixBody2);
                    prefixRule2.body = prefixBody2;

                    for (auto &chc : source.chcs)
                    {
                        chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);
                        chc.locVars.clear();
                    }

                    for (auto &chc : target.chcs)
                    {
                        chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);
                        chc.locVars.clear();
                    }

                    return true;
                }
            }
            return false;
        }

        void createVariableMapping(Product_CHCs &product) {
            ExprVector combinedVars;
            Expr dcl = product.chcs[product.cycles[0][0]].srcRelation;
            concatenateVectors(combinedVars, source.invVars[source.loopRel], target.invVars[target.loopRel]);
            for (auto &pr : pairings) {
                Expr e = mk<EQ>(source.invVars[source.loopRel][pr[0]], target.invVars[target.loopRel][pr[1]]);
                mapping.insert(replaceAll(e, combinedVars, product.invVars[dcl]));
            }
        }

        bool learnInvariantsPr(Product_CHCs &ruleManager, bool lockstepCheck = false)
        {

            if (debug > 4) ruleManager.print(true);
            BndExpl bnd(ruleManager, to, debug);

            RndLearnerV3 ds(ruleManager.m_efac, ruleManager.m_z3, ruleManager, to, freqs, aggp, mut, dat,
                    doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, to, debug);

            map<Expr, ExprSet> cands;
            Expr dcl = ruleManager.chcs[ruleManager.cycles[0][0]].srcRelation;
            if (!ds.initializedDecl(dcl)) {
                ds.initializeDecl(dcl);

                // adding the matching explicitly
                cands[dcl].insert(mapping.begin(), mapping.end());

                if (dSee || lockstepCheck) {
                    Expr pref = bnd.compactPrefix(0);
                    ExprSet tmp;
                    getConj(pref, tmp);
                    for (auto & t : tmp)
                        if (hasOnlyVars(t, ruleManager.invVars[dcl]))
                            cands[dcl].insert(t);

                    if (mut > 0) ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
                    ds.initializeAux(cands[dcl], bnd, 0, pref);
                }
            }

            if (dat > 0) ds.getDataCandidates(cands);

            for (int i = 0; i < doProp; i++)
                for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
            ds.addCandidates(dcl, cands[dcl]);
            ds.prepareSeeds(dcl, cands[dcl]);

            // call bootstrap with option to only consider equalities as candidates for finding invariant
            // also add equalities for variable matchings
            bool check = ds.bootstrap();
            return check;
            //return (check && ds.verifySolution(mapping));
        }

        bool factSanityCheck(Expr &factBody) {
            return bool(u.isSat(factBody));
        }

        Expr getPrecondition(Product_CHCs &product) {
            Expr pre = conjoin(mapping, m_efac);
            return replaceAll(pre, product.invVars[product.loopRel], product.invVarsPrime[product.loopRel]);
        }

        bool checkLockstepComposability(Product_CHCs &product) {
            
            auto query = product.getQuery();
            auto &originalQuery = query->body;
            auto loopGuard1 = source.getPrecondition(&source.chcs[source.cycles[0][0]]);
            auto loopGuard2 = target.getPrecondition(&target.chcs[target.cycles[0][0]]);
            Expr lockstepCheckPredicate = mk<NEQ>(loopGuard2, loopGuard1);
            query->body = mk<AND>(lockstepCheckPredicate, originalQuery);
            // TODO: according to paper, we need to return <inv, cex>
            bool lockstepCheck = learnInvariantsPr(product, true);
            query->body = originalQuery;
            return lockstepCheck;
        }

        bool checkEquivalence(Product_CHCs &product) {
            auto loopGuardS = source.getPrecondition(&source.chcs[source.cycles[0][0]]);
            auto query = product.getQuery();
            auto &originalQuery = query->body;
            Expr negationLoopGuardS = mkNeg(loopGuardS);
            Expr post = simplifyBool(mkNeg(conjoin(mapping, m_efac)));
            // we only add negation of loop guard of source because we have verified, 
            // using lockstep check, that loop guards of source and target are always equal
            query->body = mk<AND>(originalQuery, mk<AND>(negationLoopGuardS, post));
            bool equivalenceCheck = learnInvariantsPr(product);
            query->body = originalQuery;
            return equivalenceCheck;
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

    void decomposeSource(Extended_CHCs& source, Extended_CHCs& target, Extended_CHCs& SDecomposed) {
        auto& efac = source.m_efac;
        auto& TCycles = target.cycles;
        auto TCyclesSize = TCycles.size();
        auto& TPrefixes = target.prefixes;
        auto& SPrefix = source.prefixes[0].back();
        auto& SCycle = source.cycles[0][0];
        auto& SCycleCHC = source.chcs[SCycle];
        Expr SLoopRel = SCycleCHC.srcRelation;
        Expr SLoopRel_i_minus_1 = mk<TRUE>(efac);
        ExprVector SLoopVars(SCycleCHC.head->args_begin()+1, SCycleCHC.head->args_end());
        ExprVector SLoopSrcVars = SCycleCHC.srcVars;
        Expr negSGuard;
        ExprVector invVars = source.invVars[SLoopRel];
        ExprVector invVarsPrime = source.invVarsPrime[SLoopRel];
 
        for (int cycleNum = 0; cycleNum < TCyclesSize; cycleNum++) {
            auto& cycleList = TCycles[cycleNum];
            auto& prefixList = TPrefixes[cycleNum];
            auto& prefixCHC = target.chcs[prefixList.back()];
            auto& cycleCHC = target.chcs[cycleList.back()];
            
            auto SFact = source.chcs[SPrefix];
            auto SLoop = source.chcs[SCycle];

            // if-condition is required according to the paper implementation
            //if (cycleNum < TCyclesSize-1) {
            // a better way would be to use precondition and eliminateQuantifiers
                auto TGuard = target.getPrecondition(&cycleCHC);
                auto P_i = replaceAll(TGuard, cycleCHC.srcVars, SLoop.srcVars);
                SLoop.body = mk<AND>(SLoop.body, P_i);
            //}

            Expr SLoopRel_i = mkTerm<string>(lexical_cast<string>(SLoopRel)+
                    "_"+to_string(cycleNum), efac);
            SDecomposed.invVars[SLoopRel_i] = invVars;
            SDecomposed.invVarsPrime[SLoopRel_i] = invVarsPrime;
            Expr SLoopHead_i = bind::fdecl(SLoopRel_i, SLoopVars);
            SDecomposed.decls.insert(SLoopHead_i);
            
            SFact.srcRelation = SLoopRel_i_minus_1;
            if (!isOpX<TRUE>(SLoopRel_i_minus_1)) {
                SFact.srcVars = SLoopSrcVars;
                SFact.body = negSGuard;
                SFact.isFact = false;
            }
            SFact.dstRelation = SLoopRel_i;
            SLoop.srcRelation = SLoop.dstRelation = SLoopRel_i;
            SLoop.head = SLoopHead_i;
            SLoopRel_i_minus_1 = SLoopRel_i;
            
            SDecomposed.chcs.push_back(SFact);
            SDecomposed.chcs.push_back(SLoop);

            auto SGuard = SDecomposed.getPrecondition(&SDecomposed.chcs.back());
            negSGuard = mkNeg(replaceAll(SGuard, invVars, invVarsPrime));
        }

        auto SQuery = source.getQuery();
        SQuery->srcRelation = SLoopRel_i_minus_1;
        SDecomposed.chcs.push_back(*SQuery);

        // a better way to populate cycles info; 
        // might not be needed if later we will have to make projections 
        SDecomposed.prefixes.clear();
        SDecomposed.cycles.clear();
        SDecomposed.outgs.clear();
        SDecomposed.wtoCHCs.clear();

        for (int i = 0; i < SDecomposed.chcs.size(); i++)
            SDecomposed.outgs[SDecomposed.chcs[i].srcRelation].push_back(i);
        SDecomposed.wtoSort();
    }

    void projection(Extended_CHCs& projRm, int i, Extended_CHCs &origRm) {
        auto &prefix = origRm.chcs[origRm.prefixes[i].back()];
        if (!prefix.isFact) {
            prefix.srcRelation = mk<TRUE>(origRm.m_efac);
            prefix.srcVars.clear();
            prefix.isFact = true;
        }
        projRm.chcs.push_back(prefix);
        auto &cycle = origRm.chcs[origRm.cycles[i][0]];
        projRm.chcs.push_back(cycle);
        Expr rel = cycle.srcRelation;
        projRm.decls.insert(origRm.getDecl(rel));
        projRm.invVars[rel] = origRm.invVars[rel];
        projRm.invVarsPrime[rel] = origRm.invVarsPrime[rel];

        projRm.chcs.push_back(HornRuleExt());
        HornRuleExt& hr = projRm.chcs.back();
        hr.srcRelation = cycle.srcRelation;
        hr.dstRelation = mk<FALSE>(origRm.m_efac);
        hr.isQuery = true;
        hr.isFact = false;
        hr.isInductive = false;
        hr.srcVars = cycle.srcVars;
        hr.dstVars = ExprVector();
        hr.body = mk<TRUE>(origRm.m_efac);

        for (int i = 0; i < projRm.chcs.size(); i++)
            projRm.outgs[projRm.chcs[i].srcRelation].push_back(i);

        projRm.wtoSort();
        projRm.loopRel = cycle.srcRelation;
    }
        
    bool checkEquivalence(Extended_CHCs &source, Extended_CHCs &target, bool doAlign,
            unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
            bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
            bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
    {
        int cycleSize1 = source.cycles.size();
        int cycleSize2 = target.cycles.size();
        auto& efac = source.m_efac;
        auto& z3 = source.m_z3;

        assert(cycleSize1 == 1);

        Extended_CHCs decomposedSource(source, true);
        decomposeSource(source, target, decomposedSource);
        assert(cycleSize2 == decomposedSource.cycles.size());

        for (int i = 0; i < cycleSize2; i++) {
            Extended_CHCs projectionSource(decomposedSource, true);
            projection(projectionSource, i, decomposedSource);
            
            Extended_CHCs projectionTarget(target, true);
            projection(projectionTarget, i, target);
            
            projectionSource.categorizeVars();
            projectionTarget.categorizeVars();
            // TODO: change the name from nonitercombs to just combs
            vector<vector<vector<int>>> nonIterCombs;
            createNonIterCombs(projectionSource, projectionTarget, nonIterCombs);

            bool equivalenceCheck;
            for (auto &comb : nonIterCombs) {
                // cex loop

                EquivalenceInPaper equiv(projectionSource, projectionTarget, maxAttempts, to, freqs,
                        aggp, dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat,
                        dStrenMbp, dFwd, dRec, dGenerous, dSee, debug, comb);

                while (true) {
                    bool aligned = false;
                    Product_CHCs product(projectionSource, projectionTarget, "_pr_", debug-2);
                    product.createProduct();

                    equiv.createVariableMapping(product);
                    auto fact = product.getFact();
                    fact->body = mk<AND>(fact->body, equiv.getPrecondition(product));

                    bool factSanity = equiv.factSanityCheck(fact->body);
                    bool lockstepCheck;
                    if (factSanity) {
                        lockstepCheck = equiv.checkLockstepComposability(product);
                    }
                    if (!factSanity || !lockstepCheck) {
                        // align the programs
                        auto itersFound = equiv.findIterators();
                        aligned = equiv.alignPrograms();
                        if (aligned) continue;
                        //return false;
                    }
                    else {
                        // check equivalence
                        equivalenceCheck = equiv.checkEquivalence(product);
                        if (equivalenceCheck) {
                            outs() << "current projections are equivalent\n";
                        }
                        else {
                            outs() << "current projections are not equivalent\n";
                            return false;
                        }
                    }
                    break;
                }
                if (equivalenceCheck) break;
            }
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
            outs() << "\nprogram equivalence is unknown\n";
    };
}

#endif
