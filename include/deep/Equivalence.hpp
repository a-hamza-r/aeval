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

                outs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
            }
    };


    class EquivalenceInPaper 
    {
        private:
            ExprFactory &m_efac;
            EZ3 &m_z3;
            //Extended_CHCs &source;
            //Extended_CHCs &target;
            SMTUtils u;

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
            bool allowEq;

        EquivalenceInPaper(Extended_CHCs &r1, Extended_CHCs &r2,
                unsigned _maxAttempts, unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut,
                bool _doElim, bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp, bool _dAddProp, bool _dAddDat,
                bool _dStrenMbp, int _dFwd, bool _dRec, bool _dGenerous, bool _dSee, bool _allowEq, int _debug) :
            m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to), 
            //source(r1), target(r2),
            maxAttempts(_maxAttempts), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
            doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp), mbpEqs(_mbpEqs), dAllMbp(_dAllMbp),
            dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec),
            dGenerous(_dGenerous), dSee(_dSee), allowEq(_allowEq), debug(_debug)
        {}

        bool learnInvariantsPr(CHCs &ruleManager)
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
                //cands[dcl] = currentMatching;  // adding the matching explicitly

                // GF: most likely, you won't need any of these,
                //     so I disabled it to improve performance.
                //     In case some bench requires a specific invariant,
                //     try to enable gradually.

                if (allowEq)
                {
                    auto & chc = ruleManager.chcs[ruleManager.prefixes[i][0]];
                    if (chc.dstRelation == dcl)
                        for (auto & v : chc.dstVars)
                        {
                            if (containsOp<ARRAY_TY>(v)) continue;
                            ExprVector tmp = {v};
                            getConj(replaceAll(keepQuantifiers(chc.body, tmp),
                                        chc.dstVars, ruleManager.invVars[dcl]), cands[dcl]);
                        }
                }

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
            return check;
                //ds.verifySolution(currentMatching);
        }


        void decomposeSource(Extended_CHCs& source, Extended_CHCs& target, Extended_CHCs& SDecomposed) {
            auto& efac = source.m_efac;
            auto& TCycles = target.cycles;
            auto& TPrefixes = target.prefixes;
            int TCyclesSize = TCycles.size();
            auto& SCycle = source.cycles[0][0];
            auto& SPrefix = source.prefixes[0].back();
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
                negSGuard = mkNeg(SGuard);
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
            hr.body = mkNeg(origRm.getPrecondition(&cycle));

            for (int i = 0; i < projRm.chcs.size(); i++)
                projRm.outgs[projRm.chcs[i].srcRelation].push_back(i);

            projRm.wtoSort();
            projRm.loopRel = cycle.srcRelation;
        }
        
        bool factSanityCheck(Expr &factBody) {
            return bool(u.isSat(factBody));
        }

        Expr getPrecondition(Extended_CHCs &source, Extended_CHCs &target, vector<vector<int>> &combs) {

            Expr sourceCycleRel = source.loopRel;
            Expr targetCycleRel = target.loopRel;
            Expr precondition = mk<TRUE>(m_efac);
            for (auto &pr : combs) {
                precondition = mk<AND>(precondition, mk<EQ>(
                    source.invVarsPrime[sourceCycleRel][pr[0]], target.invVarsPrime[targetCycleRel][pr[1]]));
            }
            return simplifyBool(precondition);
        }

        bool checkLockstepComposability(Product_CHCs &product, Extended_CHCs &rm1, Extended_CHCs &rm2) {
            
            auto query = product.getQuery();
            auto &originalQuery = query->body;
            auto loopGuard1 = rm1.getPrecondition(&rm1.chcs[rm1.cycles[0][0]]);
            auto loopGuard2 = rm2.getPrecondition(&rm2.chcs[rm2.cycles[0][0]]);
            Expr lockstepCheckPredicate = mk<NEQ>(loopGuard2, loopGuard1);
            query->body = mk<AND>(lockstepCheckPredicate, originalQuery);
            // TODO: according to paper, we need to return <inv, cex>
            bool lockstepCheck = learnInvariantsPr(product);
            query->body = originalQuery;
            return lockstepCheck;
        }

        bool checkEquivalence(Product_CHCs &product, vector<vector<int>>& combs, 
                Extended_CHCs &source, Extended_CHCs &target) {
            auto &sourceVars = source.invVars[source.loopRel];
            auto &targetVars = target.invVars[target.loopRel];
            auto query = product.getQuery();
            auto &originalQuery = query->body;
            // TODO: temporarily create a mapping, later need to pass it as a parameter
            Expr mapping = mk<TRUE>(product.m_efac);
            for (auto &pr : combs) {
                mapping = mk<AND>(mapping, mk<EQ>(sourceVars[pr[0]], targetVars[pr[1]]));
            }
            Expr post = simplifyBool(mkNeg(mapping));
            query->body = mk<AND>(post, originalQuery);
            bool equivalenceCheck = learnInvariantsPr(product);
            query->body = originalQuery;
            return equivalenceCheck;
        }
    };

    class Equivalence
    {
        private:
            ExprFactory &m_efac;
            EZ3 &m_z3;
            Extended_CHCs &ruleManager1;
            Extended_CHCs &ruleManager2;
            SMTUtils u;
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
            bool allowEq;

            Equivalence(Extended_CHCs &r1, Extended_CHCs &r2, vector<vector<int>> combs, 
                    unsigned _maxAttempts, unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut,
                    bool _doElim, bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp, bool _dAddProp, bool _dAddDat,
                    bool _dStrenMbp, int _dFwd, bool _dRec, bool _dGenerous, bool _dSee, bool _allowEq, int _debug) :
                m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to), ruleManager1(r1), ruleManager2(r2), pairings(combs),
                maxAttempts(_maxAttempts), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
                doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp), mbpEqs(_mbpEqs), dAllMbp(_dAllMbp),
                dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec),
                dGenerous(_dGenerous), dSee(_dSee), allowEq(_allowEq), debug(_debug)
        {}

            bool learnInvariantsPr(CHCs &ruleManager, ExprSet& currentMatching, bool lockStepCheck=false)
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

                    if (allowEq)
                    {
                        auto & chc = ruleManager.chcs[ruleManager.prefixes[i][0]];
                        if (chc.dstRelation == dcl)
                            for (auto & v : chc.dstVars)
                            {
                                if (containsOp<ARRAY_TY>(v)) continue;
                                ExprVector tmp = {v};
                                getConj(replaceAll(keepQuantifiers(chc.body, tmp),
                                            chc.dstVars, ruleManager.invVars[dcl]), cands[dcl]);
                            }
                    }

                    if (!lockStepCheck && !dSee) continue;
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


            bool getAlignmentVals(ExprSet& pre)
            {
                /*
                   int iter1 = ruleManager1.iter, iter2 = ruleManager2.iter;
                   Expr rel1 = ruleManager1.loopRel, rel2 = ruleManager2.loopRel;

                   outs() << "\n\nassuming iters: "
                   << ruleManager1.invVars[rel1][iter1] << " and " << ruleManager2.invVars[rel2][iter2] << "\n";
                   */

                Expr numIters1 = ruleManager1.numOfIters;
                Expr numIters2 = ruleManager2.numOfIters;
                //outs() << "numIters: " << numIters1 << " and " << numIters2 << "\n";

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
                            preForEqualityCheck.insert(mk<EQ>(var1Dst, var2Dst));
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
                    ruleManager1.createAlignment(0, possibleAlign[0], 0, bnd1, prefixBody1, false);
                    ruleManager2.createAlignment(0, possibleAlign[1], 0, bnd2, prefixBody2, false);

                    equalityChecks.insert(prefixBody1);
                    equalityChecks.insert(prefixBody2);

                    Expr eq = mk<EQ>(iterF, iterS);
                    impliesEq = bool(u.implies(conjoin(equalityChecks, m_efac), eq));

                    if (impliesEq)
                    {
                        Expr prefixBody1 = prefixRule1.body, prefixBody2 = prefixRule2.body;
                        // actual alignment created here
                        ruleManager1.createAlignment(itersInLoopR1, possibleAlign[0], itersOutLoopR1-possibleAlign[0], bnd1, prefixBody1);
                        prefixRule1.body = prefixBody1;

                        ruleManager2.createAlignment(itersInLoopR2, possibleAlign[1], itersOutLoopR2-possibleAlign[1], bnd2, prefixBody2);
                        prefixRule2.body = prefixBody2;

                        for (auto &chc : ruleManager1.chcs)
                        {
                            chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);
                            chc.locVars.clear();
                        }

                        for (auto &chc : ruleManager2.chcs)
                        {
                            chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);
                            chc.locVars.clear();
                        }

                        return true;
                    }
                }
                return false;
            }


            bool checkEquivalence(bool innerLoop)
            {
                HornRuleExt *q1 = ruleManager1.getQuery(), *q2 = ruleManager2.getQuery();
                HornRuleExt *f1 = ruleManager1.getFact(), *f2 = ruleManager2.getFact();
                /* used when alignment is done, but for now not needed
                f1->srcVars = ruleManager1.factSrcVars; 
                f2->srcVars = ruleManager2.factSrcVars;
                q1->dstVars = ruleManager1.queryDstVars;
                q2->dstVars = ruleManager2.queryDstVars;
                */

                // create the product
                Product_CHCs ruleManagerProduct(ruleManager1, ruleManager2, "_pr_", debug-2);
                ruleManagerProduct.createProduct();
                assert(ruleManagerProduct.chcs.size() == 3);

                HornRuleExt *fact, *query, *ind;
                for (auto &chc : ruleManagerProduct.chcs)
                {
                    if (chc.isFact) fact = &chc;
                    if (chc.isQuery) query = &chc;
                    if (chc.isInductive) ind = &chc;
                }

                // create pre and post conditions
                ExprSet pre, post;
                //if (ruleManager1.iter >= 0) post.insert(mk<EQ>(q1->srcVars[ruleManager1.iter], q2->srcVars[ruleManager2.iter]));
                if (pairings[0][0] != -1)
                {
                    for (auto &pair : pairings)
                    {
                        // TODO: this is when alignment is needed but need generic, fix later:
                        //pre.insert(mk<EQ>(f1->srcVars[pair[0]], f2->srcVars[pair[1]]));
                        //post.insert(mk<EQ>(q1->dstVars[pair[0]], q2->dstVars[pair[1]]));
                        
                        pre.insert(mk<EQ>(f1->dstVars[pair[0]], f2->dstVars[pair[1]]));
                        post.insert(mk<EQ>(q1->srcVars[pair[0]], q2->srcVars[pair[1]]));
                    }
                }
                fact->body = simplifyBool(mk<AND>(fact->body, conjoin(pre, m_efac)));
                Expr queryBody = query->body;
                ExprVector queryLocVars = query->locVars;
                
                ExprSet lin;
                query->srcVars.clear();
                ExprVector postSrc, dummy;
                concatenateVectors(postSrc, q1->srcVars, q2->srcVars);
                query->assignVarsAndRewrite(postSrc, ruleManagerProduct.invVars[query->srcRelation],
                        dummy, dummy, lin);
                
                ExprSet currentMatching;
                int sz = ind->srcVars.size()/2;

                for (int i = 0; i < sz; i++)
                    if (bind::typeOf(ind->srcVars[i]) == bind::typeOf(ind->srcVars[sz + i])) {
                        currentMatching.insert(mk<EQ>(ind->srcVars[i], (ind->srcVars[sz + i])));
                    }
                
                Expr lockStepCheck = mk<NEQ>(ruleManager1.loopGuard, ruleManager2.loopGuard);
                query->body = simplifyBool(mk<AND>(lockStepCheck, conjoin(lin, m_efac)));
                
                for (auto &chc : ruleManagerProduct.chcs)
                {
                    chc.body = eliminateQuantifiers(chc.body, chc.locVars, true, false);
                    chc.locVars.clear();
                }
                outs() << "product for lockstep check\n";
                ruleManagerProduct.print(true);

                ExprSet dummyS;
                // we need dSee set to true (compute seeds), because many times the invariant cannot be found
                // since candidates available are not enough, especially while checking lockstep
                if (!learnInvariantsPr(ruleManagerProduct, currentMatching, true)) {
                    outs() << "no lockstep\n";
                    return false;
                }

                //Expr phi = myAbduce(conjoin(post, m_efac), queryBody, postSrc);
                Expr phi = conjoin(post, m_efac);
                query->body = simplifyBool(mk<AND>(simplifyBool(mkNeg(phi)), conjoin(lin, m_efac)));
                query->body = mk<AND>(query->body, simplifyBool(mkNeg(ruleManagerProduct.getPrecondition(ind))));

                // replace the body of the loop with the loop summary
                if (!innerLoop)
                {
                    Expr srcEq = conjoin(currentMatching, m_efac);
                    Expr dstEq = replaceAll(srcEq, ind->srcVars, ind->dstVars);
                    ind->body = mk<AND>(ind->body, mk<IMPL>(srcEq, dstEq));
                }

                //query->body = eliminateQuantifiers(query->body, queryLocVars, true, false);

                //outs() << "equivalence check: \n";
                //ruleManagerProduct.print(true);
                outs () << "   check fact sanity:  "  << bool(u.isSat(fact->body)) << "\n";
                outs () << "   check query sanity:  "  << bool(u.isSat(query->body)) << "\n";
                outs () << "   check ind sanity:  "  << bool(u.isSat(ind->body)) << "\n";

                outs() << "------------------------PRODUCT CREATED-----------------------------\n\n";

                // call the function with all default values for arguments that are not relevant
                // probably, do a cleaner way of calling the function
                return learnInvariantsPr(ruleManagerProduct, currentMatching);
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


    void constructNewRuleManager(Extended_CHCs &newRM, Extended_CHCs &oldRM, Expr loop,
            bool hasMultipleLoops = false, bool addTransition = false, bool deleteOldRules = false)
    {
        newRM.decls = oldRM.decls;
        newRM.failDecl = oldRM.failDecl;
        newRM.invVars = oldRM.invVars;
        newRM.invVarsPrime = oldRM.invVarsPrime;
        newRM.iter = oldRM.iter;
        newRM.numOfIters = oldRM.numOfIters;
        newRM.iterGrows = oldRM.iterGrows;
        newRM.loopRel = loop;
        newRM.varsInt = oldRM.varsInt;
        newRM.varsBool = oldRM.varsBool;
        newRM.varsArray = oldRM.varsArray;
        newRM.queryDstVars = oldRM.queryDstVars;
        newRM.factSrcVars = oldRM.factSrcVars;
        newRM.loopGuard = oldRM.loopGuard;

        Expr newName1, newName2;
        // create rules of form:
        // true -> newInv1; newInv1 -> inv; inv -> inv; inv -> newInv2; newInv2 -> false;
        // this is required for multiple loops and nested loops
        if (hasMultipleLoops) {
            newName1 = mkTerm<string>("newInv1", oldRM.m_efac);
            newName2 = mkTerm<string>("newInv2", oldRM.m_efac);
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
        }

        for (auto it = oldRM.wtoCHCs.begin(); it != oldRM.wtoCHCs.end(); )
        {
            auto chc = *(*it);
            if (loop == chc.srcRelation || loop == chc.dstRelation)
            {
                if (chc.srcRelation != loop && hasMultipleLoops)
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
                    hr.body = mk<TRUE>(oldRM.m_efac);
                }

                else if (chc.dstRelation != loop && hasMultipleLoops)
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
                    hr.body = mk<TRUE>(oldRM.m_efac);
                }
                newRM.chcs.push_back(chc);
                if (deleteOldRules) it = oldRM.wtoCHCs.erase(it);
                else it++;
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

        for (int i = 0; i < newRM.chcs.size(); i++)
            newRM.outgs[newRM.chcs[i].srcRelation].push_back(i);

        newRM.wtoSort();
    }


    bool checkEquivalenceSingleLoop(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2, bool doAlign,
            unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
            bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
            bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, bool allowEq, int debug,
            bool innerLoop, bool requireIters = true)
    {
        //if (doAlign) 
        //{
        ruleManager1.preprocessing();
        ruleManager2.preprocessing();

        // if no iterator was found, the tool exits stating non-equivalence. Support more
        bool iterFound = ruleManager1.findIterators(requireIters);
        //if (innerLoop && !iterFound)
        //{
        //    outs() << "no iterator was found for program 1. program equivalence is unknown\n";
        //    return false;
        //}

        iterFound = ruleManager2.findIterators(requireIters);
        //if (innerLoop && !iterFound)
        //{
        //    outs() << "no iterator was found for program 2. program equivalence is unknown\n";
        //    return false;
        //}
        //}

        vector<vector<vector<int>>> nonIterCombs;
        createNonIterCombs(ruleManager1, ruleManager2, nonIterCombs);

        // check for all combinations of variables, such that we match same type of variables
        for (auto &pairings : nonIterCombs)
        {
            Extended_CHCs newRuleManager1(ruleManager1.m_efac, ruleManager1.m_z3, "_v1_", debug-2);
            Extended_CHCs newRuleManager2(ruleManager1.m_efac, ruleManager1.m_z3, "_v2_", debug-2);

            constructNewRuleManager(newRuleManager1, ruleManager1, ruleManager1.loopRel);
            constructNewRuleManager(newRuleManager2, ruleManager2, ruleManager2.loopRel);

            for (auto &pr : pairings) {
                if (pr[1] != -1 && pr[1] == newRuleManager2.iter) {
                    auto& cycle = newRuleManager1.chcs[newRuleManager1.cycles[0][0]];
                    auto vars1 = newRuleManager1.invVars[newRuleManager1.loopRel];
                    auto vars2 = newRuleManager2.invVars[newRuleManager2.loopRel];
                    Expr loopG = replaceAll(newRuleManager2.loopGuard, vars2[pr[1]], vars1[pr[0]]);
                    cycle.body = mk<AND>(cycle.body, loopG);
                    break;
                }
            }

            Equivalence eq(newRuleManager1, newRuleManager2, pairings, maxAttempts, to, freqs,
                    aggp, dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat,
                    dStrenMbp, dFwd, dRec, dGenerous, dSee, allowEq, debug);

            if (innerLoop && !eq.initialSanityChecks()) return false;
            if (innerLoop && doAlign && !eq.alignPrograms()) return false;
            if (eq.checkEquivalence(innerLoop))
            {
                outs() << "\ncurrent loop is equivalent\n";
                return true;
            }
        }
        outs() << "\nequivalence of current loops is unknown\n";
        return false;
    }

    bool checkEquivalence(Extended_CHCs &source, Extended_CHCs &target, bool doAlign,
            unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
            bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
            bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, bool allowEq, int debug)
    {
        int cycleSize1 = source.cycles.size();
        int cycleSize2 = target.cycles.size();
        auto& efac = source.m_efac;
        auto& z3 = source.m_z3;

        assert(cycleSize1 == 1);

        if (cycleSize1 == cycleSize2) {
            // current support for single loops or similarly nested loops
            for (int i = 0; i < cycleSize1; i++)
            {
                Expr loop1 = source.chcs[source.cycles[i][0]].srcRelation;
                Expr loop2 = target.chcs[target.cycles[i][0]].srcRelation;
                outs() << "currently processing: " << loop1 << " and " << loop2 << "\n";

                Extended_CHCs newsource(source.m_efac, source.m_z3, "_v1_", debug-2);
                Extended_CHCs newtarget(source.m_efac, source.m_z3, "_v2_", debug-2);

                bool hasMultipleLoops = source.cycles.size()>1;
                constructNewRuleManager(newsource, source, loop1, hasMultipleLoops, i>0, true);
                constructNewRuleManager(newtarget, target, loop2, hasMultipleLoops, i>0, true);

                if (!checkEquivalenceSingleLoop(newsource, newtarget, doAlign, maxAttempts, to, freqs, aggp,
                            dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec,
                            dGenerous, dSee, allowEq, debug, i <= 0))
                    return false;
            }
            return true;
        }
        else {
            // current support for multi-phase loops, where one program has single loop and other contains multiple
            assert(cycleSize1 == 1 && cycleSize2 > 1);
            
            EquivalenceInPaper equiv(source, target, maxAttempts, to, freqs,
                    aggp, dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat,
                    dStrenMbp, dFwd, dRec, dGenerous, dSee, allowEq, debug);

            // TODO: whether it is a good idea to keep source, target, decomposed source, projections
            // and products in the class or not
            Extended_CHCs decomposedSource(source, true);
            equiv.decomposeSource(source, target, decomposedSource);
            assert(cycleSize2 == decomposedSource.cycles.size());

            for (int i = 0; i < cycleSize2; i++) {
                Extended_CHCs projectionSource(decomposedSource, true);
                equiv.projection(projectionSource, i, decomposedSource);
                
                Extended_CHCs projectionTarget(target, true);
                equiv.projection(projectionTarget, i, target);

                projectionSource.categorizeVars();
                projectionTarget.categorizeVars();
                // TODO: change the name from nonitercombs to just combs
                vector<vector<vector<int>>> nonIterCombs;
                createNonIterCombs(projectionSource, projectionTarget, nonIterCombs);

                bool equivalenceCheck;
                for (auto &comb : nonIterCombs) {
                    // cex loop
                    while (true) {
                        Product_CHCs product(projectionSource, projectionTarget, "_pr_", debug-2);
                        product.createProduct();

                        Expr precondition = equiv.getPrecondition(projectionSource, projectionTarget, comb);
                        auto fact = product.getFact();
                        fact->body = mk<AND>(fact->body, precondition);

                        bool factSanity = equiv.factSanityCheck(fact->body);
                        bool lockstepCheck;
                        if (factSanity) {
                            lockstepCheck = equiv.checkLockstepComposability(product, projectionSource, projectionTarget);
                        }
                        if (!factSanity || !lockstepCheck) {
                            // align the programs
                        }
                        else {
                            // check equivalence
                            equivalenceCheck = equiv.checkEquivalence(product, comb, projectionSource, projectionTarget);
                            if (equivalenceCheck) {
                                outs() << "current projections are equivalent\n";
                            }
                            else {
                                outs() << "current projections are not equivalent\n";
                            }
                        }
                        break;
                    }
                    if (equivalenceCheck) break;
                }
            }
            return true;

            Expr loopGuard1, loopGuard2;
            Expr loop1 = source.chcs[source.cycles[0][0]].srcRelation;

            for (int i = 0; i < cycleSize2; i++) {
                Expr loop2 = target.chcs[target.cycles[i][0]].srcRelation;

                Extended_CHCs newsource(source.m_efac, source.m_z3, "_v1_", debug-2);
                constructNewRuleManager(newsource, source, loop1, false, false, false);
                Extended_CHCs newtarget(target.m_efac, target.m_z3, "_v2_", debug-2);
                constructNewRuleManager(newtarget, target, loop2, true, false, true);

                if (i > 0) {
                    // when considering all cycles, except for the first one, for the 2nd program,
                    // the fact should be true, as we do not want the initial state of the loop to be
                    // represented by initial inputs but some precondition that is added later;
                    auto chc1 = newsource.getFact();
                    chc1->body = mk<TRUE>(newsource.m_efac);
                    
                    // we also create a new fact for the target because it is removed in the first iteration 
                    newtarget.chcs.push_back(HornRuleExt());
                    HornRuleExt &hr = newtarget.chcs.back();
                    hr.dstVars = newtarget.invVarsPrime[loop2];
                    hr.srcRelation = mk<TRUE>(newtarget.m_efac);
                    hr.dstRelation = loop2;
                    hr.isFact = true;
                    hr.isQuery = false;
                    hr.body = simplifyArithm(mkNeg(replaceAll(loopGuard2, target.invVars[loop2], target.invVarsPrime[loop2])));
                    
                    // TODO: remove and devise a better way to deal with cycles not being computed
                    newtarget.prefixes.clear();
                    newtarget.cycles.clear();
                    newtarget.outgs.clear();
                    newtarget.wtoCHCs.clear();

                    for (int i = 0; i < newtarget.chcs.size(); i++)
                        newtarget.outgs[newtarget.chcs[i].srcRelation].push_back(i);
                    newtarget.wtoSort();
                }

                auto& cycle1 = newsource.chcs[newsource.cycles[0][0]];
                auto& cycle2 = newtarget.chcs[newtarget.cycles[0][0]];
                loopGuard2 = newtarget.getPrecondition(&cycle2);
                // TODO: right now, assumes that variables pair at the same index, generalize that
                Expr restrictIters = replaceAll(loopGuard2, cycle2.srcVars, cycle1.srcVars);
                cycle1.body = mk<AND>(cycle1.body, restrictIters);
                loopGuard1 = newsource.getPrecondition(&cycle1);
                
                newsource.loopGuard = loopGuard1;
                newtarget.loopGuard = loopGuard2;

                //outs() << "printing rule Manager1 after decomposition\n";
                //newsource.print(true);
                //outs() << "printing rule Manager2 after decomposition\n";
                //newtarget.print(true);

                newsource.loopRel = newsource.chcs[newsource.cycles[0][0]].srcRelation;
                // 3rd option is doAlign, however, this needs better handling
                if (!checkEquivalenceSingleLoop(newsource, newtarget, false, maxAttempts, to, freqs, aggp,
                            dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec,
                            dGenerous, dSee, allowEq, debug, true, false))
                    return false;
            }
            return true;
        }
    }




    // check equivalence of programs
    inline void checkEquivalenceOfPrograms(const char *chcfileSrc, const char *chcfileDst, bool doAlign,
            unsigned maxAttempts, unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
            bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp, bool dAddDat,
            bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, bool allowEq, int debug)
    {
        ExprFactory m_efac;
        EZ3 z3(m_efac);

        Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-2);
        Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_", debug-2);

        if (!ruleManagerSrc.parse(string(chcfileSrc), doElim, doArithm)) return;
        if (!ruleManagerDst.parse(string(chcfileDst), doElim, doArithm)) return;

        if (checkEquivalence(ruleManagerSrc, ruleManagerDst, doAlign, maxAttempts, to, freqs, aggp, dat, mut, doElim,
                    doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, allowEq, debug))
            outs() << "\nprograms are equivalent\n";
        else
            outs() << "\nprogram equivalence is unknown\n";
    };
}

#endif
