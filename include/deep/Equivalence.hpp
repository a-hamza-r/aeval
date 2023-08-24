#ifndef EQUIVALENCE__HPP__
#define EQUIVALENCE__HPP__

#include "Extended_Horn.hpp"

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

        public:
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
            vector<pair<int, int>> pairings;
            ExprSet mapping;

        EquivalenceInPaper(Extended_CHCs &r1, Extended_CHCs &r2,
                unsigned _to, bool _freqs, bool _aggp, int _dat, int _mut, bool _doElim,
                bool _doArithm, bool _doDisj, int _doProp, int _mbpEqs, bool _dAllMbp,
                bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int _dFwd, bool _dRec,
                bool _dGenerous, bool _dSee, int _debug, vector<pair<int, int>> &_pairings) :
            m_efac(r1.m_efac), m_z3(r1.m_z3), u(r1.m_efac, _to), 
            source(r1), target(r2), to(_to), freqs(_freqs), aggp(_aggp), dat(_dat), mut(_mut),
            doElim(_doElim), doArithm(_doArithm), doDisj(_doDisj), doProp(_doProp),
            mbpEqs(_mbpEqs), dAllMbp(_dAllMbp), dAddProp(_dAddProp), dAddDat(_dAddDat),
            dStrenMbp(_dStrenMbp), dFwd(_dFwd), dRec(_dRec), dGenerous(_dGenerous),
            dSee(_dSee), debug(_debug), pairings(_pairings)
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
            return source.findIterators() && target.findIterators();
        }

        bool getAlignmentVals(ExprSet& pre, int &itersInLoop1, int &itersOutLoop1,
                int &itersInLoop2, int &itersOutLoop2)
        {
            Expr numItersS = source.numOfIters;
            Expr numItersT = target.numOfIters;

            // variables required for the quantified formula for optimization query
            Expr coef1 = bind::intConst(mkTerm<string>("coef1", m_efac));
            Expr coef2 = bind::intConst(mkTerm<string>("coef2", m_efac));
            Expr const1 = bind::intConst(mkTerm<string>("const1", m_efac));
            Expr const2 = bind::intConst(mkTerm<string>("const2", m_efac));
            Expr numIters1 = bind::intConst(mkTerm<string>("numIters1", m_efac));
            Expr numIters2 = bind::intConst(mkTerm<string>("numIters2", m_efac));

            // remove redundant clauses in precondition
            for (auto it = pre.begin(); it != pre.end(); )
                if (emptyIntersect(*it, numItersS) &&
                        emptyIntersect(*it, numItersT)) it = pre.erase(it);
                else ++it;

            // add exact value for numIters to precondition
            pre.insert(mk<EQ>(numIters1, numItersS));
            pre.insert(mk<EQ>(numIters2, numItersT));
            Expr exprPre = conjoin(pre, m_efac);

            // get all variables in the precondition
            ExprVector varsIters;
            filter(exprPre, IsConst(), inserter(varsIters, varsIters.begin()));

            auto zero = mkMPZ(0, m_efac);
            // coef1 > 0 && coef2 > 0
            Expr coefs = mk<AND>(mk<GT>(coef1, zero), mk<GT>(coef2, zero));
            // const1 >= 0 && const2 >= 0
            Expr consts = mk<AND>(mk<GEQ>(const1, zero), mk<GEQ>(const2, zero));
            // coef2 * (numIters1 - const1) = coef1 * (numIters2 - const2)
            Expr constraint = mk<EQ>(mk<MULT>(coef2, mk<MINUS>(numIters1, const1)),
                    mk<MULT>(coef1, mk<MINUS>(numIters2, const2)));
            // pre => constraint
            Expr preImpliesCst = mk<IMPL>(exprPre, constraint);
            Expr quantifiedPreImpliesCst = createQuantifiedFormulaRestr(preImpliesCst, varsIters);
            // exists coef1, coef2, const1, const2 . forall varsIters . pre => constraint
            Expr quantifiedFla = mk<AND>(mk<AND>(consts, coefs), quantifiedPreImpliesCst);

            ExprMap c1, c2, c12;
            c12[const1] = zero;     c12[const2] = zero;
            c1[const1] = zero;      c2[const2] = zero;

            Expr model = nullptr;
            if (bool(u.isSat(replaceAll(quantifiedFla, c12)))) model = u.getModel();
            else if (bool(u.isSat(replaceAll(quantifiedFla, c1)))) model = u.getModel();
            else if (bool(u.isSat(replaceAll(quantifiedFla, c2)))) model = u.getModel();
            else if (bool(u.isSat(quantifiedFla))) model = u.getModel();
            if (model == nullptr)
            {
                outs() << "No satisfying assignment for quantified formula was found\n";
                return false;
            }

            // iterative solving optimization query to get all minModels
            ExprMap mp;
            ExprSet s{coef1, coef2, const1, const2};
            Expr minCoef1, minCoef2, minConst1, minConst2;

            // Solve for min coef1
            u.getOptModel<LT>(s, mp, coef1);
            minCoef1 = mp[coef1];
            quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef1, minCoef1));
            u.isSat(quantifiedFla);

            // Solve for min coef2
            u.getOptModel<LT>(s, mp, coef2);
            minCoef2 = mp[coef2];
            quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(coef2, minCoef2));
            u.isSat(quantifiedFla);

            // Solve for min const1
            u.getOptModel<LT>(s, mp, const1);
            minConst1 = mp[const1];
            quantifiedFla = mk<AND>(quantifiedFla, mk<EQ>(const1, minConst1));
            u.isSat(quantifiedFla);

            // Solve for min const2
            u.getOptModel<LT>(s, mp, const2);
            minConst2 = mp[const2];

            itersInLoop1 = (int)lexical_cast<cpp_int>(minCoef1);
            itersOutLoop1 = (int)lexical_cast<cpp_int>(minConst1);
            itersInLoop2 = (int)lexical_cast<cpp_int>(minCoef2);
            itersOutLoop2 = (int)lexical_cast<cpp_int>(minConst2);

            outs() << "copy "
                << itersOutLoop1 << " iterations of loop 1 to fact and query combined\n";
            outs() << "copy "
                << itersOutLoop2 << " iterations of loop 2 to fact and query combined\n";
            outs() << "we need " << itersInLoop1 << " iterations of loop 1 to align\n";
            outs() << "we need " << itersInLoop2 << " iterations of loop 2 to align\n";

            return true;
        }

        bool alignPrograms()
        {
            HornRuleExt &cycleS = source.chcs[source.cycles[0][0]];
            HornRuleExt &prefixS = source.chcs[source.prefixes[0][0]];

            HornRuleExt &cycleT = target.chcs[target.cycles[0][0]];
            HornRuleExt &prefixT = target.chcs[target.cycles[0][0]];

            BndExpl bnd1(source, debug);
            BndExpl bnd2(target, debug);
            Expr pref1 = bnd1.compactPrefix(0), pref2 = bnd2.compactPrefix(0);
            int iterS = source.iter, iterT = target.iter;
            ExprSet equalityChecks, preForQuantifiedFla;

            for (const auto &pair : pairings)
            {
                auto &p1 = pair.first, &p2 = pair.second;
                Expr var1Src = cycleS.srcVars[p1];
                Expr var2Src = cycleT.srcVars[p2];
                Expr var1Dst = cycleS.dstVars[p1];
                Expr var2Dst = cycleT.dstVars[p2];

                // we create here the pre required for quantified formula
                // and pre to check equality of iters later
                // we do not want to add arrays to any of the pre version
                if (!isOpX<ARRAY_TY>(bind::typeOf(var1Src)))
                {
                    equalityChecks.insert(mk<EQ>(var1Dst, var1Dst));
                    preForQuantifiedFla.insert(mk<EQ>(var1Src, var2Src));
                }
            }

            int itersInLoopS, itersOutLoopS, itersInLoopT, itersOutLoopT;
            if (!getAlignmentVals(preForQuantifiedFla, itersInLoopS, itersOutLoopS,
                        itersInLoopT, itersOutLoopT)) return false;

            // Currently, it does all combinations to check the number of iterations
            // to be added to fact and query
            vector<int> combsS, combsT;
            for (int i = 0; i <= itersOutLoopS; i++) combsS.push_back(i);
            for (int i = 0; i <= itersOutLoopT; i++) combsT.push_back(i);

            vector<pair<int, int>> possibleFactAligns;
            for (auto &it : combsS)
                for (auto &it2 : combsT)
                    possibleFactAligns.push_back({it, it2});

            Expr eq = mk<EQ>(cycleS.dstVars[iterS], cycleT.dstVars[iterT]);
            for (const auto &possibleAlign : possibleFactAligns)
            {
                Expr prefixBody1 = prefixS.body, prefixBody2 = prefixT.body;
                int toFactS = possibleAlign.first, toFactT = possibleAlign.second;
                int toQueryS = itersOutLoopS - toFactS, toQueryT = itersOutLoopT - toFactT;

                // check if adding certain iterations to fact will make
                // the initial values of iterators equal
                // it is not greedy approach currently
                source.createAlignment(0, toFactS, 0, bnd1, prefixBody1, false);
                target.createAlignment(0, toFactT, 0, bnd2, prefixBody2, false);
                equalityChecks.insert(prefixBody1);
                equalityChecks.insert(prefixBody2);

                if (bool(u.implies(conjoin(equalityChecks, m_efac), eq)))
                {
                    Expr prefixBody1 = prefixS.body, prefixBody2 = prefixT.body;
                    // actual alignment created here
                    source.createAlignment(itersInLoopS, toFactS, toQueryS, bnd1, prefixBody1);
                    prefixS.body = prefixBody1;

                    target.createAlignment(itersInLoopT, toFactT, toQueryT, bnd2, prefixBody2);
                    prefixT.body = prefixBody2;

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
            concatenateVectors(combinedVars,
                    source.invVars[source.loopRel], target.invVars[target.loopRel]);

            for (const auto &pr : pairings) {
                Expr e = mk<EQ>(source.invVars[source.loopRel][pr.first],
                        target.invVars[target.loopRel][pr.second]);
                mapping.insert(replaceAll(e, combinedVars, product.invVars[dcl]));
            }
        }

        bool learnInvariantsPr(Product_CHCs &ruleManager, bool lockstepCheck = false)
        {

            if (debug > 4) ruleManager.print(true);
            BndExpl bnd(ruleManager, to, debug);

            RndLearnerV3 ds(ruleManager.m_efac, ruleManager.m_z3, ruleManager, to, freqs, aggp,
                    mut, dat, doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec,
                    dGenerous, to, debug);

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

        Expr getRelationalPrecondition(Product_CHCs &product) {
            Expr pre = conjoin(mapping, m_efac);
            return replaceAll(pre,
                    product.invVars[product.loopRel], product.invVarsPrime[product.loopRel]);
        }

        bool checkLockstepComposability(Product_CHCs &product) {
            
            auto query = product.getQuery();
            const auto &originalQuery = query->body;
            const auto loopGuard1 = std::move(
                    simplifyArithm(source.getPrecondition(&source.chcs[source.cycles[0][0]])));
            const auto loopGuard2 = std::move(
                    simplifyArithm(target.getPrecondition(&target.chcs[target.cycles[0][0]])));
            const auto lockstepCheckPredicate = std::move(mk<NEQ>(loopGuard2, loopGuard1));
            query->body = std::move(mk<AND>(lockstepCheckPredicate, originalQuery));
            // TODO: according to paper, we need to return <inv, cex>
            bool lockstepCheck = learnInvariantsPr(product, true);
            query->body = originalQuery;
            return lockstepCheck;
        }

        bool checkEquivalence(Product_CHCs &product) {

            auto query = product.getQuery();
            const auto &originalQuery = query->body;
            const auto loopGuardS =
                std::move(source.getPrecondition(&source.chcs[source.cycles[0][0]]));
            const Expr negationLoopGuardS = std::move(mkNeg(loopGuardS));
            const Expr post = std::move(simplifyBool(mkNeg(conjoin(mapping, m_efac))));
            // we only add negation of loop guard of source because we have verified, 
            // using lockstep check, that loop guards of source and target are always equal
            query->body = std::move(mk<AND>(originalQuery, mk<AND>(negationLoopGuardS, post)));
            bool equivalenceCheck = learnInvariantsPr(product);
            query->body = originalQuery;
            return equivalenceCheck;
        }
    };

    void combinations(vector<int> &vars1, vector<int> &vars2, vector<pair<int, int>> c,
            vector<int> vars2Used, vector<vector<pair<int, int>>> &combs, int pos)
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
                c.push_back({vars1[pos], vars2[i]});
                combinations(vars1, vars2, c, vars2Used, combs, pos+1);
                c.pop_back();
                vars2Used.pop_back();
            }
        }
    }


    void combinationsOfVars(vector<int> &vars1, vector<int> &vars2,
            vector<vector<pair<int, int>>> &combs)
    {
        for (int i = 0; i < vars2.size(); i++)
        {
            vector<int> vars2Used{i};
            pair<int, int> v{vars1[0], vars2[i]};
            vector<pair<int, int>> c{v};
            combinations(vars1, vars2, c, vars2Used, combs, 1);
        }
    }

    void joinVars(vector<vector<pair<int, int>>> &vec1, vector<vector<pair<int, int>>> &vec2,
            vector<vector<pair<int, int>>> &combs)
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
                    vector<pair<int, int>> v;
                    concatenateVectors(v, it, it2);
                    combs.push_back(v);
                }
            }
        }
    }

    void createIterCombs(Extended_CHCs &ruleManager1, Extended_CHCs &ruleManager2,
            vector<vector<pair<int, int>>> &iterCombs)
    {

        vector<vector<pair<int, int>>> combsArray, combsInt, combsBool, combs1;
        combinationsOfVars(ruleManager1.varsArray, ruleManager2.varsArray, combsArray);
        combinationsOfVars(ruleManager1.varsInt, ruleManager2.varsInt, combsInt);
        combinationsOfVars(ruleManager1.varsBool, ruleManager2.varsBool, combsBool);

        joinVars(combsArray, combsInt, combs1);
        joinVars(combs1, combsBool, iterCombs);
    }

    void decomposeSource(Extended_CHCs& source, Extended_CHCs& target, Extended_CHCs& SDecomposed) {
        auto& efac = source.m_efac;
        const auto& TCycles = target.cycles;
        auto TCyclesSize = TCycles.size();
        const auto& TPrefixes = target.prefixes;

        int SPrefix = source.prefixes[0].back();
        int SCycle = source.cycles[0][0];
        const auto& SCycleCHC = source.chcs[SCycle];

        Expr SLoopRel = SCycleCHC.srcRelation;
        Expr SInductiveCHCRel_i_minus_1 = mk<TRUE>(efac);
        ExprVector SLoopVars(SCycleCHC.head->args_begin()+1, SCycleCHC.head->args_end());
        const ExprVector& SLoopSrcVars = SCycleCHC.srcVars;
        Expr negSGuard;
        ExprVector& invVars = source.invVars[SLoopRel];
        ExprVector& invVarsPrime = source.invVarsPrime[SLoopRel];
 
        for (int cycleNum = 0; cycleNum < TCyclesSize; cycleNum++) {
            const auto& cycleList = TCycles[cycleNum];
            auto& cycleCHC = target.chcs[cycleList.back()];

            auto SNonInductiveCHC = source.chcs[SPrefix];
            auto SInductiveCHC = source.chcs[SCycle];

            // if-condition is required according to the paper implementation
            if (cycleNum < TCyclesSize-1) {
            // a better way would be to use precondition and eliminateQuantifiers
                auto TGuard = std::move(target.getPrecondition(&cycleCHC));
                auto P_i = replaceAll(TGuard, cycleCHC.srcVars, SInductiveCHC.srcVars);
                SInductiveCHC.body = mk<AND>(SInductiveCHC.body, P_i);
            }

            Expr SInductiveCHCRel_i = mkTerm<string>(lexical_cast<string>(SLoopRel)+
                    "_"+to_string(cycleNum), efac);
            SDecomposed.invVars[SInductiveCHCRel_i] = invVars;
            SDecomposed.invVarsPrime[SInductiveCHCRel_i] = invVarsPrime;
            Expr SInductiveCHCHead_i = bind::fdecl(SInductiveCHCRel_i, SLoopVars);
            SDecomposed.decls.insert(SInductiveCHCHead_i);

            SNonInductiveCHC.srcRelation = SInductiveCHCRel_i_minus_1;
            if (!isOpX<TRUE>(SInductiveCHCRel_i_minus_1)) {
                SNonInductiveCHC.srcVars = SLoopSrcVars;
                SNonInductiveCHC.body = negSGuard;
                SNonInductiveCHC.isFact = false;
            }
            SNonInductiveCHC.dstRelation = SInductiveCHCRel_i;
            SInductiveCHC.srcRelation = SInductiveCHC.dstRelation = SInductiveCHCRel_i;
            SInductiveCHC.head = SInductiveCHCHead_i;
            SInductiveCHCRel_i_minus_1 = SInductiveCHCRel_i;

            SDecomposed.chcs.push_back(SNonInductiveCHC);
            SDecomposed.chcs.push_back(SInductiveCHC);

            auto SGuard = SDecomposed.getPrecondition(&SDecomposed.chcs.back());
            negSGuard = mkNeg(replaceAll(SGuard, invVars, invVarsPrime));
        }

        auto SQuery = source.getQuery();
        SQuery->srcRelation = SInductiveCHCRel_i_minus_1;
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

    void projection(Extended_CHCs& projRm, int i, Extended_CHCs &origRm, bool multipleProjections) {
        const auto cycle = origRm.chcs[origRm.cycles[i][0]];
        projRm.loopRel = cycle.srcRelation;
        if (!multipleProjections) {
            auto query = projRm.getQuery();
            query->body = mk<TRUE>(origRm.m_efac);
            return;
        }

        auto prefix = origRm.chcs[origRm.prefixes[i].back()];
        if (!prefix.isFact) {
            prefix.srcRelation = mk<TRUE>(origRm.m_efac);
            prefix.srcVars.clear();
            prefix.isFact = true;
        }
        projRm.chcs.push_back(std::move(prefix));

        projRm.chcs.push_back(std::move(cycle));

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
        hr.dstVars = ExprVector{};
        hr.body = mk<TRUE>(origRm.m_efac);

        for (int i = 0; i < projRm.chcs.size(); i++)
            projRm.outgs[projRm.chcs[i].srcRelation].push_back(i);

        projRm.wtoSort();
    }
        
    bool checkEquivalenceOfRMs(Extended_CHCs &source, Extended_CHCs &target,
            unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim,
            bool doArithm, bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
            bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
    {
        auto cycleSizeSrc = source.cycles.size();
        auto cycleSizeTgt = target.cycles.size();
        const auto& efac = source.m_efac;
        const auto& z3 = source.m_z3;

        assert(cycleSizeSrc == 1 && cycleSizeTgt >= 1);

        Extended_CHCs decomposedSource(source, cycleSizeTgt > 1);
        if (cycleSizeTgt > 1)
            decomposeSource(source, target, decomposedSource);

        auto numProjections = decomposedSource.cycles.size();
        assert(cycleSizeTgt == numProjections);
        assert(target.chcs.size() == decomposedSource.chcs.size());

        for (int i = 0; i < numProjections; i++) {
            // TODO: Use move semantics for better performance
            Extended_CHCs projectionSource(decomposedSource, numProjections > 1);
            projection(projectionSource, i, decomposedSource, numProjections > 1);

            Extended_CHCs projectionTarget(target, numProjections > 1);
            projection(projectionTarget, i, target, numProjections > 1);

            projectionSource.categorizeVars();
            projectionTarget.categorizeVars();

            vector<vector<pair<int, int>>> iterCombs;
            createIterCombs(projectionSource, projectionTarget, iterCombs);

            int j = 0;
            do {
                // cex loop
                auto comb = iterCombs.empty() ? vector<pair<int, int>>{} : iterCombs[j];
                EquivalenceInPaper equiv(projectionSource, projectionTarget, to, freqs, aggp,
                        dat, mut, doElim, doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp,
                        dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, debug, comb);

                bool equivalenceCheck = false;
                while (true) {
                    bool aligned = false;
                    bool refined = false;

                    // create product of source and target projections
                    Product_CHCs product(projectionSource, projectionTarget, "_pr_", debug-2);
                    product.createProduct();
                    equiv.createVariableMapping(product);

                    // fact sanity check
                    auto fact = product.getFact();
                    fact->body = mk<AND>(fact->body, equiv.getRelationalPrecondition(product));
                    bool factSanity = equiv.factSanityCheck(fact->body);

                    bool lockstepCheck = false;
                    if (factSanity) {
                        lockstepCheck = equiv.checkLockstepComposability(product);
                    }
                    if (!factSanity || !lockstepCheck) {
                        // align the programs
                        auto itersFound = equiv.findIterators();
                        if (itersFound) aligned = equiv.alignPrograms();
                        if (aligned) continue;
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
                j++;
            } while (j < iterCombs.size());
        }
        return true;
    }


    // check equivalence of programs
    inline void checkEquivalenceOfPrograms(const char *chcfileSrc, const char *chcfileDst,
            unsigned to, bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
            bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp, bool dAddDat,
            bool dStrenMbp, int dFwd, bool dRec, bool dGenerous, bool dSee, int debug)
    {
        ExprFactory m_efac;
        EZ3 z3(m_efac);

        Extended_CHCs ruleManagerSrc(m_efac, z3, "_v1_", debug-2);
        Extended_CHCs ruleManagerDst(m_efac, z3, "_v2_", debug-2);

        if (!ruleManagerSrc.parse(string(chcfileSrc), doElim, doArithm)) return;
        if (!ruleManagerDst.parse(string(chcfileDst), doElim, doArithm)) return;

        if (checkEquivalenceOfRMs(ruleManagerSrc, ruleManagerDst, to, freqs, aggp, dat, mut, doElim,
                    doArithm, doDisj, doProp, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp, dFwd, dRec, dGenerous, dSee, debug))
            outs() << "\nprograms are equivalent\n";
        else
            outs() << "\nprogram equivalence is unknown\n";
    };
}

#endif
