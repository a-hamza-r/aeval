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

    Expr myAbduce(Expr goal, Expr assmp, ExprVector varsNotInc=ExprVector())
    {
        Expr quantified = keepQuantifiers(mkNeg(mk<IMPL>(assmp, goal)), varsNotInc);
        Expr tmp = mkNeg(quantified);

        return tmp;
    }


    class Extended_CHCs : public CHCs
    {
        public:
            ExprVector factSrcVars;

            int iter;
            Expr loopRel;
            Expr loopGuard;
            bool iterGrows;
            Expr numOfIters;
            vector<int> varsInt;
            vector<int> varsBool;
            vector<int> varsArray;
            ExprVector postLoopSrcVars;
            ExprVector queryDstVars;

            Extended_CHCs(ExprFactory &efac, EZ3 &z3, string n, int d = false) : CHCs(efac, z3, n, d), iter(-1) {};
            Extended_CHCs(const Extended_CHCs &old_chc, bool shallowCopy=false) 
                : CHCs(old_chc, shallowCopy), iter(-1) {};


            Expr getDecl(Expr relation) const
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
    
            void categorizeVars() {
                for (int i = 0; i < invVars[loopRel].size(); i++) {
                    Expr var = invVars[loopRel][i];
                    if (bind::isIntConst(var)) varsInt.push_back(i);
                    else if (bind::isBoolConst(var)) varsBool.push_back(i);
                    else if (isOpX<ARRAY_TY>(bind::typeOf(var))) varsArray.push_back(i);
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

            HornRuleExt *getFact()
            {
                for (auto &chc : chcs)
                {
                    if (chc.isFact) return &chc;
                }
                return NULL;
            }

            int removePreLoop()
            {
                HornRuleExt *f;
                int factLoc;
                for (auto chc = chcs.begin(); chc != chcs.end(); chc++)
                {
                    if (chc->isFact) 
                    {
                        f = &(*chc);
                        factLoc = chc-chcs.begin();
                    }
                }

                for (auto chc = chcs.begin(); chc != chcs.end(); chc++)
                {
                    if (!chc->isFact && !chc->isInductive && !chc->isQuery && chc->dstRelation == loopRel)
                    {
                        HornRuleExt &pl = *chc;

                        Expr body = replaceAll(f->body, f->dstVars, pl.srcVars);
                        pl.body = mk<AND>(pl.body, body);
                        if (emptyIntersect(pl.body, pl.srcVars)) factSrcVars = pl.dstVars;
                        else factSrcVars = pl.srcVars;
                        pl.srcVars.clear();
                        removeDecl(pl.srcRelation);
                        pl.srcRelation = f->srcRelation;
                        pl.isFact = true;

                        return factLoc;
                    }
                }
                factSrcVars = f->dstVars;
                return -1;
            }

            int removePostLoop()
            {
                HornRuleExt *q;
                int queryLoc;
                for (auto chc = chcs.begin(); chc != chcs.end(); chc++)
                {
                    if (chc->isQuery) 
                    {
                        q = &(*chc);
                        queryLoc = chc-chcs.begin();
                    }
                }

                for (auto chc = chcs.begin(); chc != chcs.end(); chc++)
                {
                    if (!chc->isFact && !chc->isInductive && !chc->isQuery && chc->srcRelation == loopRel)
                    {
                        HornRuleExt &pl = *chc;

                        //Expr body = replaceAll(q->body, q->srcVars, pl.dstVars);
                        //pl.body = mk<AND>(pl.body, body);
                        if (emptyIntersect(pl.body, pl.dstVars)) queryDstVars = pl.srcVars;
                        else queryDstVars = pl.dstVars;
                        pl.dstVars.clear();
                        removeDecl(pl.dstRelation);
                        pl.dstRelation = q->dstRelation;
                        pl.isQuery = true;

                        return queryLoc;
                    }
                }
                queryDstVars = q->srcVars;
                return -1;
            }

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
                //concatenateVectors(vars, factSrcVars, v);

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

            Expr numIterations(Expr init, Expr transition, Expr final, Expr add)
            {
                if (!(init && transition && final)) return mkMPZ(-1, m_efac);
                Expr numer = mk<MINUS>(final, init);

                if (add) numer = mk<PLUS>(numer, add);
                Expr divisible = mk<EQ>(mk<MOD>(numer, transition), mkMPZ(0, m_efac));

                Expr numIters = mk<PLUS>(mk<IDIV>(numer, transition), mk<ITE>(divisible, mkMPZ(0, m_efac), mkMPZ(1, m_efac)));
                return simplifyArithm(numIters);
            }

            Expr findInitialValue(int i, Expr init)
            {
                Expr equalities = nullptr;
                Expr iter = invVars[loopRel][i];

                findExpr<EQ>(iter, init, equalities, true);
                if (equalities)
                {
                    Expr initVal = nullptr;
                    ExprSet equalitiesSet;
                    getConj(equalities, equalitiesSet);
                    for (const auto &it : equalitiesSet)
                    {
                        Expr normalized = ineqSimplifier(iter, simplifyArithm(it));
                        if (isOpX<EQ>(normalized) && normalized->left() == iter)
                        {
                            // if multiple equalities are found, just return; support more
                            if (initVal) return nullptr;
                            else initVal = normalized;
                        }
                    }
                    if (initVal)
                    {
                        Expr normalized = ineqSimplifier(iter, simplifyArithm(initVal));
                        initVal = normalized->right();
                        // assigns non-primed variables
                        initVal = replaceAll(initVal, invVarsPrime[loopRel], invVars[loopRel]);
                        return initVal;
                    }
                }
                return nullptr;
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

            void rulesOfPredicate(Expr decl, vector<HornRuleExt*> &rulesOfP)
            {
                for (auto it = chcs.begin(); it != chcs.end(); it++)
                    if (decl == it->dstRelation)
                        rulesOfP.push_back(&*it);
            }

            void mergeIterationsFact(HornRuleExt &fact, int num, ExprVector &ssa, BndExpl &bnd, 
                    Expr &prefixBody, bool actualAlign)
            {
                if (num <= 0) return;

                ssa[num] = replaceAll(ssa[num], bnd.bindVars[num], fact.dstVars);	
                prefixBody = conjoin(ssa, m_efac);

                // in case factSrcVars are empty, we needed the factSrcVars as bnd.bindVars[0]
                // in case factSrcVars are not empty, we just replaced the whole fact with some formula, 
                // initial variables are then bnd.bindVars[0]
                if (actualAlign)
                {
                    for (auto i = 1; i < bnd.bindVars.size()-1; i++)
                    {
                        fact.locVars.reserve(fact.locVars.size()+bnd.bindVars[i].size());
                        fact.locVars.insert(fact.locVars.end(), bnd.bindVars[i].begin(), bnd.bindVars[i].end());
                    }
                    factSrcVars = bnd.bindVars[0];
                }
            }

            void mergeIterationsLoop(HornRuleExt &loop, int num, ExprVector &ssa, BndExpl &bnd)
            {
                if (num <= 0) return;

                ExprSet locVars;
                filter(conjoin(ssa, m_efac), IsConst(), inserter(locVars, locVars.begin()));

                loop.body = replaceAll(loop.body, loop.dstVars, bnd.bindVars[0]);
                ssa[num-1] = replaceAll(ssa[num-1], bnd.bindVars[num], loop.dstVars);

                loop.body = mk<AND>(loop.body, conjoin(ssa, m_efac));
                loop.locVars.insert(loop.locVars.end(), locVars.begin(), locVars.end());
            }

            void mergeIterationsQuery(int num, ExprVector &ssa, BndExpl &bnd)
            {
                if (num <= 0) return;

                auto query = getQuery();

                //query->body = replaceAll(query->body, query->srcVars, bnd.bindVars[bnd.bindVars.size()-1]);
                queryDstVars = bnd.bindVars[bnd.bindVars.size()-1];
                ssa[0] = replaceAll(ssa[0], bnd.bindVars[0], query->srcVars);
                //query->body = mk<AND>(query->body, conjoin(ssa, m_efac));
                query->body = conjoin(ssa, m_efac);
                for (auto i = 1; i < bnd.bindVars.size()-2; i++)
                {
                    query->locVars.reserve(query->locVars.size()+bnd.bindVars[i].size());
                    query->locVars.insert(query->locVars.end(), bnd.bindVars[i].begin(), bnd.bindVars[i].end());
                }
            }

            void createAlignment(int unrollTrans, int unrollFact, int unrollQuery, BndExpl &bnd, 
                    Expr &prefixBody, bool actualAlign=true)
            {
                if (actualAlign)
                {
                    cout << "Iterations in the loop: " << unrollTrans << "\n";
                    cout << "Iterations added to fact: " << unrollFact << "\n";
                    cout << "Iterations added to query: " << unrollQuery << "\n";
                }

                vector<int>& cycle = cycles[0];
                HornRuleExt& rule = chcs[cycle[0]];
                auto & prefix = prefixes[0];
                HornRuleExt &prefixRule = chcs[prefix[0]];

                vector<int> traceFactUnroll = {prefix[0]}, traceQueryUnroll = {prefix[0]}, traceLoopUnroll = {prefix[0]};
                ExprVector ssa, ssa1, ssa2;


                // ************* FACT UNROLLING ***************

                // merge iterations to the fact, given the unrollFact value
                for (int j = 0; j < unrollFact; j++)
                    for (int m = 0; m < cycle.size(); m++)
                        traceFactUnroll.push_back(cycle[m]);

                bnd.getSSA(traceFactUnroll, ssa, varname);

                mergeIterationsFact(prefixRule, unrollFact, ssa, bnd, prefixBody, actualAlign);


                // ************* QUERY UNROLLING ***************

                // merge iterations to the query, given the unrollquery value
                for (int j = 0; j < unrollQuery; j++)
                    for (int m = 0; m < cycle.size(); m++)
                        traceQueryUnroll.push_back(cycle[m]);

                bnd.getSSA(traceQueryUnroll, ssa1, varname);
                ssa1.erase(ssa1.begin());

                mergeIterationsQuery(unrollQuery, ssa1, bnd);


                // ************* LOOP UNROLLING ***************

                // unroll the inductive rule unrollTrans times
                for (int j = 0; j < unrollTrans-1; j++)
                    for (int m = 0; m < cycle.size(); m++)
                        traceLoopUnroll.push_back(cycle[m]);

                bnd.getSSA(traceLoopUnroll, ssa2, varname);
                ssa2.erase(ssa2.begin());

                mergeIterationsLoop(rule, unrollTrans-1, ssa2, bnd);
            }

            Expr findTransitionValue(int i, Expr body)
            {
                Expr a = invVars[loopRel][i];
                Expr b = invVarsPrime[loopRel][i];

                Expr allTransitions = nullptr;
                findExpr<EQ>(b, body, allTransitions, true);
                if (!allTransitions) return NULL;

                bool multipleTransVal = false;
                Expr transition = nullptr;
                ExprSet allExprsSet;
                getConjAndDisj(allTransitions, allExprsSet);
                for (const auto &it : allExprsSet)
                {
                    Expr normalized = ineqSimplifier(b, simplifyArithm(it));
                    if (contains(normalized, a) && isOpX<EQ>(normalized)
                            && normalized->left() == b)
                    {
                        if (transition) multipleTransVal = true;
                        else transition = normalized;
                    }
                }

                // Cases when transition can't be found:
                    // multiple transition rels, 
                    // no transition rel, 
                    // contains an ITE
                if (multipleTransVal || !transition || transition->right()->arity() <= 1
                        || containsOp<ITE>(transition))
                    return nullptr;

                Expr rightOfTransition = transition->right();

                Expr transitionVal = nullptr;
                // assuming no local vars
                if (rightOfTransition->arg(0) == a)
                    transitionVal = rightOfTransition->arg(1);
                else
                    transitionVal = rightOfTransition->arg(0);

                // check if delta value is constant; Eq. 10, section 4 in paper
                Expr replacedTrans
                    = replaceAll(transitionVal, invVars[loopRel], invVarsPrime[loopRel]);
                return u.implies(body, mk<EQ>(transitionVal, replacedTrans))
                    ? transitionVal : nullptr;
            }

            Expr findFinalValue(int i, Expr body, Expr& add, bool iterIncreases)
            {
                Expr iter = invVars[loopRel][i];
                auto &cycle = chcs[cycles[0][0]];
                auto precondition = std::move(getPrecondition(&cycle));

                if (!precondition || isOpX<AND>(precondition) || isOpX<OR>(precondition)) {
                    // TODO: support more
                    return nullptr;
                }

                precondition = ineqSimplifier(iter, precondition);
                if (!loopGuard) loopGuard = precondition;

                if (containsOp<LEQ>(precondition)) add = mkMPZ(1, m_efac);
                else if (containsOp<GEQ>(precondition)) add = mkMPZ(-1, m_efac);
                else if (!containsOp<LT>(precondition) && !containsOp<GT>(precondition))
                    return nullptr;

                Expr limitVal = precondition->arg(1);
                
                // check if limit value is constant; Eq. 8, section 4
                Expr replacedLimit = replaceAll(limitVal, invVars[loopRel], invVarsPrime[loopRel]);
                bool constLimitValCheck = bool(u.implies(body, mk<EQ>(limitVal, replacedLimit)));

                // check the case that iter does not exceed limit value during transition;
                // Eq. 7, section 4
                bool loopEndCheck = precondition && !u.isSat(mk<AND>(mkNeg(precondition), body));

                if (!constLimitValCheck || !loopEndCheck) return nullptr;
                return limitVal;
            }

            bool findIterators()
            {
                BndExpl bnd(*this, debug);
                const HornRuleExt& rule = chcs[cycles[0][0]];

                Expr pref = bnd.compactPrefix(0);

                for (auto& i : varsInt)
                {
                    Expr a = invVars[loopRel][i];
                    Expr b = invVarsPrime[loopRel][i];

                    bool isAnIter = false;
                    bool iterDecreases = bool(u.implies(rule.body, mk<GT>(a, b)));
                    bool iterIncreases = bool(u.implies(rule.body, mk<LT>(a, b)));

                    if (iterIncreases || iterDecreases)
                    {
                        Expr add;
                        Expr initVal = findInitialValue(i, pref);
                        Expr transitionVal = findTransitionValue(i, rule.body);
                        Expr limitVal = findFinalValue(i, rule.body, add, iterIncreases);

                        isAnIter = initVal && transitionVal && limitVal;
                        if (isAnIter)
                        {
                            // TODO: allow multiple iters
                            iter = i;
                            iterGrows = iterIncreases;
                            numOfIters = numIterations(initVal, transitionVal, limitVal, add);
                            return true;
                        }
                    }
                }
                return false;
            }

            void preprocessing()
            {
                int factRemove = removePreLoop();
                int queryRemove = removePostLoop();

                for (auto it = chcs.begin(); it != chcs.end(); )
                {
                    if (factRemove == it-chcs.begin() || queryRemove == it-chcs.begin()) 
                    {
                        it = chcs.erase(it);
                        factRemove--; queryRemove--;
                    }
                    else it++;
                }

                // we do it because we have already populated these containers with information with initial chcs,
                // which have now been updated by removing pre and post loop
                // either do this, or never populate with initial state of the chcs
                prefixes.clear();
                cycles.clear();
                outgs.clear();
                wtoCHCs.clear();

                for (int i = 0; i < chcs.size(); i++)
                    outgs[chcs[i].srcRelation].push_back(i);

                wtoSort();
            }
    };
}

#endif
