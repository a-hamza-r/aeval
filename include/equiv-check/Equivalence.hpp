#include "equiv-check/ContractsCHCs.hpp"


namespace ufo {

enum class EquivCheckProcedure {
    BASELINE,
    INCREMENTAL,
};

std::string sat_result(boost::tribool result) {
    return result ? "SAT" : !result ? "UNSAT" : "UNKNOWN";
}


class Equivalence {
private:
    ContractsCHCs m_contract1; // contract1
    ContractsCHCs m_contract2; // contract2
    std::vector<std::pair<int, int>> m_checkOrder;
    EquivCheckProcedure m_proc;
    std::vector<std::pair<Expr, Expr>> m_equivalences; // pairs of equivalent predicates (pred1, pred2) where pred1 is from contract1 and pred2 is from contract2

public:
    Equivalence(ContractsCHCs& contract1, ContractsCHCs& contract2,
                const std::vector<std::pair<std::string, std::string>>& equivalences,
                EquivCheckProcedure proc)
    : m_contract1(contract1), m_contract2(contract2), m_proc(proc) {
        // TODO: remove targetPredicatePairs, if possible; use funcs1 and funcs2 instead
        std::set<std::pair<int, int>> targetPredicatePairs;
        std::unordered_set<int> funcs1, funcs2;
        for (auto &pair : equivalences) {
            std::string pred1 = pair.first;
            std::string pred2 = pair.second;
            int pos1 = m_contract1.funcs_info.getFunctionIndex(pred1);
            int pos2 = m_contract2.funcs_info.getFunctionIndex(pred2);
            assert(pos1 != -1 && pos2 != -1);
            targetPredicatePairs.insert({pos1, pos2});
            funcs1.insert(pos1);
            funcs2.insert(pos2);
        }
        auto& callOrder1 = m_contract1.funcs_info.getCallingOrder();
        auto& callOrder2 = m_contract2.funcs_info.getCallingOrder();
        int ptr1 = callOrder1.size() - 1;
        int ptr2 = callOrder2.size() - 1;
        int numPairs = 0;
        while (ptr1 >= 0 && ptr2 >= 0) {
            int pos1 = callOrder1[ptr1];
            int pos2 = callOrder2[ptr2];
            if (targetPredicatePairs.find({pos1, pos2}) != targetPredicatePairs.end()) {
                // check if this has overhead
                m_checkOrder.insert(m_checkOrder.begin(), {pos1, pos2});
                ptr1--;
                ptr2--;
                numPairs++;
            }
            else if (funcs1.find(pos1) == funcs1.end()) {
                m_checkOrder.insert(m_checkOrder.begin(), {pos1, -1});
                ptr1--;
            }
            else {
                m_checkOrder.insert(m_checkOrder.begin(), {-1, pos2});
                ptr2--;
            }
        }
        if (numPairs != targetPredicatePairs.size() &&
            m_proc == EquivCheckProcedure::INCREMENTAL) {
            std::cout << "Cannot check equivalence using incremental approach\n";
            m_proc = EquivCheckProcedure::BASELINE;
        }
        print_info();
    }

    void print_info() {
        for (int i = 0; i < m_checkOrder.size(); i++) {
            int pos1 = m_checkOrder[i].first;
            int pos2 = m_checkOrder[i].second;
            if (pos1 != -1 && pos2 != -1) {
                std::cout << "Checking equivalence for " <<
                    m_contract1.funcs_info.getFunctions()[pos1].name << " and " <<
                    m_contract2.funcs_info.getFunctions()[pos2].name << "." << std::endl;
            }
            else if (pos1 == -1) {
                std::cout << "Only inlining " <<
                    m_contract2.funcs_info.getFunctions()[pos2].name << "." << std::endl;
            }
            else {
                std::cout << "Only inlining " <<
                    m_contract1.funcs_info.getFunctions()[pos1].name << "." << std::endl;
            }
        }
    }

    void get_equivalence_result() {
        switch (m_proc) {
            case EquivCheckProcedure::BASELINE: {
                // Inline everything
                m_contract1.inlining();
                m_contract2.inlining();

                functionsInfo fInfo1 = m_contract1.funcs_info;
                functionsInfo fInfo2 = m_contract2.funcs_info;
                function& f1 = fInfo1.getFunctions()[fInfo1.getCallingOrder().back()];
                function& f2 = fInfo2.getFunctions()[fInfo2.getCallingOrder().back()];
                std::cout << "Checking equivalence for " << f1.name << " and " << f2.name << "." << std::endl;
                assert(f1.args.size() == f2.args.size());
                assert(f1.outputs.size() == f2.outputs.size());
                int inputs_sz = f1.args.size();
                int outputs_sz = f1.outputs.size();
                auto& z3 = m_contract1.m_z3;
                auto& efac = m_contract1.m_efac;
                SMTUtils u(efac, z3, z3.getAdtAccessors(), 100000);

                // Make two funds variables equivalent
                auto finding_funds = [&](Expr f) {
                    ExprSet vars;
                    filter(f, bind::IsConst(), std::inserter(vars, vars.begin()));
                    for (auto &v : vars) {
                        std::string vname = lexical_cast<std::string>(v);
                        if (vname.find("funds") != std::string::npos) {
                            return v;
                        }
                    }
                    return mkMPZ(0, efac);
                };
                Expr funds1 = finding_funds(f1.definition);
                Expr funds2 = finding_funds(f2.definition);
                Expr funds_eq = mk<EQ>(funds1, funds2);

                ExprVector eqArgs = {funds_eq}, eqOuts;
                for (int i = 0; i < inputs_sz; i++) {
                    eqArgs.push_back(mk<EQ>(f1.args[i], f2.args[i]));
                }
                for (int i = 0; i < outputs_sz; i++) {
                    eqOuts.push_back(mk<EQ>(f1.outputs[i], f2.outputs[i]));
                }
                Expr equalArgs = conjoin(eqArgs, efac);
                Expr equalOuts = conjoin(eqOuts, efac);
                Expr prec_and_bodies = mk<AND>(equalArgs, mk<AND>(f1.definition, f2.definition));
                Expr equiv = mk<IMPL>(prec_and_bodies, equalOuts);
                auto sys_sat = u.isSat(equiv);
                if (!bool(sys_sat)) {
                    std::cout << "System is unsatisfiable." << std::endl;
                    return;
                }
                Expr neg = mk<NEG>(equiv);
                auto neg_sat = u.isSat(neg);
                ExprSet exprs;
                getConj(neg, exprs);
                u.dumpToFile(exprs);
                std::cout << "check on negation of equiv fla: " << sat_result(neg_sat) << std::endl;
                if (!bool(neg_sat)) {
                    std::cout << "Programs are equivalent." << std::endl;
                } else {
                    std::cout << "Programs are not equivalent." << std::endl;
                }
                break;
            }
            case EquivCheckProcedure::INCREMENTAL: {
                std::cout << "WARNING: Incremental equivalence check is not implemented yet." << std::endl;
                auto& funcs_info1 = m_contract1.funcs_info;
                auto& funcs_info2 = m_contract2.funcs_info;
                for (auto& pair : m_checkOrder) {
                    int pos1 = pair.first;
                    int pos2 = pair.second;

                    EquivalenceCands equivCands;
                    if (pos1 != -1 && pos2 != -1) {
                        function& f1 = funcs_info1.getFunctions()[pos1];
                        function& f2 = funcs_info2.getFunctions()[pos2];
                        equivCands.populate(f1.name, f2.name,
                                {f1.fpred_expr, f1.fpred_trailing_pred},
                                {f2.fpred_expr, f2.fpred_trailing_pred});
                        std::string equivFilePrefix = "sygus_files/" + f1.name + "_" + f2.name + "_equiv";
                        {
                            std::ofstream eq1(equivFilePrefix + "_1.smt2", std::ios_base::trunc);
                            std::ofstream eq2(equivFilePrefix + "_2.smt2", std::ios_base::trunc);
                        }
                    }
                    if (pos1 != -1) {
                        function& f1 = funcs_info1.getFunctions()[pos1];
                        // m_contract1.inliningSingleFunction(f1);
                        std::cout << "Generating summary for " << f1.name << "...\n\n";
                        bool retry = false;
                        do {
                            retry = m_contract1.findSummary(f1.fpred_expr, f1, equivCands, false);
                            if (m_contract1.summaryGen.isSummaryAvailable(f1.fpred_expr) &&
                                !retry) {
                                break;
                            }
                        } while (retry);
                        // m_contract1.printFunctionInfo(f1);
                    }
                    if (pos2 != -1) {
                        function& f2 = funcs_info2.getFunctions()[pos2];
                        // m_contract2.inliningSingleFunction(f2);
                        std::cout << "Generating summary for " << f2.name << "...\n\n";
                        bool retry = false;
                        do {
                            retry = m_contract2.findSummary(f2.fpred_expr, f2, equivCands, true);
                            if (m_contract2.summaryGen.isSummaryAvailable(f2.fpred_expr) &&
                                !retry) {
                                break;
                            }
                        } while (retry);
                        // m_contract2.printFunctionInfo(f2);
                    }
                    if (pos1 != -1 && pos2 != -1) {
                        function& f1 = funcs_info1.getFunctions()[pos1];
                        function& f2 = funcs_info2.getFunctions()[pos2];

                        auto equivalenceCheck = [&](std::string fileName, Expr rel1, Expr rel2) {
                            std::string pred1Name = lexical_cast<std::string>(rel1);
                            std::string pred2Name = lexical_cast<std::string>(rel2);
                            std::cout << "Checking equivalence for " <<
                                pred1Name << " and " << pred2Name << "." << std::endl;

                            // partition inputs and outputs for the two summaries
                            ExprVector args1, args2, outs1, outs2;
                            inlinedDefinition d1 = m_contract1.summaryGen.getSummary(rel1);
                            m_contract1.partitionInputsOutputs(d1.dsts, args1, outs1);
                            inlinedDefinition d2 = m_contract2.summaryGen.getSummary(rel2);
                            m_contract2.partitionInputsOutputs(d2.dsts, args2, outs2);

                            assert(args1.size() == args2.size());
                            assert(outs1.size() == outs2.size());
                            int inputs_sz = args1.size();
                            int outputs_sz = outs1.size();

                            std::ofstream equiv_file(fileName, std::ios_base::app);
                            equiv_file << "(assert (and\n";
                            for (int i = 0; i < inputs_sz; i++) {
                                equiv_file << " (= ";
                                m_contract1.u.print(args1[i], equiv_file);
                                equiv_file << " ";
                                m_contract2.u.print(args2[i], equiv_file);
                                equiv_file << ")\n";
                            }
                            equiv_file << "))\n";
                            equiv_file << "(assert (not (and\n";
                            for (int i = 0; i < outputs_sz; i++) {
                                equiv_file << " (= ";
                                m_contract1.u.print(outs1[i], equiv_file);
                                equiv_file << " ";
                                m_contract2.u.print(outs2[i], equiv_file);
                                equiv_file << ")\n";
                            }
                            equiv_file << ")))\n";
                            equiv_file << "(check-sat)\n";
                            equiv_file.close();
                            Expr eq_fla = z3_from_smtlib_file(m_contract1.m_z3, fileName.c_str());
                            auto sat = m_contract1.u.isSat(eq_fla);
                            if (!bool(sat)) {
                                std::cout << pred1Name << " and " << pred2Name <<
                                    " are equivalent." << std::endl;
                                m_equivalences.push_back({rel1, rel2});
                                m_contract1.checkedEquivalent.insert(rel1);
                                m_contract2.checkedEquivalent.insert(rel2);
                                return true;
                            } else {
                                std::cout << pred1Name << " and " << pred2Name <<
                                    " are not equivalent." << std::endl;
                                return false;
                            }
                        };

                        std::string equivFilePrefix = "sygus_files/" + f1.name + "_" + f2.name + "_equiv";
                        // check for trailing preds
                        bool equiv = equivalenceCheck(equivFilePrefix + "_2.smt2",
                                         equivCands.func1Preds[1], equivCands.func2Preds[1]);
                        // check for fpreds
                        equiv &= equivalenceCheck(equivFilePrefix + "_1.smt2",
                                         equivCands.func1Preds[0], equivCands.func2Preds[0]);
                        
                        if (!equiv) {
                            std::cout << "Programs are not equivalent." << std::endl;
                            return;
                        } else {
                            std::cout << f1.name << " and " << f2.name << " are equivalent.\n\n";
                        }
                    }
                }
            }
        }
    }
};

inline void check_equivalence(char* contract1File, char* contract2File,
                              const std::vector<std::pair<std::string, std::string>>& equivalences,
                              std::string contract1Name, std::string contract2Name,
                              std::vector<std::string>& predicatesC1,
                              std::vector<std::string>& predicatesC2,
                              unsigned maxAttempts, unsigned to, bool freqs, bool aggp,
                              bool enableDataLearning, bool doElim,
                              bool doDisj, int doProp, bool dAllMbp, bool dAddProp, bool dAddDat,
                              bool dStrenMbp, bool toSkip, int invMode, int lookahead,
                              bool lb, bool lmax, bool prio, int debug) {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    /*
    Expr fla = z3_from_smtlib_file(z3, "test2.smt2");
    SMTUtils u(m_efac, z3, z3.getAdtAccessors(), to);
    u.print(fla);
    */

    ContractsCHCs ruleManagerC1(m_efac, z3, "_v1_", predicatesC1);
    ruleManagerC1.parse(contract1File, contract1Name);
    //ruleManagerC1.print();


    ContractsCHCs ruleManagerC2(m_efac, z3, "_v2_", predicatesC2);
    ruleManagerC2.parse(contract2File, contract2Name);
    //ruleManagerC2.print();

    EquivCheckProcedure proc = EquivCheckProcedure::INCREMENTAL;
    // EquivCheckProcedure proc = EquivCheckProcedure::BASELINE;
    auto equiv = Equivalence(ruleManagerC1, ruleManagerC2, equivalences, proc);
    equiv.get_equivalence_result();
}

}
