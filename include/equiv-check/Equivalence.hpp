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
            int pos1 = m_contract1.funcsInfo.getFunctionIndex(pred1);
            int pos2 = m_contract2.funcsInfo.getFunctionIndex(pred2);
            assert(pos1 != -1 && pos2 != -1);
            targetPredicatePairs.insert({pos1, pos2});
            funcs1.insert(pos1);
            funcs2.insert(pos2);
        }
        auto& callOrder1 = m_contract1.funcsInfo.getCallingOrder();
        auto& callOrder2 = m_contract2.funcsInfo.getCallingOrder();
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
                    m_contract1.funcsInfo.getFunctions()[pos1].getName() << " and " <<
                    m_contract2.funcsInfo.getFunctions()[pos2].getName() << "." << std::endl;
            }
            else if (pos1 == -1) {
                std::cout << "Only inlining " <<
                    m_contract2.funcsInfo.getFunctions()[pos2].getName() << "." << std::endl;
            }
            else {
                std::cout << "Only inlining " <<
                    m_contract1.funcsInfo.getFunctions()[pos1].getName() << "." << std::endl;
            }
        }
    }

    void get_equivalence_result() {
        switch (m_proc) {
            case EquivCheckProcedure::BASELINE: {
                // Inline everything
                m_contract1.inlining();
                m_contract2.inlining();

                functionsInfo fInfo1 = m_contract1.funcsInfo;
                functionsInfo fInfo2 = m_contract2.funcsInfo;
                function& f1 = fInfo1.getFunctions()[fInfo1.getCallingOrder().back()];
                function& f2 = fInfo2.getFunctions()[fInfo2.getCallingOrder().back()];
                std::cout << "Checking equivalence for " << f1.getName() << " and " << f2.getName() << "." << std::endl;
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
                auto& funcsInfo1 = m_contract1.funcsInfo;
                auto& funcsInfo2 = m_contract2.funcsInfo;
                for (auto& pair : m_checkOrder) {
                    int pos1 = pair.first;
                    int pos2 = pair.second;
                    if (pos1 != -1) {
                        function& f1 = funcsInfo1.getFunctions()[pos1];
                        m_contract1.printFunctionInfo(f1);
                        m_contract1.inliningSingleFunction(f1);
                    }
                    if (pos2 != -1) {
                        function& f2 = funcsInfo2.getFunctions()[pos2];
                        m_contract2.printFunctionInfo(f2);
                        m_contract2.inliningSingleFunction(f2);
                    }
                }
                break;
            }
        }
    }
};

inline void check_equivalence(char* contract1, char* contract2,
                              const std::vector<std::pair<std::string, std::string>>& equivalences,
                              std::vector<std::string>& predicatesC1,
                              std::vector<std::string>& predicatesC2,
                              unsigned maxAttempts, unsigned to, bool freqs, bool aggp,
                              bool enableDataLearning, bool doElim,
                              bool doDisj, int doProp, bool dAllMbp, bool dAddProp, bool dAddDat,
                              bool dStrenMbp, bool toSkip, int invMode, int lookahead,
                              bool lb, bool lmax, bool prio, int debug) {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    ContractsCHCs ruleManagerC1(m_efac, z3, "_v1_", predicatesC1);
    ruleManagerC1.parse(contract1);
    //ruleManagerC1.print();


    ContractsCHCs ruleManagerC2(m_efac, z3, "_v2_", predicatesC2);
    ruleManagerC2.parse(contract2);
    //ruleManagerC2.print();

    EquivCheckProcedure proc = EquivCheckProcedure::INCREMENTAL;
    // EquivCheckProcedure proc = EquivCheckProcedure::BASELINE;
    auto equiv = Equivalence(ruleManagerC1, ruleManagerC2, equivalences, proc);
    equiv.get_equivalence_result();
}

}
