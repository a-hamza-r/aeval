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
    std::vector<std::pair<int, int>> m_targetPredicatePairs;

public:
    Equivalence(ContractsCHCs& contract1, ContractsCHCs& contract2,
                const std::vector<std::pair<std::string, std::string>>& equivalences)
    : m_contract1(contract1), m_contract2(contract2) {
        m_targetPredicatePairs.reserve(equivalences.size());
        for (auto &pair : equivalences) {
            std::string pred1 = pair.first;
            std::string pred2 = pair.second;
            int pos1 = m_contract1.funcsInfo.getFunctionIndex(pred1);
            int pos2 = m_contract2.funcsInfo.getFunctionIndex(pred2);
            assert(pos1 != -1 && pos2 != -1);
            m_targetPredicatePairs.emplace_back(pos1, pos2);
        }
    }

    void print_info() {
        for (int i = 0; i < m_targetPredicatePairs.size(); i++) {
            int pos1 = m_targetPredicatePairs[i].first;
            int pos2 = m_targetPredicatePairs[i].second;
            std::cout << "Checking equivalence for " <<
                m_contract1.funcsInfo.getFunctions()[pos1].getName() << " and " <<
                m_contract2.funcsInfo.getFunctions()[pos2].getName() << "." << std::endl;
        }
    }

    void get_equivalence_result(EquivCheckProcedure proc) {
        switch (proc) {
            case EquivCheckProcedure::BASELINE: {
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
                    return Expr();
                };
                Expr funds1 = finding_funds(f1.definition);
                Expr funds2 = finding_funds(f2.definition);
                Expr funds_eq = funds1 != Expr() && funds2 != Expr() ?
                    mk<EQ>(funds1, funds2) : mk<TRUE>(efac);

                ExprVector eqArgs = {funds_eq}, eqOuts;
                // AH: Hacky way of constructing precondition and postcondition
                for (int i = 0; i < inputs_sz; i++) {
                    /*
                    ExprVector accs1, accs2;
                    u.unfold(accs1, f1.args[i]);
                    u.unfold(accs2, f2.args[i]);
                    size_t sz = accs1.size();
                    for (size_t j = 0; j < sz; j++) {
                        eqArgs.push_back(mk<EQ>(accs1[j], accs2[j]));
                    }
                    */
                    // eqArgs.push_back(mk<EQ>(f1.args[i], f2.args[i]));
                }
                for (int i = 0; i < outputs_sz; i++) {
                    /*
                    ExprVector accs1, accs2;
                    u.unfold(accs1, f1.outputs[i]);
                    u.unfold(accs2, f2.outputs[i]);
                    size_t sz = accs1.size();
                    for (size_t j = 0; j < sz; j++) {
                        eqOuts.push_back(mk<EQ>(accs1[j], accs2[j]));
                    }
                    */
                    eqOuts.push_back(mk<EQ>(f1.outputs[i], f2.outputs[i]));
                }
                Expr equalArgs = conjoin(eqArgs, efac);
                Expr equalOuts = conjoin(eqOuts, efac);
                Expr prec_and_bodies = mk<AND>(equalArgs, mk<AND>(f1.definition, f2.definition));
                Expr equiv = mk<IMPL>(prec_and_bodies, equalOuts);
                auto sys_sat = u.isSat(equiv);
                std::cout << "check on equiv fla: " << sat_result(u.isSat(equiv)) << std::endl;
                if (!bool(sys_sat)) {
                    std::cout << "System is unsatisfiable." << std::endl;
                    return;
                }
                Expr neg = mk<NEG>(equiv);
                ExprSet cnjs;
                getConj(neg, cnjs);
                u.dumpToFile(cnjs);
                auto neg_sat = u.isSat(neg);
                std::cout << "check on negation of equiv fla: " << sat_result(neg_sat) << std::endl;
                if (!bool(neg_sat)) {
                    std::cout << "Programs are equivalent." << std::endl;
                } else {
                    std::cout << "Programs are not equivalent." << std::endl;
                }
                break;
            }
            case EquivCheckProcedure::INCREMENTAL: {
                std::cout << "Incremental equivalence check is not implemented yet." << std::endl;
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

    ruleManagerC1.inlining();
    ruleManagerC2.inlining();

    auto equiv = Equivalence(ruleManagerC1, ruleManagerC2, equivalences);
    equiv.get_equivalence_result(EquivCheckProcedure::BASELINE);
}

}
