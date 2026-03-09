#include "deep/HornNonlin.hpp"
#include <regex>

namespace ufo {


struct function {
    // Actual function signature/definition
    ExprVector args;
    ExprVector outputs;
    Expr definition;

    // Below variables used at the level of CHCs to represent the functions
    // Each predicate represents a function e.g., a predicate like "summary_foo" represents a
    // function "foo", we call these function predicates (or fpreds)
    std::string fpred_name;
    int fpred_sink; // CHC containing the function predicate as head (sink)
    int fpred_source; // CHC that serves as source for the function predicate (fact CHC)
    Expr fpred_expr; // the function predicate
    Expr fpred_trailing_pred; // predicate that is used to define the control-flow of the function
    std::vector<int> chc_nums; // CHC numbers that are used to define the function

    std::string name;

    function(std::string _fpred_name) : fpred_name(_fpred_name) {
        // best effort to retrieve the actual function name from the function predicate
        std::regex pattern(R"(summary_+\d+_+function_(.*)_+\d+_+\d+_+\d+)");
        std::smatch match;

        if (std::regex_search(fpred_name, match, pattern)) {
            std::string funcname = match[1].str();

            // Trim leading and trailing underscores
            size_t start = funcname.find_first_not_of('_');
            size_t end = funcname.find_last_not_of('_');

            name = (start != std::string::npos) ? funcname.substr(start, end - start + 1) : fpred_name;
        }
    }

    void print() const {
        std::cout << "Function: " << name << "\n";
        std::cout << "Arguments: ";
        for (auto &arg : args) {
            std::cout << arg << " ";
        }
        std::cout << "\n";
        std::cout << "Outputs: ";
        for (auto &out : outputs) {
            std::cout << out << " ";
        }
        std::cout << "\n";
        std::cout << "Definition: " << definition << "\n";
        std::cout << "\n";
    }
};


// A class to represent information about functions and function calls
class functionsInfo {
    const std::vector<std::string>& m_fpreds_names;
    // TODO: currently not used; either remove or use it
    std::set<int> m_function_relevant_chcs; // CHC numbers that are relevant for the functions
    std::vector<function> m_functions; // a list of functions in the contract

    // a map from caller to callees
    std::unordered_map<int, std::vector<int>> m_caller_to_callee;
    std::vector<int> m_calling_order;

public:
    functionsInfo(const std::vector<std::string>& preds)
    : m_fpreds_names(preds) {
        m_functions.reserve(m_fpreds_names.size());
        for (auto &pred : m_fpreds_names) {
            m_functions.push_back(function(pred));
        }
        m_calling_order.reserve(m_fpreds_names.size());
    }

    int getFunctionIndex(std::string name) {
        for (int i = 0; i < m_functions.size(); i++) {
            if (m_functions[i].fpred_name == name) {
                return i;
            }
        }
        return -1;
    }

    const std::vector<std::string>& getPredicateNames() const {
        return m_fpreds_names;
    }

    // TODO: also add indexing for functions, getFunction[i]
    std::vector<function>& getFunctions() {
        return m_functions;
    }

    std::unordered_set<int> getSinks() {
        std::unordered_set<int> sinks;
        for (auto &func : m_functions) {
            sinks.insert(func.fpred_sink);
        }
        return sinks;
    }

    std::unordered_set<int> getSources() {
        std::unordered_set<int> sources;
        for (auto &func : m_functions) {
            sources.insert(func.fpred_source);
        }
        return sources;
    }

    void addRelevantCHCs(const std::vector<int>& chc_nums) {
        m_function_relevant_chcs.insert(chc_nums.begin(), chc_nums.end());
    }

    void addCall(int from_predicate, int to_predicate) {
        m_caller_to_callee[from_predicate].push_back(to_predicate);
    }

    void addCallingOrder(int predicate) {
        m_calling_order.push_back(predicate);
    }

    // topological sort
    void findCallingOrder() {
        std::unordered_set<int> visited;
        std::function<void(int)> dfs = [&](int predicate) {
            if (visited.find(predicate) != visited.end()) return;
            visited.insert(predicate);
            for (auto &callee : m_caller_to_callee[predicate]) {
                dfs(callee);
            }
            addCallingOrder(predicate);
        };
        for (auto &caller_callee : m_caller_to_callee) {
            dfs(caller_callee.first);
        }
    }

    std::vector<int>& getCallingOrder() {
        return m_calling_order;
    }

    void printCalls() {
        for (auto &caller_callee : m_caller_to_callee) {
            for (auto &callee : caller_callee.second) {
                std::cout << m_functions[caller_callee.first].name << " calls ";
                std::cout << m_functions[callee].name << "\n";
            }
        }
    }

    void callGraphToDotFile(std::string filename) {
        std::ofstream file(filename);
        file << "digraph CallGraph {\n";
        if (m_caller_to_callee.empty()) {
            for (auto &func : m_functions) {
                file << func.name << ";\n";
            }
        }
        else {
            for (auto &caller_callee : m_caller_to_callee) {
                for (auto &callee : caller_callee.second) {
                    file << m_functions[caller_callee.first].name << " -> ";
                    file << m_functions[callee].name << ";\n";
                }
            }
        }
        file << "}\n";
        file.close();
    }

    void printFunctions() {
        for (auto &func : m_functions) {
            func.print();
        }
    }
};


// A class to represent a node in the CHC graph
// A node is a CHC with a unique CHC number
struct Node {
public:
    int chc_num;
    std::shared_ptr<Node> next;
    ExprVector& srcs;
    Expr dstRelation;

    explicit Node(int _chc_num, ExprVector& _srcs, Expr _dstRelation)
    : chc_num(_chc_num), next(nullptr), srcs(_srcs), dstRelation(_dstRelation) {}


    void print(std::ostream &os) const {
        os << chc_num << ": " << dstRelation << " <- ";
        if (srcs.empty()) {
            os << "\u22A4"; // print top symbol
            os << "\n";
            return;
        }
        for (int i = 0; i < srcs.size() - 1; i++) {
            os << srcs[i] << ", ";
        }
        os << srcs.back() << "\n";
    }
};


// A class to define non-linear CHCs
class CHCsGraph {
    // Mapping from CHC number to the corresponding node
    std::unordered_map<int, std::shared_ptr<Node>> chc_num_to_node;
    // Mapping from destination relation to the corresponding node
    // This maintains a linked list of CHCs that share the same destination relation
    std::unordered_map<Expr, std::shared_ptr<Node>> dstRelation_to_node;

    // TODO: define iterator for the linked list of nodes with the same destination relation

public:
    void addNode(int chc_num, Expr dstRelation, ExprVector &srcs) {
        if (chc_num_to_node.find(chc_num) != chc_num_to_node.end()) {
            // The node already exists, hence the dstRelation has already been processed
            return;
        }
        auto newNode = std::make_shared<Node>(chc_num, srcs, dstRelation);
        chc_num_to_node[chc_num] = newNode;
        auto dstNode = dstRelation_to_node.find(dstRelation);
        if (dstNode != dstRelation_to_node.end()) {
            // A node with the same destination relation already exists
            // Add the new node to the end of the linked list
            auto lastNode = dstNode->second;
            while (lastNode->next != nullptr) {
                lastNode = lastNode->next;
            }
            lastNode->next = newNode;
        }
        else {
            // Create a new linked list with the new node
            dstRelation_to_node[dstRelation] = newNode;
        }
    }

    // Returns a specific node based on the CHC number
    std::shared_ptr<Node> getNode(int chc_num) {
        return chc_num_to_node.count(chc_num) ? chc_num_to_node[chc_num] : nullptr;
    }

    // Returns a (linked) list of nodes that share the same destination relation
    std::shared_ptr<Node> getNode(Expr dstRelation) {
        return dstRelation_to_node.count(dstRelation) ? dstRelation_to_node[dstRelation] : nullptr;
    }

    // Returns true if there is a path from srcExpr to dstExpr
    bool hasPath(Expr srcExpr, Expr dstExpr) {
        auto srcNode = getNode(srcExpr);
        if (srcNode == nullptr) return false;
        ExprSet visited;
        std::function<bool(Expr)> dfs = [&](Expr dst) {
            if (dst == srcExpr) return true;
            if (visited.find(dst) != visited.end()) return false;
            visited.insert(dst);
            auto node = getNode(dst);
            while (node != nullptr) {
                for (auto &src : node->srcs) {
                    if (dfs(src)) return true;
                }
                node = node->next;
            }
            return false;
        };
        return dfs(dstExpr);
    }

    void print(std::ostream &os) {
        for (auto &p : dstRelation_to_node) {
            auto node = p.second;
            os << "(" << p.first << ")\n";
            while (node != nullptr) {
                node->print(os);
                node = node->next;
            }
            os << "\n";
        }
    }

    void addEdge(std::ofstream &file, const ExprVector& srcs, Expr dst, int& counter) {
        if (srcs.empty()) return;
        std::string dst_str = lexical_cast<std::string>(dst);
        if (srcs.size() == 1) {
            std::string src_str = lexical_cast<std::string>(srcs[0]);
            file << src_str << " -> " << dst_str << "\n";
        }
        else {
            std::string dummy = "dummy" + std::to_string(counter++);
            file << "    subgraph cluster_" << counter << " {\n";
            file << "        style = invis;\n";
            file << "        " << dummy << " [shape=point, width=0.05];\n";
            for (auto &src : srcs) {
                std::string src_str = lexical_cast<std::string>(src);
                file << "        " << src_str << " -> " << dummy << " [style=dashed];\n";
            }
            file << "        " << dummy << " -> " << dst_str << ";\n";
            file << "    }\n";
        }
    }

    void toDotFile(std::ofstream &file, Expr dst, int& counter, ExprSet &visited,
                   const std::unordered_set<int> &sinks, const std::unordered_set<int> &sources) {
        if (visited.find(dst) != visited.end()) return;
        auto node = getNode(dst);
        if (sinks.find(node->chc_num) != sinks.end()) {
            file << dst << " [shape=box, style=filled, fillcolor=lightblue];\n";
        }
        if (sources.find(node->chc_num) != sources.end()) {
            file << dst << " [shape=box, style=filled, fillcolor=lightgreen];\n";
        }
        visited.insert(dst);
        while (node != nullptr) {
            addEdge(file, node->srcs, dst, counter);
            for (auto &src : node->srcs) {
                toDotFile(file, src, counter, visited, sinks, sources);
            }
            node = node->next;
        }
    }

    void toDotFile(std::string filename, const std::unordered_set<int>& sinks,
                   const std::unordered_set<int>& sources) {
        std::ofstream file(filename);
        file << "digraph CHC_Graph {\n";
        int counter = 0;
        ExprSet visited;
        for (auto &p : dstRelation_to_node) {
            toDotFile(file, p.first, counter, visited, sinks, sources);
        }
        file << "}\n";
        file.close();
    }
};


struct inlinedDefinition {
    Expr definition;
    ExprVector dsts;

    inlinedDefinition() = default;
    inlinedDefinition(Expr _definition, ExprVector _dsts)
    : definition(_definition), dsts(std::move(_dsts)) {}
};


struct SummaryInfo {
    // we use the following criteria to identify which kind of summary to use:
        // index=-2 -> No disjunctions/basic summary
        // index=-1 -> OR-ed summary (with disjuncts)
        // index=0..n-1 = ITE-based summary (with disjuncts) where n is the number of
            // permutations of disjuncts
    int summaryIndex = -2;
    std::vector<Expr> disjuncts;
    size_t numDisjuncts = 0;
    std::vector<std::vector<int>> disjunctsIndicesPermutations;
    ExprVector summaries;
    bool invalidSummary = false;
    Expr rel; // relation/predicate for which this summary is being generated
    std::string prefix; // prefix for sygus files
    // variable sets for constructing summaries
    ExprVector v; // all variables
    ExprVector u; // interface variables
    ExprVector l; // local variables
    ExprVector v_types; // types of all variables
    ExprVector u_types; // types of interface variables
    ExprVector forall_u_args; // forall quantifier arguments for interface variables
    ExprVector forall_v_args; // forall quantifier arguments for all variables
    ExprVector exists_l_args; // exists quantifier arguments for local variables

    SummaryInfo() = default;
    SummaryInfo(Expr _rel, ExprVector&& _disjuncts, int _summaryIndex,
                ExprVector&& _u, std::vector<ExprVector>&& _keepIntactPreds,
                std::vector<std::vector<ExprVector>>&& _keepIntactPredsVars, ExprFactory& _efac)
    : rel(_rel), disjuncts(std::move(_disjuncts)), numDisjuncts(disjuncts.size()),
        summaryIndex(_summaryIndex), u(std::move(_u)),
        prefix("sygus_files/" + lexical_cast<string>(rel) + "_summary") {
        constructVariableSets(_efac);
        insertIntactPreds(std::move(_keepIntactPreds), std::move(_keepIntactPredsVars), _efac);
    }

    void insertIntactPreds(std::vector<ExprVector>&& keepIntactPreds,
                          std::vector<std::vector<ExprVector>>&& keepIntactPredsVars,
                           ExprFactory& efac) {
        for (int i = 0; i < numDisjuncts; i++) {
            Expr& disjunct = disjuncts[i];
            ExprVector& intactPreds = keepIntactPreds[i];
            std::vector<ExprVector>& intactPredsVars = keepIntactPredsVars[i];
            for (int j = 0; j < intactPreds.size(); j++) {
                Expr& intactPred = intactPreds[j];
                ExprVector& intactPredVars = intactPredsVars[j];
                ExprVector types;
                for (auto& var : intactPredVars) {
                    types.push_back(typeOf(var));
                }
                Expr decl = bind::fdecl(mkTerm<string>(lexical_cast<string>(intactPred), efac),
                                        types);
                Expr app = bind::fapp(decl, intactPredVars);
                disjunct = mk<AND>(disjunct, app);
            }
        }
    }

    void constructVariableSets(ExprFactory& efac) {
        // declare variables; keep them common for all disjuncts rather than per disjunct
        // can improve this later, but not necessary
        // these variables are used for all candidates to be synthesized
        filter(mknary<OR>(disjuncts), bind::IsConst(), std::inserter(v, v.begin()));
        // compute set difference v - u
        for (auto &var : v) {
            if (std::find(u.begin(), u.end(), var) == u.end()) {
                l.push_back(var);
            }
        }
        // compute signature for the function definition (same for all disjuncts)
        for (auto &var : v) {
            v_types.push_back(typeOf(var));
        }
        v_types.push_back(mk<BOOL_TY>(efac));

        // compute signature for the function summary (same for all disjuncts)
        for (auto &var : u) {
            u_types.push_back(typeOf(var));
        }
        u_types.push_back(mk<BOOL_TY>(efac));

        // construct the exists quantifier arguments 
        for (auto& var : l) exists_l_args.push_back(var->left());

        // construct the forall quantifier arguments
        for (auto& var : u) forall_u_args.push_back(var->left());

        // construct the forall quantifier for all variables (u + l)
        for (auto& var : v) forall_v_args.push_back(var->left());
    }

    std::string stringifySummaryKind() {
        if (isBasicSummary()) {
            return "_basic";
        }
        else if (isOrSummary()) {
            return "_or";
        }
        else {
            return "_ite_" + std::to_string(summaryIndex);
        }
    }

    bool isBasicSummary() {
        return summaryIndex == -2;
    }

    bool isOrSummary() {
        return summaryIndex == -1;
    }

    bool isITESummary() {
        return summaryIndex >= 0;
    }

    void computePermutations() {
        disjunctsIndicesPermutations.clear();
        std::vector<int> indices(numDisjuncts);
        for (size_t i = 0; i < numDisjuncts; i++) {
            indices[i] = i;
        }
        do {
            disjunctsIndicesPermutations.push_back(indices);
        } while (std::next_permutation(indices.begin(), indices.end()));
    }

    void findNextSummaryKind() {
        assert(summaryIndex > -2);
        if (disjunctsIndicesPermutations.empty()) {
            computePermutations();
        }
        if (summaryIndex < (int)disjunctsIndicesPermutations.size() - 1) {
            summaryIndex++;
        }
    }

    std::vector<int> getITEPermutation() {
        assert(summaryIndex >= 0);
        if (summaryIndex < disjunctsIndicesPermutations.size()) {
            return disjunctsIndicesPermutations[summaryIndex];
        }
    }

    void computePredicateSets(std::string name, ExprVector& predicates,
                              std::vector<std::string>& predicateNames, ExprFactory& efac) {
        // TODO: fix this
        int inputVariableIndex = 6;
        ExprVector inputVariables, inputVariablesTypes;
        inputVariables.push_back(u[inputVariableIndex]);
        inputVariablesTypes.push_back(u_types[inputVariableIndex]);
        inputVariablesTypes.push_back(mk<BOOL_TY>(efac));
        size_t numPreds = [&]() {
            return name == "G" ? numDisjuncts - 1 : numDisjuncts;
        }();

        std::string relName = lexical_cast<string>(rel);
        for (int i = 0; i < numPreds; i++) {
            std::string predName = relName + "_" + name + "_" + std::to_string(i);
            Expr decl = bind::fdecl(mkTerm<string> (predName, efac),
                                        name == "definition" ? v_types :
                                        name == "G" ? inputVariablesTypes :
                                        u_types);
            Expr app = bind::fapp(decl, name == "definition" ? v :
                                        name == "G" ? inputVariables :
                                        u);
            predicates.push_back(app);
            predicateNames.push_back(predName);
        }
    }
};

// Keeping track of which candidates in a certain function to chekc equivalence for
struct EquivalenceCands {
    bool checkEq;
    std::string func1Name;
    std::string func2Name;
    ExprVector func1Preds; // fpred and fpred_trailing_pred for func1
    ExprVector func2Preds; // fpred and fpred_trailing_pred for func2

    EquivalenceCands() : checkEq(false), func1Name(""), func2Name("") {}
    void populate(std::string f1Name, std::string f2Name, const ExprVector& f1Preds,
                  const ExprVector& f2Preds) {
        checkEq = true;
        func1Name = f1Name;
        func2Name = f2Name;
        func1Preds = f1Preds;
        func2Preds = f2Preds;
    }
};


struct SummaryGenerator {
    std::unordered_map<Expr, SummaryInfo> summaries;
    SMTUtils &m_u;
    EZ3 &m_z3;
    ExprFactory &m_efac;
    // keep one map for all extra decls, and declare them all when needed;
    // this can be improved later
    ExprMap m_extraDecls;
    SummaryGenerator(SMTUtils& _u, EZ3& z3, ExprFactory& efac) : m_u(_u), m_z3(z3), m_efac(efac)
    {}

    void addInfo(Expr rel, ExprVector &&disjuncts, ExprVector &&dsts,
                 std::vector<ExprVector> &&keepIntactPreds,
                 std::vector<std::vector<ExprVector>> &&keepIntactPredsVars) {
        int summaryIndex = disjuncts.size() > 1 ? -1 : -2;
        for (int i = 0; i < keepIntactPreds.size(); i++) {
            auto& intactPreds = keepIntactPreds[i];
            auto& intactPredsVars = keepIntactPredsVars[i];
            for (int j = 0; j < intactPreds.size(); j++) {
                auto& intactPred = intactPreds[j];
                auto& intactPredVars = intactPredsVars[j];
                ExprVector types;
                for (auto& var : intactPredVars) {
                    types.push_back(typeOf(var));
                }
                Expr decl = bind::fdecl(mkTerm<string>(lexical_cast<string>(intactPred), m_efac),
                                        types);
                m_extraDecls[intactPred] = decl;
            }
        }
        summaries[rel] = SummaryInfo(rel, std::move(disjuncts), summaryIndex, std::move(dsts),
                                     std::move(keepIntactPreds), std::move(keepIntactPredsVars),
                                     m_efac);
    }

    void addSummary(Expr rel, Expr summary) {
        summaries[rel].summaries.push_back(summary);
    }

    bool isSummaryAvailable(Expr rel) {
        return !summaries[rel].invalidSummary && !summaries[rel].summaries.empty();
    }

    inlinedDefinition getSummary(Expr rel) {
        assert(isSummaryAvailable(rel));
        return inlinedDefinition(summaries[rel].summaries.back(),
                                 summaries[rel].u);
    }

    void declareLogicAndDataTypes(std::ofstream& file, bool declareDivMod=false) {
        file << "(set-logic ALL)\n\n";
        // declare datatypes used
        file << "(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))" << "\n";
        file << "(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))" << "\n";
        file << "(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))" << "\n";
        file << "(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))" << "\n";
        file << "(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))" << "\n";
        file << "(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))" << "\n\n";

        if (declareDivMod) {
            file << "(define-fun div_total ((x Int) (y Int)) Int\n";
            file << "  (ite (= y 0) x (div x y))\n";
            file << ")\n\n";
            file << "(define-fun mod_total ((x Int) (y Int)) Int\n";
            file << "  (ite (= y 0) x (mod x y))\n";
            file << ")\n\n";
        }
    }

    // specialized print function
    void print(Expr e, std::ostream& out = outs()) {
        if (isOpX<FAPP>(e) && e->arity() > 1) {
            Expr name = e->left()->left();
            if (m_extraDecls.find(name) != m_extraDecls.end()) {
                out << "(";
                out << lexical_cast<std::string>(e->left()->left()) << " ";
                for (int i = 1; i < e->arity(); i++)
                {
                    out << m_z3.toSmtLib(e->arg(i));
                    if (i < e->arity() - 1) out << " ";
                }
                out << ")";
            }
            else {
                out << m_z3.toSmtLib(e);
            }
        }
        else if (isOpX<FORALL>(e) || isOpX<EXISTS>(e))
        {
            if (isOpX<FORALL>(e)) out << "(forall (";
            else out << "(exists (";

            for (int i = 0; i < e->arity() - 1; i++)
            {
                Expr var = bind::fapp(e->arg(i));
                out << "(" << m_z3.toSmtLib(var) << " " << m_z3.toSmtLib(typeOf(var)) << ")";
                if (i != e->arity() - 2) out << " ";
            }
            out << ") ";
            print (e->last(), out);
            out << ")";
        }
        else if (isOpX<NEG>(e))
        {
            out << "(not ";
            print(e->left(), out);
            out << ")";
        }
        else if (isOpX<AND>(e))
        {
            out << "(and ";
            ExprSet cnjs;
            getConj(e, cnjs);
            int i = 0;
            for (auto & c : cnjs)
            {
                i++;
                print(c, out);
                if (i != cnjs.size()) out << " ";
            }
            out << ")";
        }
        else if (isOpX<OR>(e))
        {
            out << "(or ";
            ExprSet dsjs;
            getDisj(e, dsjs);
            int i = 0;
            for (auto & d : dsjs)
            {
                i++;
                print(d, out);
                if (i != dsjs.size()) out << " ";
            }
            out << ")";
        }
        else if (isOpX<IMPL>(e) || isOp<ComparissonOp>(e))
        {
            if (isOpX<IMPL>(e)) out << "(=> ";
            if (isOpX<EQ>(e)) out << "(= ";
            if (isOpX<GEQ>(e)) out << "(>= ";
            if (isOpX<LEQ>(e)) out << "(<= ";
            if (isOpX<LT>(e)) out << "(< ";
            if (isOpX<GT>(e)) out << "(> ";
            if (isOpX<NEQ>(e)) out << "(distinct ";
            print(e->left(), out);
            out << " ";
            print(e->right(), out);
            out << ")";
        }
        else if (isOpX<ITE>(e))
        {
            out << "(ite ";
            print(e->left(), out);
            out << " ";
            print(e->right(), out);
            out << " ";
            print(e->last(), out);
            out << ")";
        }
        else out << m_z3.toSmtLib (e);
    }

    void constructDeclareFun(string name, Expr decl, std::ostream& file) {
        file << "(declare-fun " << name << " (";
        for (int i = 1; i < decl->arity(); i++)
        {
            m_u.print(decl->arg(i), file);
            if (i < decl->arity()-1) file << " ";
        }
        file << ") Bool\n";
        file << ")\n\n";
    }

    void constructTypedVariables(string prefix, string name, const ExprVector& vars, std::ostream& file, Expr definition=nullptr) {
        file << "(" << prefix << " " << name << " (";
        for (int i = 0; i < vars.size(); i++)
        {
            file << "(";
            m_u.print(vars[i], file);
            file << " " ;
            m_u.print(typeOf(vars[i]), file);
            file << ")";
            if (i < vars.size()-1) file << " ";
        }
        file << ") Bool\n";
        if (definition != nullptr) {
            print(definition, file);
        }
        file << ")\n\n";
    }

    bool readSygusOutput(std::string filename, const std::vector<std::string>& names,
                         std::string& func_def) {
        // check if all synthesis candidates were found in the file
        std::ifstream ifs(filename);
        if (!ifs) {
            std::cout << "Error: Could not open sygus output file." << std::endl;
            return false;
        }
        std::string content((std::istreambuf_iterator<char>(ifs)),
                            std::istreambuf_iterator<char>());

        for (const auto& s : names) {
            if (content.find(s) == std::string::npos) {
                std::cout << s << " not synthesized." << std::endl;
                return false;
            }
        }
        ifs.close();

        // extract the definitions from the file
        std::ifstream infile(filename);

        // TODO: use --sygus-out=status-and-def option of cvc5 to simplify parsing
        std::string line;
        size_t line_count = 0;
        while (std::getline(infile, line)) {
            line_count++;
        }
        infile.clear();
        infile.seekg(0, std::ios::beg);
        size_t current_line = 0;
        while (std::getline(infile, line)) {
            if (current_line != 0 && current_line != line_count - 1) {
                /*
                // some hack to deal with mod_total and div_total functions
                if (line.find("mod_total") != std::string::npos ||
                    line.find("div_total") != std::string::npos) {
                    // remove _total from the line
                    line = std::regex_replace(line, std::regex("_total"), "");
                }
                */
                func_def += line + "\n";
            }
            current_line++;
        }
        infile.close();
        return true;
    }

    /* Generic function to handle all kind of sygus queries required for summary generation.
     * Variables are:
     *  v = all variables
     *  u = interface variables
     *  l = local variables
     *  v = u ∪ l
     * Summaries that are being supported:
     * 1. Definition <=> Summary
     *   the queries will be:
     *    a. ∀ v . D(v) => S(u)
     *    b. ∀ u . S(u) => ∃ l . D(v)
     * 2. Summary => Guard
     *  the query will be:
     *    a. ∀ u . S(u) => G(u)
     * 3. Summary <=> Guard /\ Branch
     *  the queries will be:
     *    a. ∀ u . S(u) <=> G(u) /\ B(u)
     */
    void constructSygusQuery(Expr rel, std::string sygusFile,
                             // definitions (case 1), summaries (case 2 and 3)
                             const ExprVector& fapps1,
                             // summaries (case 1), guards (case 2), branches (case 3)
                             const ExprVector& synthCandidates,
                             const std::vector<std::string>& synthCandidateNames,
                             // guards (case 3), empty for case 1 and 2
                             const ExprVector& fapps2,
                             const std::vector<std::string>& fapp2Names,
                             const ExprVector& fapp1_defs,
                             const ExprVector& fapp2_defs,
                             // when using dealing with definitions with local variables
                             bool constructingSummaries, // case 1
                             bool constructingBranches // case 3
                             ) {
        assert(fapps1.size() == synthCandidates.size());
        assert(!constructingBranches || (fapps1.size() == fapps2.size()));

        SummaryInfo& info = summaries[rel];
        // TODO: fix this
        int inputVariableIndex = 6;
        ExprVector inputVariables;
        inputVariables.push_back(info.u[inputVariableIndex]);
        {
            std::ofstream file(sygusFile, std::ios::trunc);
        }
        std::ofstream file(sygusFile, std::ios::app);

        // set logic and declare datatypes used
        declareLogicAndDataTypes(file);

        // if there are any uninterpreted predicates, declare them
        for (auto &declPair : m_extraDecls) {
            Expr decl = declPair.second;
            std::string predName = lexical_cast<string>(declPair.first);
            constructDeclareFun(predName, decl, file);
        }

        // synthesis candidates
        for (auto &name : synthCandidateNames) {
            constructTypedVariables("synth-fun", name,
                    (constructingSummaries || constructingBranches) ? info.u : inputVariables,
                    file);
        }

        if (constructingBranches) {
            for (int i = 0; i < fapp2Names.size(); i++) {
                constructTypedVariables("define-fun", fapp2Names[i], 
                                        inputVariables, // generally, info.u, 
                                        file, fapp2_defs[i]);
            }
        }

        bool isTwoWayImpl = (constructingSummaries || constructingBranches);
        for (int i = 0; i < fapps1.size(); i++) {
            Expr fapp1 = fapps1[i];
            Expr synthCandidate = synthCandidates[i];
            std::string fapp1_name = lexical_cast<string>(fapp1->left()->left());

            Expr e = rewriteOrAnd(simplifyArithm(simplifyBool(fapp1_defs[i]))); // simplify the definitions to make it easier for the synthesizer to solve
            //e = propagateEqualities(e);
            e = simplifyArithmConjunctions(e);
            e = simplifyArithmDisjunctions(e);
            // definitions of any predicates
            constructTypedVariables("define-fun", fapp1_name,
                                    constructingSummaries ? info.v : info.u, file,
                                    e);
            // constructing right direction (=>) implication
            Expr impl1 = mk<IMPL>(fapp1, constructingBranches ?
                                            mk<AND>(synthCandidate, fapps2[i]) :
                                            synthCandidate);

            // forall vars . impl1
            Expr forall_fla1;
            ExprVector vars = constructingSummaries ? info.forall_v_args : info.forall_u_args;
            if (vars.empty()) forall_fla1 = impl1;
            else {
                vars.push_back(impl1);
                forall_fla1 = mknary<FORALL>(vars);
            }

            file << "(constraint \n";
            m_u.print(forall_fla1, file);
            file << "\n)\n\n";

            if (isTwoWayImpl) {
                if (constructingSummaries) {
                    if (!info.exists_l_args.empty()) {
                        info.exists_l_args.push_back(fapp1);
                        fapp1 = mknary<EXISTS>(info.exists_l_args);
                        info.exists_l_args.pop_back(); // to reuse the variables vector
                    }
                }

                // constructing left direction (<=) implication
                Expr impl2 = mk<IMPL>(constructingBranches ? mk<AND>(synthCandidate, fapps2[i]) :
                                            synthCandidate, fapp1);

                // forall u . impl2
                Expr forall_fla2;
                if (info.forall_u_args.empty()) forall_fla2 = impl2;
                else {
                    info.forall_u_args.push_back(impl2);
                    forall_fla2 = mknary<FORALL>(info.forall_u_args);
                    info.forall_u_args.pop_back(); // to reuse the variables vector
                }

                file << "(constraint \n";
                m_u.print(forall_fla2, file);
                file << "\n)\n\n";
            }
        }
        file << "\n(check-synth)\n";
        file.close();
    }

    ExprVector parseDefinitionsFromString(std::string& definitions,
                                    const std::vector<Expr>& predApps,
                                    const ExprVector& vars) {
        ExprVector definitionSet;
        std::string output_file2 = "sygus_files/output.smt2";
        // TODO: currently, for each summary, we dump all synthesized summary definitions,
        // and then parse each definition one by one. This can be improved
        for (int i = 0; i < predApps.size(); i++) {
            Expr app = predApps[i];
            std::ofstream outfile(output_file2);

            // set logic and declare datatypes used
            declareLogicAndDataTypes(outfile, true);

            outfile << definitions << "\n";

            for (auto &var : vars) {
                outfile << "(declare-var ";
                m_u.print(var, outfile);
                outfile << " ";
                m_u.print(typeOf(var), outfile);
                outfile << ")\n";
            }

            outfile << "\n\n(assert ";
            m_u.print(app, outfile);
            outfile << ")\n";
            outfile << "(check-sat)\n";

            outfile.close();

            definitionSet.push_back(z3_from_smtlib_file(m_z3, output_file2.c_str()));
        }
        return definitionSet;
    }

    // computes guards from guard predicates G0, G1, ..., Gn
    // guards are computed as:
    // guard0 = G0
    // guard1 = ¬G0 ∧ G1
    // guard2 = ¬G0 ∧ ¬G1 ∧ G2
    // ...
    // guardn = ¬G0 ∧ ¬G1 ∧ ... ∧ ¬Gn-1
    ExprVector computeGuards(ExprVector& guardPreds) {
        Expr prev = mk<TRUE>(m_efac);
        ExprVector guards;
        for (auto &pred : guardPreds) {
            guards.push_back(mk<AND>(prev, pred));
            prev = mk<AND>(prev, mkNeg(pred));
        }
        guards.push_back(simplifyBool(prev)); // last guard
        return guards;
    }

    bool sygusEngine(Expr rel, EquivalenceCands &equiv, bool version2) {
        SummaryInfo& info = summaries[rel];
        ExprVector& disjuncts = info.disjuncts;
        /*
        if (!info.isBasicSummary()) {
            // only enforcing for now
            std::cout << "forcing ITE-based summary generation..." << std::endl;
            info.findNextSummaryKind();
        }
        */

        ExprVector defApps, summApps;
        std::vector<std::string> defNames, summNames;
        // definition0, definition1, ..., definitionn
        info.computePredicateSets("definition", defApps, defNames, m_efac);
        // summary0, summary1, ..., summaryn
        info.computePredicateSets("summary", summApps, summNames, m_efac);

        std::string fileName = info.prefix + info.stringifySummaryKind() + ".smt2";
        // sygus query for constructing summaries
        constructSygusQuery(rel, fileName, defApps, summApps, summNames, {}, {}, disjuncts, {},
                            true, false);

        auto runCommand = [&](const std::string& cmd) {
            int ret = system(cmd.c_str());
            if (ret != 0) {
                std::cout << "Error: Sygus engine failed to run." << std::endl;
                return false;
            }
            return true;
        };

        // call sygus engine on the file
        std::string outputFile = info.prefix + "_output.smt2";
        std::string command = "timeout -s SIGTERM 5s cvc5 --lang=sygus2 " + fileName + " > " +
            outputFile;
        if (!runCommand(command)) {
            if (info.isBasicSummary()) {
                return false; // no retry
            }
            info.findNextSummaryKind();
            return true; // retry
        }

        std::string funcDef;
        // read the sygus output file and extract the function definitions
        if (!readSygusOutput(outputFile, summNames, funcDef)) {
            return false;
        }

        if (info.isBasicSummary() || info.isOrSummary()) {
            std::cout << "constructing "
                      << (info.isBasicSummary() ? "basic" : "OR-based")
                      << " summary..." << std::endl;
            std::string outputFile2 = info.prefix + "_output2.smt2";
            std::ofstream outfile(outputFile2);

            // set logic and declare datatypes used
            declareLogicAndDataTypes(outfile, true);

            for (auto &declPair : m_extraDecls) {
                Expr decl = declPair.second;
                std::string predName = lexical_cast<string>(declPair.first);
                constructDeclareFun(predName, decl, outfile);
            }

            outfile << funcDef << "\n";

            for (auto &var : info.u) {
                outfile << "(declare-var ";
                m_u.print(var, outfile);
                outfile << " ";
                m_u.print(typeOf(var), outfile);
                outfile << ")\n";
            }

            // construct a disjunction of all summary applications
            std::string summName = lexical_cast<string>(rel) + "_summary_final";
            Expr disjoinedSummApps;
            if (summApps.size() == 1) disjoinedSummApps = summApps[0];
            else disjoinedSummApps = mknary<OR>(summApps);
            constructTypedVariables("define-fun", summName, info.u, outfile, disjoinedSummApps);

            // construct the summary application
            Expr summDecl = bind::fdecl(mkTerm<string>(summName, m_efac), info.u_types);
            Expr summApp = bind::fapp(summDecl, info.u);

            outfile << "\n\n(assert ";
            m_u.print(summApp, outfile);
            outfile << ")\n";
            outfile << "(check-sat)\n";

            outfile.close();

            // parse the function definition using z3
            // TODO: something can go wrong here, need to add error handling
            Expr final_summary = z3_from_smtlib_file(m_z3, outputFile2.c_str());
            final_summary = simplifyBool(final_summary);
            final_summary = simplifyArithm(final_summary);
            /*
            final_summary = unfoldITE(final_summary);
            final_summary = liftITEs(final_summary);
            final_summary = rewriteOrAnd(final_summary);
            final_summary = normalize(final_summary);
            final_summary = moveInsideITE(final_summary);
            */
            final_summary = simplifyArithmConjunctions(final_summary);
            final_summary = simplifyArithmDisjunctions(final_summary);
            //final_summary = propagateEqualities(final_summary);
            final_summary = rewriteOrAnd(simplifyArithm(simplifyBool(final_summary)));
            addSummary(rel, final_summary);

            if (!equiv.checkEq) {
                return false; // no equivalence check needed and no retry
            }

            // fill in the equivalence check info in the files
            std::string fileNumber = "";
            if (version2) {
                fileNumber = rel == equiv.func2Preds[0] ? "1" :
                    rel == equiv.func2Preds[1] ? "2" : "";
            }
            else {
                fileNumber = rel == equiv.func1Preds[0] ? "1" :
                    rel == equiv.func1Preds[1] ? "2" : "";
            }
            if (fileNumber != "") {
                // construct the equivalence check
                std::string equivalence_file = "sygus_files/" + equiv.func1Name + "_" + equiv.func2Name + "_equiv_" + fileNumber + ".smt2";
                std::ofstream eq_file;
                if (version2) {
                    eq_file.open(equivalence_file, std::ios_base::app);
                }
                else {
                    eq_file.open(equivalence_file);
                    declareLogicAndDataTypes(eq_file, true);
                }
                eq_file << funcDef << "\n";
                constructTypedVariables("define-fun", summName, info.u, eq_file, disjoinedSummApps);

                for (auto &v : info.u) {
                    eq_file << "(declare-var ";
                    m_u.print(v, eq_file);
                    eq_file << " ";
                    m_u.print(typeOf(v), eq_file);
                    eq_file << ")\n";
                }
                eq_file << "\n\n(assert ";
                m_u.print(summApp, eq_file);
                eq_file << ")\n";
            }
        }
        else {
            std::cout << "constructing ITE-based summary..." << std::endl;
            ExprVector summDefs = parseDefinitionsFromString(funcDef, summApps, info.u);

            // sygus query for constructing guards
            ExprVector guardApps, branchApps;
            std::vector<std::string> guardNames, branchNames;
            // G0, G1, ..., Gn-1
            info.computePredicateSets("G", guardApps, guardNames, m_efac);
            ExprVector guards = computeGuards(guardApps);
            // branch0, branch1, ..., branchn
            info.computePredicateSets("branch", branchApps, branchNames, m_efac);

            auto findPermutations = [](std::vector<int>& perm, ExprVector& predicates) {
                ExprVector permuted;
                for (auto &idx : perm) {
                    permuted.push_back(predicates[idx]);
                }
                return permuted;
            };

            for (; info.summaryIndex < info.disjunctsIndicesPermutations.size();
                info.summaryIndex++) {
                std::vector<int>& perm = info.disjunctsIndicesPermutations[info.summaryIndex];
                std::string guardFile = info.prefix + info.stringifySummaryKind() + "_guards_" +
                    std::to_string(info.summaryIndex) + ".smt2";
                ExprVector permutedSummApps = findPermutations(perm, summApps);
                ExprVector permutedSummDefs = findPermutations(perm, summDefs);

                constructSygusQuery(rel, guardFile, permutedSummApps, guards, guardNames,
                                    {}, {}, permutedSummDefs, {}, false, false);

                // call sygus engine on the file
                std::string command = "timeout -s SIGTERM 5s cvc5 --lang=sygus2 " + guardFile +
                    " > " + outputFile;
                system(command.c_str());

                std::string guardsDef;
                // read the sygus output file and extract the function definitions
                if (!readSygusOutput(outputFile, guardNames, guardsDef)) {
                    continue;
                }

                ExprVector guardDefs = parseDefinitionsFromString(guardsDef, guardApps, info.u);

                // sygus query for constructing branches
                std::string branchFile = info.prefix + info.stringifySummaryKind() +
                    "_branches_" + std::to_string(info.summaryIndex) + ".smt2";
                constructSygusQuery(rel, branchFile, permutedSummApps, branchApps, branchNames,
                                    guards, guardNames, permutedSummDefs, guardDefs, false,
                                    true);
                // call sygus engine on the file
                command = "timeout -s SIGTERM 5s cvc5 --lang=sygus2 " + branchFile + " > " +
                    outputFile;
                system(command.c_str());
                // read the sygus output file and extract the function definitions
                if (!readSygusOutput(outputFile, branchNames, guardsDef)) {
                    continue;
                }
                ExprVector branchDefs = parseDefinitionsFromString(guardsDef, branchApps,
                                                                   info.u);
                // construct the final summary using guards and branches
                // ite(G0, branch0, ite(G1, branch1, ... ite(Gn-1, branchn-1, branchn)...))
                Expr final_summary = branchDefs.back();
                for (int j = guardDefs.size() - 1; j >= 0; j--) {
                    final_summary = mk<ITE>(guardDefs[j], branchDefs[j], final_summary);
                }
                 std::cout << "Final summary constructed: ";
                    m_u.print(final_summary, std::cout);
                    std::cout << "\n";
                // TODO: verification of the final summary should be done here
                addSummary(rel, final_summary);
                break;
            }
        }

        return true;
    }
};


class ContractsCHCs : public CHCs {
public:
    SMTUtils u;
    functionsInfo funcs_info;
    CHCsGraph chc_graph;
    // names to relation mapping (only used for ease of access)
    std::unordered_map<std::string, Expr> names_to_rel;
    // predicate to inlined definition mapping
    // TODO: move this to functionsInfo?
    std::unordered_map<Expr, inlinedDefinition> preds_to_inlined_defs;
    // std::unordered_map<Expr, inlinedDefinition> preds_to_summaries;
    int variableCounter = 0;
    ExprSet checkedEquivalent;

    SummaryGenerator summaryGen;

    ContractsCHCs(ExprFactory &efac, EZ3 &z3, std::string name, std::vector<std::string>& preds)
    : CHCs(efac, z3, name), u(efac, z3), summaryGen(u, z3, efac), funcs_info(preds) {}

    void printFunctionInfo(const function& func) {
        func.print();
        std::cout << "Relevant CHCs:\n";
        for (auto &chc_num : func.chc_nums) {
            chc_graph.getNode(chc_num)->print(std::cout);
        }
        std::cout << "\n";
    }

    Expr renamedClone(Expr origVar, bool isFundsVar=false) {
        // a way of identifying funds variables is needed with current logic
        std::string append = isFundsVar ? "fnd_" : "var_";
        Expr name = mkTerm<string>(varname + append + std::to_string(variableCounter++), m_efac);
        return cloneVar(origVar, name);
    }

    // This function readjusts the variables in the definition
    // The definition computed for a predicate may have different variables than one where we
    // are inlining that definition. Since target CHC can have its own set of variables, and
    // simply making equality between the two sets isn't sufficient (as names may clash), we
    // create new variables for the definition being inlined, and add equalities
    // toInlineIntoVars here are the variables in the target CHC where we are inlining the
    // definition
    void readjustVariables(const inlinedDefinition& inlinedDef,
                           const ExprVector& toInlineIntoVars, ExprVector& terms) {
        ExprVector new_vars;
        Expr definition = inlinedDef.definition;
        for (int i = 0; i < inlinedDef.dsts.size(); i++) {
            Expr v = inlinedDef.dsts[i];
            Expr new_var = renamedClone(v);
            new_vars.push_back(new_var);
            terms.push_back(mk<EQ>(toInlineIntoVars[i], new_var));
            definition = replaceAll(definition, v, new_var);
        }
        terms.push_back(simplifyBool(definition));
    }

    // TODO: this needs to be checked for correctness, along with renaming of variables
    void matchVariables(Expr &definition, const ExprVector& srcVars,
                        const ExprVector& dstVars, ExprVector& terms, function& func) {
        // locVars might also need renaming
        ExprVector new_vars;
        for (int i = 0; i < srcVars.size(); i++) {
            Expr v = srcVars[i];
            Expr new_var = renamedClone(v);
            new_vars.push_back(new_var);
            // This might be too strict. We want to replace the function arguments too, whenever
            // we are inlining the source of the function
            // This should happen only once, but for now, there is no code to enforce that
            // TODO: find a better way/place to handle this renaming
            auto it = std::find(func.args.begin(), func.args.end(), v);
            if (it != func.args.end()) {
                *it = new_var;
            }
            terms.push_back(mk<EQ>(dstVars[i], new_var));
            definition = replaceAll(definition, v, new_var);
        }
        definition = simplifyBool(definition);
    }

    bool findSummary(Expr rel, function& func, EquivalenceCands &equiv, bool version2) {
        if (summaryGen.isSummaryAvailable(rel)) {
            // We have already computed the summary for this predicate
            return false;
        }
        auto node = chc_graph.getNode(rel);
        if (node == nullptr) {
            return false;
        }
        ExprVector disjuncts;
        int chc_num = node->chc_num;
        ExprVector dsts;
        // create a vector of destination variables for this definition,
        // it is okay to use any node for creating the clones of variables
        dsts.reserve(chcs[chc_num].dstVars.size());
        for (auto &v : chcs[chc_num].dstVars) {
            dsts.push_back(renamedClone(v));
        }
        auto inlined_def = new inlinedDefinition{mk<FALSE>(m_efac), dsts};
        auto current = node;
        // keep the preds intact without inlining their summaries, for all disjuncts
        std::vector<ExprVector> keepIntactPreds;
        // keep variables of the preds being kept intact, for all disjuncts
        std::vector<std::vector<ExprVector>> keepIntactPredsVars;
        while (current != nullptr) {
            int chc_num = current->chc_num;
            ExprVector exprs;
            ExprVector intactPreds;
            std::vector<ExprVector> intactVars;
            for (int i = 0; i < current->srcs.size(); i++) {
                Expr src = current->srcs[i];
                auto& src_vars = chcs[chc_num].srcVars[i];
                /*
                if (checkedEquivalent.find(src) != checkedEquivalent.end()) {
                    intactPreds.push_back(src);
                    intactVars.push_back(src_vars);
                    continue;
                }
                */
                // For now, use inlined definition class but change later
                bool retry = findSummary(src, func, equiv, version2);
                if (retry) {
                    return retry;
                }
                inlinedDefinition d = summaryGen.getSummary(src);
                // Take care of different variables, and inserts adjusted expressions into exprs
                readjustVariables(d, src_vars, exprs);
            }
            keepIntactPreds.push_back(intactPreds);
            keepIntactPredsVars.push_back(intactVars);
            // to unify dst variables of all CHCs, add equalities to generated dst variables
            // later, we only use these dst variables for the final summary
            for (int i = 0; i < dsts.size(); i++) {
                exprs.push_back(mk<EQ>(dsts[i], chcs[chc_num].dstVars[i]));
            }
            // Conjoin the summaries of the source relations, including extra formulas to match
            Expr def = mk<AND>(conjoin(exprs, m_efac), chcs[chc_num].body);
            // some cleaning up, might need better solutions later
            ExprSet cnjs;
            getConj(def, cnjs);
            for (auto it = cnjs.begin(); it != cnjs.end(); ) {
                std::string cnj_str = lexical_cast<std::string>(*it);
                if (cnj_str.find("msg.data") != string::npos ||
                    cnj_str.find("msg.sig") != string::npos) {
                    it = cnjs.erase(it);
                }
                else {
                    ++it;
                }
            }
            def = conjoin(cnjs, m_efac);

            // check if a variable starts with "funds"
            // TODO: handle this more elegantly later
            ExprVector vars;
            filter(def, bind::IsConst(), std::inserter(vars, vars.begin()));
            for (auto &v : vars) {
                if (lexical_cast<string>(v).find("funds") != string::npos) {
                    // add a renamed clone of funds variable to dsts
                    Expr new_v = renamedClone(v, true); // true indicates funds variable
                    dsts.push_back(new_v);
                    def = replaceAll(def, v, new_v);
                }
            }

            disjuncts.push_back(def);
            current = current->next;
        }
        std::cout << "invoking sygus engine for " << rel << " with " << disjuncts.size() << " disjuncts...\n";
        // take all the definitions and pass to the sygus engine
        summaryGen.addInfo(rel, std::move(disjuncts), std::move(dsts),
                           std::move(keepIntactPreds), std::move(keepIntactPredsVars));
        summaryGen.sygusEngine(rel, equiv, version2);
        // AH: if something fails in sygusEngine, we should return true to retry
        auto summary = summaryGen.getSummary(rel);
        std::cout << "Summary for " << rel << ": " << summary.definition << "\n\n";
        // preds_to_summaries[rel] = {summary, dsts};
        return false;
    }

    void partitionInputsOutputs(const ExprVector& vars, ExprVector& inputs, ExprVector& outputs) {
        // heuristic-based: given two state variables, everything before second state variable
        // is input, everything after is output; except for the funds variable, which is input
        int state_var_count = 0;
        for (auto &v : vars) {
            if (lexical_cast<string>(typeOf(v)).find("state_type") != string::npos) {
                state_var_count++;
            }
            if (lexical_cast<string>(v).find("fnd_") != string::npos) {
                inputs.push_back(v);
                continue;
            }
            if (state_var_count >= 2) {
                outputs.push_back(v);
            }
            else {
                inputs.push_back(v);
            }
        }
    }

    inlinedDefinition findInlinedDefinition(Expr rel, function& func) {
        if (preds_to_inlined_defs.find(rel) != preds_to_inlined_defs.end()) {
            // We have already computed the inlined definition for this predicate
            return preds_to_inlined_defs[rel];
        }
        auto node = chc_graph.getNode(rel);
        if (node == nullptr) return inlinedDefinition();
        auto current = node;
        // We will go through all the CHCs that have the destination relation as rel,
        // and disjoin their definitions
        ExprVector dsts;
        // create a vector of destination variables for this definition,
        // it is okay to use any node for creating the clones of variables
        int chc_num = node->chc_num;
        dsts.reserve(chcs[chc_num].dstVars.size());
        for (auto &v : chcs[chc_num].dstVars) {
            dsts.push_back(renamedClone(v));
        }
        auto inlined_def = new inlinedDefinition{mk<FALSE>(m_efac), dsts};
        while (current != nullptr) {
            chc_num = current->chc_num;
            ExprVector src_exprs, dst_exprs;
            // For each source relation, we will find the inlined definition
            for (int i = 0; i < current->srcs.size(); i++) {
                Expr src = current->srcs[i];
                inlinedDefinition d = findInlinedDefinition(src, func);
                auto& src_vars = chcs[chc_num].srcVars[i];
                ExprVector eqs;
                // Take care of different variables
                matchVariables(d.definition, d.dsts, src_vars, eqs, func);
                src_exprs.push_back(d.definition);
                dst_exprs.insert(dst_exprs.end(), eqs.begin(), eqs.end());
            }
            // Experimental: eliminate extra/local variables
            //chcs[chc_num].body = eliminateQuantifiers(chcs[chc_num].body, chcs[chc_num].locVars);
            //chcs[chc_num].locVars.clear();

            // Conjoin the definitions of the source relations, including extra formulas to match
            // differently-named variables, with the body of the CHC
            Expr def = mk<AND>(conjoin(src_exprs, m_efac), conjoin(dst_exprs, m_efac),
                               chcs[chc_num].body);
            // Take care of different variables for each CHC to be disjoined
            ExprVector eqs;
            matchVariables(def, chcs[chc_num].dstVars, dsts, eqs, func);
            def = mk<AND>(def, conjoin(eqs, m_efac));
            inlined_def->definition = mk<OR>(inlined_def->definition, def);
            current = current->next;
        }
        preds_to_inlined_defs[rel] = std::move(*inlined_def);
        free(inlined_def);
        preds_to_inlined_defs[rel].definition = simplifyBool(preds_to_inlined_defs[rel].definition);
        return preds_to_inlined_defs[rel];
    }

    void inliningSingleFunction(function& func) {
        auto &source = chcs[func.fpred_source];
        auto &sink = chcs[func.fpred_sink];
        func.args = source.dstVars;
        inlinedDefinition d = findInlinedDefinition(func.fpred_expr, func);
        func.definition = d.definition;
        func.outputs = d.dsts;
        //func.print();
    }


    void inlining() {
        for (auto &i : funcs_info.getCallingOrder()) {
            auto &func = funcs_info.getFunctions()[i];
            //std::cout << "Inlining " << func.name << "\n";
            //std::cout << "----------------------------------\n";
            inliningSingleFunction(func);
            //std::cout << "----------------------------------\n\n";
        }
    }


    void computeCallGraph() {
        auto &functions = funcs_info.getFunctions();
        if (functions.size() <= 1) {
            funcs_info.addCallingOrder(0);
        }
        else {
            for (int i = 0; i < functions.size(); i++) {
                for (int j = i+1; j < functions.size(); j++) {
                    auto &func1 = functions[i];
                    auto &func2 = functions[j];
                    // trailing predicates define the control-flow of the functions,
                    // however, we will start with the actual CHCs since we know the CHC numbers
                    // for them, then trace back (trailing predicates should be on the path)
                    bool found_trace1 = chc_graph.hasPath(func2.fpred_trailing_pred,
                                                          names_to_rel[func1.fpred_name]);
                    bool found_trace2 = chc_graph.hasPath(func1.fpred_trailing_pred,
                                                          names_to_rel[func2.fpred_name]);
                    if (found_trace1 && found_trace2) {
                        std::cout << "Both " << func1.fpred_trailing_pred << " and "
                            << func2.fpred_trailing_pred << " call each other\n";
                        std::cout << "Cannot check equivalence\n";
                        exit(0);
                    } else if (found_trace1) {
                        funcs_info.addCall(i, j);
                    }
                    else if (found_trace2) {
                        funcs_info.addCall(j, i);
                    }
                }
            }
            funcs_info.findCallingOrder();
        }
        funcs_info.callGraphToDotFile(std::string("../call_graph") + varname + ".dot");
    }


    void computeCHCsGraph(Expr dstRelation, ExprSet &processed) {
        if (processed.find(dstRelation) != processed.end()) return;
        processed.insert(dstRelation);
        for (auto &incm : incms[dstRelation]) {
            auto &chc = chcs[incm];
            for (auto &src : chc.srcRelations) {
                computeCHCsGraph(src, processed);
            }
            chc_graph.addNode(incm, dstRelation, chc.srcRelations);
        }
    }

    bool findSource(Expr dstRelation, function& func, ExprSet &processed) {
        if (processed.find(dstRelation) != processed.end()) return false;
        processed.insert(dstRelation);
        auto node = chc_graph.getNode(dstRelation);
        while (node != nullptr) {
            auto &chc = chcs[node->chc_num];
            func.chc_nums.push_back(node->chc_num);
            if (chc.isFact) {
                auto &srcs_of_sink = chcs[func.fpred_sink].srcRelations;
                Expr dst_of_chc = chc.dstRelation;
                auto it = std::find(srcs_of_sink.begin(), srcs_of_sink.end(), dst_of_chc);
                // We are only interested in the source CHC whose dstRelation is not included in
                // the srcRelations of the sink CHC, which skips all the functionality
                if (it == srcs_of_sink.end()) {
                    func.fpred_source = node->chc_num;
                    return true;
                }
            }
            for (auto &src : node->srcs) {
                if (findSource(src, func, processed)) return true;
            }
            node = node->next;
        }
        return false;
    }

    void findRelevantCHCs() {
        // Keep track of the CHCs relevant to the contract functions
        std::set<std::string> processed;
        std::vector<std::string> worklist = funcs_info.getPredicateNames();
        for (size_t i = 0; i < worklist.size(); i++) {
            std::string p = worklist[i];
            if (processed.find(p) != processed.end()) continue;
            processed.insert(p);
            for (auto &d : decls) {
                if (lexical_cast<std::string>(d->left()).compare(p) == 0) {
                    names_to_rel[p] = d->left();
                    auto incms_for_p = incms[names_to_rel[p]];
                    funcs_info.addRelevantCHCs(incms_for_p);
                    for (auto &incm : incms_for_p) {
                        for (auto &src : chcs[incm].srcRelations) {
                            std::string src_str = lexical_cast<std::string>(src);
                            if (src_str.find("interface") == std::string::npos) {
                                worklist.push_back(src_str);
                            }
                        }
                    }
                }
            }
        }
    }

    void initFunctionsInfo() {
        findRelevantCHCs();
        ExprSet processedExprs;
        for (auto &func : funcs_info.getFunctions()) {
            func.fpred_expr = names_to_rel[func.fpred_name];
            auto& all_sinks = incms[func.fpred_expr];
            assert(all_sinks.size() == 1); // only one CHC (sink) for a function predicate
            func.fpred_sink = all_sinks[0];
            for (auto &src : chcs[all_sinks[0]].srcRelations) {
                std::string src_str = lexical_cast<std::string>(src);
                if (src_str.find("summary") != std::string::npos) {
                    func.fpred_trailing_pred = src;
                    break;
                }
            }
            // We compute chc_graph one function at a time, hence we call it here
            computeCHCsGraph(func.fpred_expr, processedExprs);
        }
        computeCallGraph();
        processedExprs.clear();
        // find the source CHC for each function, which needs the call graph is computed
        auto &funcs = funcs_info.getFunctions();
        for (auto &i : funcs_info.getCallingOrder()) {
            auto &func = funcs[i];
            findSource(func.fpred_expr, func, processedExprs);
        }
        chc_graph.toDotFile(std::string("../chc_graph") + varname + ".dot", funcs_info.getSinks(),
                            funcs_info.getSources());
    }


    void parse(std::string smt, std::string contract)
    {
        if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
        std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
        m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
        ZFixedPoint<EZ3> &fp = *m_fp;
        fp.loadFPfromFile(smt);
        chcs.reserve(fp.m_rules.size());

        ExprMap eqs;
        for (auto it = fp.m_rules.begin(); it != fp.m_rules.end(); )
        {
            if (isOpX<EQ>(*it))
            {
                eqs[(*it)->left()->left()] = (*it)->right()->left();
                it = fp.m_rules.erase(it);
            }
            else ++it;
        }


        for (auto &r: fp.m_rules)
        {
            chcs.push_back(HornRuleExt());
            HornRuleExt& hr = chcs.back();
            while (true)
            {
                auto r1 = replaceAll(r, eqs);
                if (r == r1) break;
                else r = r1;
            }

            if (!normalize(r, hr))
            {
                chcs.pop_back();
                continue;
            }

            // small rewr:
            if (isOpX<ITE>(r->last()))
            {
                hr.body = mk<IMPL>(mk<AND>(r->left(), r->last()->left()),
                                   r->last()->right());
                chcs.push_back(chcs.back());
                chcs.back().body = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->last()->left())),
                                            r->last()->last());
            }
            else
        {
                hr.body = r;
            }
        }


        for (auto it = chcs.begin(); it != chcs.end();)
        {
            HornRuleExt & hr = *it;
            hr.head = hr.body->right();
            hr.body = hr.body->left();
            if (isOpX<FAPP>(hr.head))
            {
                if (hr.head->left()->arity() == 2) {
                    //              (find(fp.m_queries.begin(), fp.m_queries.end(), hr.head) !=
                    //               fp.m_queries.end()))
                    if (!addFailDecl(hr.head->left()->left())) {
                        it = chcs.erase(it);
                        continue;
                    }
                }
                else
                addDecl(hr.head->left());


                hr.dstRelation = hr.head->left()->left();
            }
            else
        {
                if (!isOpX<FALSE>(hr.head)) hr.body = mk<AND>(hr.body, mk<NEG>(hr.head));
                if (!addFailDecl(mk<FALSE>(m_efac))) {
                    it = chcs.erase(it);
                    continue;
                }
                //          addFailDecl(mk<FALSE>(m_efac));
                hr.dstRelation = mk<FALSE>(m_efac);
            }
            ++it;
        }

        //TODO: Taken preprocessing from rnd, main cycle below not changed yet

        for (auto it = chcs.begin(); it != chcs.end();)
        {
            ExprVector origSrcSymbs, origDstSymbs;
            ExprSet lin;
            HornRuleExt & hr = *it;



            Expr head = hr.head;
            Expr body = hr.body;

            splitBody(hr, origSrcSymbs, lin);

            hr.isFact = hr.srcRelations.empty();

            if (hr.srcRelations.size() == 0)
            {
                if (hasUninterp(body))
                {
                    lin.clear();
                }
            }

            hr.isQuery = (hr.dstRelation == failDecl);
            if (hr.isQuery)
            {
                it = chcs.erase(it);
                continue;
            }
            ++it;
            hr.isInductive = (hr.srcRelations.size() == 1 && hr.srcRelations[0] == hr.dstRelation);
            if (hr.isQuery) qCHCNum = chcs.size() - 1;
            ExprVector allOrigSymbs;
            for (auto & a : origSrcSymbs)  allOrigSymbs.push_back(a);
            if (!hr.isQuery)
            {
                for (auto it1 = head->args_begin()+1, end = head->args_end(); it1 != end; ++it1)
                    origDstSymbs.push_back(*it1);
            }
            allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
            if (isOpX<FAPP>(hr.head))
            {
                hr.head = head->left();
            }
            hr.body = conjoin(lin, m_efac);
            hr.dstVars.clear();


            vector<ExprVector> tmp;
            // we may have several applications of the same predicate symbol in the body:
            for (int i = 0; i < hr.srcRelations.size(); i++)
            {
                auto & a = hr.srcRelations[i];
                ExprVector tmp1;
                for (int j = 0; j < i; j++)
                {
                    if (hr.srcRelations[i] == hr.srcRelations[j])
                    {
                        for (int k = 0; k < invVars[a].size(); k++)
                        {
                            Expr new_name = mkTerm<string> (varname + to_string(++total_var_cnt), m_efac);
                            tmp1.push_back(cloneVar(invVars[a][k], new_name));
                        }
                        break;
                    }
                }
                if (tmp1.empty())
                {
                    tmp1 = invVars[a];
                }
                tmp.push_back(tmp1);
            }


            hr.assignVarsAndRewrite (origSrcSymbs, tmp,
                                     origDstSymbs, invVars[hr.dstRelation]);

            ExprVector body_vars;
            expr::filter (hr.body, bind::IsConst(), std::inserter (body_vars, body_vars.begin ()));
            for (auto it1 = hr.locVars.begin(); it1 != hr.locVars.end(); )
            {
                if (find(body_vars.begin(), body_vars.end(), *it1) == body_vars.end())
                    it1 = hr.locVars.erase(it1);
                else ++it1;
            }
        }

        for (int i = 0; i < chcs.size(); i++) {
            expr_id[chcs[i].dstRelation] = i;
            incms[chcs[i].dstRelation].push_back(i);
        }

        prune();

        index_fact_chc = -1;
        // find: index_cycle_chc
        for (int i = 0; i < chcs.size(); i++)
        {
            string name = lexical_cast<string>(chcs[i].dstRelation);
            if (name.find("nondet_interface") == std::string::npos &&
                find (chcs[i].srcRelations.begin(), chcs[i].srcRelations.end(),
                      chcs[i].dstRelation) != chcs[i].srcRelations.end() &&
                name.find(contract) != std::string::npos)
            {
                index_cycle_chc.push_back(i);
                //outs () << "cycle found (#" << i << "):\n";
                //print(chcs[i]);
            }
        }

        //assert(!index_cycle_chc.empty());

        /*
        // find fact now:
        for (int i = 0; i < chcs.size(); i++) {
            if (find(index_cycle_chc.begin(), index_cycle_chc.end(), i) !=
                index_cycle_chc.end())
                continue;
            if (chcs[i].dstRelation == chcs[index_cycle_chc[0]].dstRelation) {
                index_fact_chc = i;
                //outs() << "fact found (#" << i << "):\n";
                //print(chcs[i]);
                break;
            }
        }
    */

        // Initialize the functions and function calls info
        initFunctionsInfo();
    }

}; // ContractsCHCs

}   // namespace ufo
