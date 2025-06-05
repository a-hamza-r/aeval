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


class ContractsCHCs : public CHCs {
public:
    functionsInfo funcs_info;
    CHCsGraph chc_graph;
    // names to relation mapping (only used for ease of access)
    std::unordered_map<std::string, Expr> names_to_rel;
    // predicate to inlined definition mapping
    // TODO: move this to functionsInfo?
    std::unordered_map<Expr, inlinedDefinition> preds_to_inlined_defs;
    int variableCounter = 0;

    ContractsCHCs(ExprFactory &efac, EZ3 &z3, std::string name, std::vector<std::string>& preds)
    : CHCs(efac, z3, name), funcs_info(preds) {}

    void printFunctionInfo(const function& func) {
        func.print();
        std::cout << "Relevant CHCs:\n";
        for (auto &chc_num : func.chc_nums) {
            chc_graph.getNode(chc_num)->print(std::cout);
        }
        std::cout << "\n";
    }

    Expr renamedClone(Expr origVar) {
        Expr name = mkTerm<string>(varname + "var_" + std::to_string(variableCounter++), m_efac);
        return cloneVar(origVar, name);
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

    inlinedDefinition findInlinedDefinition(Expr rel, function& func) {
        // We have already computed the inlined definition for this predicate
        if (preds_to_inlined_defs.find(rel) != preds_to_inlined_defs.end()) {
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

        assert(!index_cycle_chc.empty());

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

        // Initialize the functions and function calls info
        initFunctionsInfo();
    }

}; // ContractsCHCs

}   // namespace ufo
