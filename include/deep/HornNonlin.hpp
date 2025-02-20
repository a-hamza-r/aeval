#ifndef HORNNONLIN__HPP__
#define HORNNONLIN__HPP__

#include "ae/AeValSolver.hpp"
#include <memory>
#include <regex>

using namespace std;
using namespace boost;

namespace ufo
{
  // all adapted from Horn.hpp; experimental; to merge with Horn.hpp at some point
  inline bool rewriteHelperConsts_nonlinear(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    vector<ExprVector> srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    ExprVector srcRelations;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;
    map<int, Expr> arg_names;

    void assignVarsAndRewrite (ExprVector& _srcVars, vector<ExprVector>& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      int counter = 0;
      for (int i = 0; i < invVarsSrc.size(); i++)
      {
        ExprVector tmp;
        for (int j = 0; j < invVarsSrc[i].size(); j++)
        {
          tmp.push_back(invVarsSrc[i][j]);
          body = mk<AND>(body, mk<EQ>(_srcVars[counter], tmp[j]));
          counter++;;
        }
        srcVars.push_back(tmp);
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
        arg_names[i] = _dstVars[i];
      }
    }
  };


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

    std::string name;

    function(std::string _fpred_name) : fpred_name(_fpred_name) {}

    void findActualName() {
        // best effort to retrieve the actual function name from the function predicate
        std::regex pattern(R"(summary_+\d+_+function_(.*)_+\d+_+\d+_+\d+)");
        std::smatch match;

        if (std::regex_search(fpred_name, match, pattern)) {
            std::string funcname = match[1].str();

            // Trim leading and trailing underscores
            size_t start = funcname.find_first_not_of('_');
            size_t end = funcname.find_last_not_of('_');

            name = (start != std::string::npos) ? funcname.substr(start, end - start + 1) : "";
        }
    }

    std::string getName() {
        return name == "" ? fpred_name : name;
    }

    void print() {
        std::cout << "Function: " << getName() << "\n";
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
    std::vector<function> m_functions; // a list of functions in the contract

    // a map from caller to callees
    std::unordered_map<int, std::vector<int>> m_caller_to_callee;
    std::vector<int> m_calling_order;

public:
    functionsInfo(const std::vector<std::string>& preds) {
        m_functions.reserve(preds.size());
        for (auto &pred : preds) {
            m_functions.push_back(function(pred));
            m_functions.back().findActualName();
        }
        m_calling_order.reserve(preds.size());
    }

    int getFunctionIndex(std::string name) {
        for (int i = 0; i < m_functions.size(); i++) {
            if (m_functions[i].fpred_name == name) {
                return i;
            }
        }
        return -1;
    }

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

    std::vector<int> getCallingOrder() {
        return m_calling_order;
    }

    void printCalls() {
        for (auto &caller_callee : m_caller_to_callee) {
            for (auto &callee : caller_callee.second) {
                std::cout << m_functions[caller_callee.first].getName() << " calls ";
                std::cout << m_functions[callee].getName() << "\n";
            }
        }
    }

    void callGraphToDotFile(std::string filename) {
        std::ofstream file(filename);
        file << "digraph CallGraph {\n";
        if (m_caller_to_callee.empty()) {
            for (auto &func : m_functions) {
                file << func.getName() << ";\n";
            }
        }
        else {
            for (auto &caller_callee : m_caller_to_callee) {
                for (auto &callee : caller_callee.second) {
                    file << m_functions[caller_callee.first].getName() << " -> ";
                    file << m_functions[callee].getName() << ";\n";
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

    explicit Node(int _chc_num, ExprVector& _srcs)
        : chc_num(_chc_num), next(nullptr), srcs(_srcs) {}


    void print(std::ostream &os) {
        os << chc_num << " <- ";
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
        auto newNode = std::make_shared<Node>(chc_num, srcs);
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


static Expr renameVariables(Expr var, int unique_id, std::string suffix) {
    std::string name = lexical_cast<std::string>(var);
    Expr new_var = mkTerm<string>(suffix + to_string(unique_id) + "_" + name, var->getFactory());
    return cloneVar(var, new_var);
}


static void updateVarsAndBody(ExprVector& vars, Expr& body, int unique_id, std::string suffix = "") {
    ExprVector prev_vars = vars;
    for (int i = 0; i < vars.size(); i++) {
        vars[i] = renameVariables(vars[i], unique_id, suffix);
    }
    body = replaceAll(body, prev_vars, vars);
}


class CHCs
{
private:
    std::set<int> indeces;
    std::string varname = "_FH_";

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    ExprSet decls;
    Expr failDecl;
    ExprVector extras;
    std::vector<HornRuleExt> chcs;
    int index_fact_chc;
    std::vector<int> index_cycle_chc;
    map<Expr, ExprVector> invVars;
    map<Expr, std::vector<int>> incms;
    map<Expr, int> expr_id;
    int qCHCNum;  // index of the query in chc
    int total_var_cnt = 0;
    ExprVector constructors;
    std::string infile;

    // Equivalence Check related
    std::vector<std::string>& fpreds_names;
    functionsInfo funcsInfo;
    CHCsGraph chc_graph;
    std::unordered_map<std::string, Expr> names_to_rel; // names to relation mapping
                                                          // (only used for ease of access)
    std::unordered_map<Expr, inlinedDefinition> preds_to_inlined_defs;
                                                // predicate to inlined definition mapping
    int variableCounter = 0;


      //ToDo: Remove or recheck later on; move from Horn.hpp
    int debug;

    CHCs(ExprFactory &efac, EZ3 &z3, std::string name, std::vector<std::string>& preds)
        : m_efac(efac), m_z3(z3), varname(name), fpreds_names(preds), funcsInfo(preds) {}

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }


    vector<HornRuleExt> getParents(HornRuleExt chc) {
      assert(std::find_if(chcs.begin(), chcs.end(), [chc](HornRuleExt comp) { return chc.body == comp.body; }) != chcs.end());
      if(chc.isFact) return {};
      auto parentsExpr = chc.srcRelations;
      vector<HornRuleExt> parents;
      for(HornRuleExt candidate: chcs){
        if(std::find(parentsExpr.begin(), parentsExpr.end(), candidate.dstRelation) != parentsExpr.end() &&
             candidate.dstRelation != chc.dstRelation){
          parents.push_back(candidate);
        }
      }
      return parents;
    }

    HornRuleExt getChild(HornRuleExt const chc) {
      assert(std::find_if(chcs.begin(), chcs.end(), [chc](HornRuleExt comp) { return chc.body == comp.body; }) != chcs.end());
      auto parentsExpr = chc.dstRelation;
      HornRuleExt child = *std::find_if(chcs.begin(), chcs.end(),
                                          [parentsExpr](HornRuleExt elem){
        return (std::find(elem.srcRelations.begin(), elem.srcRelations.end(), parentsExpr) != elem.srcRelations.end());
      });

      return child;
    }

    void splitBody (HornRuleExt& hr, ExprVector& srcVars, ExprSet& lin)
    {
      getConj (hr.body, lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FAPP>(cnj) && find(hr.locVars.begin(), hr.locVars.end(), cnj) == hr.locVars.end())
        {
          if(hr.body->arity() > 0) {
            assert(isOpX<FDECL>(cnj->left()));
            Expr rel = cnj->left();
            if (rel->arity() >= 2) {
              addDecl(rel);
              hr.srcRelations.push_back(rel->arg(0));
              for (auto it = cnj->args_begin() + 1; it != cnj->args_end(); ++it)
                srcVars.push_back(*it);
            }
            c = lin.erase(c);
          }
        }
        else ++c;
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->arg(0)].empty())
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          total_var_cnt++;
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY> (arg) && !isOpX<REAL_TY> (arg) && !isOpX<BOOL_TY> (arg) && !isOpX<ARRAY_TY> (arg) && !isOpX<AD_TY> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          Expr var;
          if (isOpX<INT_TY> (a->arg(i)))
              var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (a->arg(i)))
              var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (a->arg(i)))
              var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (a->arg(i)))
              var = bind::mkConst(new_name, mk<ARRAY_TY>(a->arg(i)->left(), a->arg(i)->right()));
          else if (isOpX<AD_TY>(a->arg(i))){
              ExprVector type;
              type.push_back(a->arg(i));
              var = bind::fapp(bind::fdecl (new_name, type));
          }
          else
              assert(0);
          invVars[a->arg(0)].push_back(var);
        }
      }
    }

    Expr normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return NULL;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return r;
    }

    bool hasOnlyInduct(Expr rel, vector<int>& indexes)
    {
      int num = 0;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].dstRelation == rel)
        {
          if (chcs[i].isFact)
          {
            indexes.clear();
            return false;
          }
          bool isInd = false;
          for (auto & c : chcs[i].srcRelations)
          {
            if (c == rel)
            {
              isInd = true;
              break;
            }
          }
          if (isInd)
          {
            indexes.push_back(i);
          }
          else
          {
            indexes.clear();
            return false;
          }
        }
      }
      return indexes.size() > 0;
    }

    void computeIncms()
    {
      incms.clear();
      for (int i = 0; i < chcs.size(); i++)
        incms[chcs[i].dstRelation].push_back(i);
    }

    void prune ()
    {
        int sz = decls.size();
        set<int> toSkip;
        computeIncms();

        for (auto it = decls.begin(); it != decls.end(); )
        {
          Expr d = *it;

          vector<int> indexes;
          bool toDel = hasOnlyInduct(d->left(), indexes);
          for (int i : indexes) toSkip.insert(i);

          if (toDel || incms[d->left()].empty())
          {
            toDel = true;
            for (int i = 0; i < chcs.size(); i++)
            {
              bool isInBody = false;
              for (auto & s : chcs[i].srcRelations)
              {
                if (s == d->left())
                {
                  isInBody = true;
                  break;
                }
              }
              if (isInBody)
              {
                toSkip.insert(i);
              }
            }
          }

          if (toDel) it = decls.erase(it);
          else ++it;
        }
        for (auto rit = toSkip.rbegin(); rit != toSkip.rend(); rit++) {
          chcs.erase(chcs.begin() + *rit);
        }

        if (sz == decls.size()) return;
        else prune();
    }


    Expr renamedClone(Expr origVar) {
        Expr name = mkTerm<string>(varname + "var_" + std::to_string(variableCounter++), m_efac);
        return cloneVar(origVar, name);
    }

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
        func.print();
    }


    void inlining() {
        for (auto &i : funcsInfo.getCallingOrder()) {
            auto &func = funcsInfo.getFunctions()[i];
            std::cout << "Inlining " << func.getName() << "\n";
            std::cout << "----------------------------------\n";
            inliningSingleFunction(func);
            std::cout << "----------------------------------\n\n";
        }
    }


    void computeCallGraph() {
        auto &functions = funcsInfo.getFunctions();
        if (functions.size() <= 1) {
            funcsInfo.addCallingOrder(0);
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
                        funcsInfo.addCall(i, j);
                    }
                    else if (found_trace2) {
                        funcsInfo.addCall(j, i);
                    }
                }
            }
            funcsInfo.findCallingOrder();
        }
        funcsInfo.callGraphToDotFile(std::string("../call_graph") + varname + ".dot");
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

    void initFunctionsInfo() {
        ExprSet processedExprs;
        for (auto &func : funcsInfo.getFunctions()) {
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
        for (auto &i : funcsInfo.getCallingOrder()) {
            auto &func = funcsInfo.getFunctions()[i];
            findSource(func.fpred_expr, func, processedExprs);
        }
        chc_graph.toDotFile(std::string("../chc_graph") + varname + ".dot", funcsInfo.getSinks(),
                            funcsInfo.getSources());
    }


    void renameVars() {
        for (int i = 0; i < chcs.size(); i++) {
            auto &chc = chcs[i];
            for (int j = 0; j < chc.srcRelations.size(); j++) {
                auto &src_vars = chc.srcVars[j];
                updateVarsAndBody(src_vars, chc.body, i);
            }
            updateVarsAndBody(chc.dstVars, chc.body, i);
            updateVarsAndBody(chc.locVars, chc.body, i, varname);
        }
    }


    void parse(std::string smt /*, std::string contract*/)
    {
      // GF: this entry part is different from the original implementation
      // (since the fixpoint format does not support ADTs)
//      Expr e = z3_from_smtlib_file (m_z3, smt_file);
//      for (auto & a : m_z3.getAdtConstructors()) {
//        constructors.push_back(regularizeQF(a));
//      }
//      ExprSet cnjs;
//      getConj(e, cnjs);
//      unitPropagation(cnjs);

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

//        filter (r, bind::IsConst(), inserter (origVrs, origVrs.begin()));
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
//
//          for (auto it = hr.head->args_begin()+1; it != hr.head->args_end(); ++it)
//            hr.dstVars.push_back(*it); // to be rewritten later
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
//        if (!)
//        {
//          outs() << "Removed: " << body << " => " << head << "\n";
//          it = chcs.erase(it);
//          continue;
//        }

        if (hr.srcRelations.size() == 0)
        {
          if (hasUninterp(body))
          {
            lin.clear();
          }
        }




//        if (isOpX<FAPP>(head))
//        {
//          if (head->arg(0)->arity() == 2 && !hr.isFact)
//          {
//            if (!addFailDecl(head->arg(0)->arg(0)))
//            {
//              it = chcs.erase(it);
//              continue;
//            }
//          }
//          else
//          {
//            addDecl(head->arg(0));
//          }
//          hr.head = head->arg(0);
//          hr.dstRelation = hr.head->arg(0);
//        }
//        else
//        {
//          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));
//
//          if (!addFailDecl(mk<FALSE>(m_efac)))
//          {
//            it = chcs.erase(it);
//            continue;
//          }
//          hr.dstRelation = mk<FALSE>(m_efac);
//        }


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
        // simplBoolReplCnj(allOrigSymbs, lin); // perhaps, not a very important optimization now; consider removing
        //        origDstSymbs = hr.dstVars;
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
        // outs() << "Chc: " << hr.body << " => " << hr.head << "\n";
      }

      for (int i = 0; i < chcs.size(); i++) {
        expr_id[chcs[i].dstRelation] = i;
        incms[chcs[i].dstRelation].push_back(i);
      }

//      for (int i = 0; i < chcs.size(); i++) {
//        outs() << "Chc " << i << " :" << chcs[i].body << " => "  << chcs[i].head << "\n";
//      }
      prune();

//      outs() << "Post pruning assignments: \n";
//      for (int i = 0; i < chcs.size(); i++) {
//        outs() << "Chc " << i << " :" << chcs[i].body  << "=>"  << chcs[i].head << "\n";
//      }


        // Keep the relevant CHCs
        std::set<std::string> processed;
        std::set<int> toKeep;
        std::vector<std::string> worklist = fpreds_names;
        for (size_t i = 0; i < worklist.size(); i++) {
            std::string p = worklist[i];
            if (processed.find(p) != processed.end()) continue;
            processed.insert(p);
            for (auto &d : decls) {
                if (lexical_cast<std::string>(d->left()).compare(p) == 0) {
                    names_to_rel[p] = d->left();
                    auto incms_for_p = incms[names_to_rel[p]];
                    toKeep.insert(incms_for_p.begin(), incms_for_p.end());
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
        std::vector<HornRuleExt> new_chcs;
        new_chcs.reserve(toKeep.size());
        for (auto &i : toKeep) {
            new_chcs.push_back(chcs[i]);
        }
        chcs = std::move(new_chcs);
        computeIncms();
        // might also need to update the decls
        renameVars();

        // Initialize the functions and function calls info
        initFunctionsInfo();


    /*
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
          outs () << "cycle found (#" << i << "):\n";
          print(chcs[i]);
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
          outs() << "fact found (#" << i << "):\n";
          print(chcs[i]);
          break;
        }
      }
    */
    }

    vector<vector<int>> cur_batch;
    void findCombs(int num, vector<vector<int>>& res)
    {
      if (num == 1)
      {
        for (int i : index_cycle_chc)
        {
          vector<int> v2 = {i};
          res.push_back(v2);
        }
      }
      else
      {
        findCombs(num - 1, res);
        vector<vector<int>> res2;
        for (auto & v : res)
        {
          for (int i : index_cycle_chc)
          {
            vector<int> v2 = v;
            v2.push_back(i);
            res2.push_back(v2);
          }
        }
        res = res2;
      }
    }

    int getNumQs()
    {
      int i = 0;
      for (auto & c : chcs)
        i += c.isQuery;
      return i;
    }

    std::tuple<bool, ExprVector> mkNewQuery(int cycl_num)
    {
      outs () << "  ***************   pop back the query ************\n";
      if (chcs.back().isQuery)
        chcs.pop_back(); // important: kill the query created in `mkNewQuery`
      outs () << "mkNewQuery: " << cur_batch.size() << "; chcs " << chcs.size() << "\n";

      if (cur_batch.empty())
      {
        outs () << "  cur_batch empt: " << cycl_num << "\n";
        findCombs(cycl_num, cur_batch);
      }

      // outs () << "to copy: " << cy.srcRelations[sum] << "\n";
      chcs.push_back(chcs[index_fact_chc]);
      auto & hr = chcs.back();
//      pprint(chcs.back().body);
      int loc = 0;
      ExprVector newbody;
      ExprVector& prevdst = chcs[index_fact_chc].dstVars;
      Expr prevbody = chcs[index_fact_chc].body;

      for (int i = 0; i < cycl_num; i++)
      {
        auto & cy = chcs[cur_batch.back()[i]];

        int sum = 0, tr = 0;
        for (; sum < cy.srcRelations.size(); sum++)
          if (cy.srcRelations[sum] != cy.dstRelation)
            break;
        for (; tr < cy.srcRelations.size(); tr++)
          if (cy.srcRelations[tr] == cy.dstRelation)
            break;
        ExprVector& cursrc = cy.srcVars[tr];

        // outs () << "\n\ncopy " << i << "\n";

        ExprMap repl1, repl2, repl3;
        for (int k = 0; k < prevdst.size(); k++)
        {
          auto newvar = mkTerm<string> ("_bnd" + to_string(loc), m_efac);
          newvar = cloneVar(prevdst[k], newvar);
          repl1[prevdst[k]] = newvar;
          repl2[cursrc[k]] = newvar;
          loc++;
        }
        for (int k = 0; k < cy.locVars.size(); k++)
        {
          auto newvar = mkTerm<string> ("_loc" + to_string(loc), m_efac);
          newvar = cloneVar(cy.locVars[k], newvar);
          repl2[cy.locVars[k]] = newvar;
          loc++;
        }
//        pprint(prevbody);
//        pprint(cy.body);
        prevbody = replaceAll(prevbody, repl1);
//        pprint(prevbody);
        newbody.push_back(prevbody);
        // pprint(prevbody);
        prevbody = replaceAll(cy.body, repl2);
//        pprint(prevbody);
        prevdst = cy.dstVars;

        hr.srcRelations.push_back(cy.srcRelations[sum]);
        hr.srcVars.push_back(ExprVector());
        ExprVector vars;
        for (auto & v : cy.srcVars[sum])
        {
          auto newvar = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          newvar = cloneVar(v, newvar);
          repl3[v] = newvar;
          hr.srcVars.back().push_back(newvar);
          total_var_cnt++;
        }
        prevbody = replaceAll(prevbody, repl3);
      }
      newbody.push_back(prevbody);
      hr.body = conjoin(newbody, m_efac);
//      pprint(chcs.back().body);
//      pprint(hr.body);
      hr.isQuery = 1;
      hr.isInductive = 0;
      hr.isFact = 0;
      hr.dstRelation = failDecl;
      hr.dstVars.clear();
      outs () << "   >>> new query:   ";
      ExprVector full_srcRelations = hr.srcRelations;
      pprint(hr.srcRelations);
      outs () << "\n";
//      if(full_srcRelations.size() > 2) {
//        hr.srcRelations = {full_srcRelations[full_srcRelations.size() - 1]};
//      }
      assert (!cur_batch.empty());
      cur_batch.pop_back();
      return {cur_batch.empty(), full_srcRelations};
    }

    void print_parse_results(){
      outs() << "chcs \n";
      for (int i = 0; i < chcs.size(); i++){
        outs() << i << " srs: ";
        for (int j = 0; j < chcs[i].srcRelations.size(); j++) {
          outs() << " " <<chcs[i].srcRelations[j]->getId();
        }
        outs() << " dst: " << chcs[i].dstRelation->getId() << " : "
        << chcs[i].dstRelation << " isQuery : " << chcs[i].isQuery << "\n";
      }
      for (auto i : index_cycle_chc)
        outs() << "index_cycle_chc : " << i << "\n";
      int i = 0;
      outs() << "decls \n";
      for (auto d: decls){
        outs() << i << " left: " << d->left()->getId() << " right: " << d->right()->getId() << "\n";
        i++;
      }
      i = 0;
      outs() << "expr_id \n";
      for (auto e: expr_id){
        outs() << i << " first: " << e.first->getId() << " second: " << e.second;
        outs() << "\n";
        i++;
      }
    }

      void unitPropagation(ExprSet &cnjs) {
        ExprMap matching;
        for  (auto &r: cnjs) {
          if (isOpX<NEG>(r) && r->arity() == 1 && !isOpX<FALSE>(r->left())) {
            matching[r->left()] = mk<FALSE>(m_efac);
          }
        }
        if (matching.empty()) {
          return;
        }
        else {
          ExprSet newCnjs;
          for  (auto &r: cnjs) {
            Expr r1 = replaceAll(r, matching);
            newCnjs.insert(r1);
          }
          cnjs = newCnjs;
          unitPropagation(cnjs);
        }
      }


      bool addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          //TODO:support
          // errs () << "Multiple queries are not supported\n";
          //exit(0);
          return false;
        }
      }
      return true;
    }

    Expr getPostcondition (int i)
    {
      HornRuleExt& hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
      for (auto & a : cnjs)
      {
        if (emptyIntersect(a, allVars)) newCnjs.insert(a);
      }
      return conjoin(newCnjs, m_efac);
    }


    void print(bool full = false)
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs) print(hr, full);
    }

    void print(HornRuleExt& hr, bool full = false)
    {
        if (hr.isFact) outs() << "  INIT:\n";
        if (hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    ";

        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          outs () << * hr.srcRelations[i];
          if (full)
          {
             outs () << " srcRelations: (";
              for(auto &a: hr.srcVars[i]) outs() << *a << ", ";
                outs () << "\b\b)";
          }
          outs () << " /\\ ";
        }
        outs () << "\b\b\b\b  [arity " << hr.srcRelations.size()<< "] -> " << * hr.dstRelation << "\n";

        if (full)
        {
          if (hr.dstVars.size() > 0)
          {
            outs () << " dstVars: (";
            for(auto &a: hr.dstVars) outs() << *a << ", ";
            outs () << "\b\b)";
          }
          outs() << "\n    body: " << * hr.body << "\n";

          if (hr.locVars.size() > 0)
          {
            outs () << " locVars: (";
            for(auto &a: hr.locVars) outs() << *a << ", ";
            outs () << "\b\b)\n";
          }
        }
    }

  };
}
#endif
