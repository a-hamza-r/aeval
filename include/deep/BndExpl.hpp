#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "Distribution.hpp"
#include "ae/AeValSolver.hpp"
#include <limits>

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    Expr extraLemmas;

    ExprVector bindVars1;

    int tr_ind; // helper vars
    int pr_ind;
    int k_ind;

    Expr inv;   // 1-inductive proof

    public:

    BndExpl (CHCs& r) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

    BndExpl (CHCs& r, Expr lms) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac), extraLemmas(lms) {}

    void guessRandomTrace(vector<int>& trace)
    {
      std::srand(std::time(0));
      Expr curRel = mk<TRUE>(m_efac);

      while (curRel != ruleManager.failDecl)
      {
        int range = ruleManager.outgs[curRel].size();
        int chosen = guessUniformly(range);
        int chcId = ruleManager.outgs[curRel][chosen];
        curRel = ruleManager.chcs[chcId].dstRelation;
        trace.push_back(chcId);
      }
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace, vector<vector<int>>& traces)
    {
      if (len == 1)
      {
        for (auto a : ruleManager.outgs[src])
        {
          if (ruleManager.chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : ruleManager.outgs[src])
        {
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(ruleManager.chcs[a].dstRelation, dst, len-1, newtrace, traces);
        }
      }
    }

    Expr compactPrefix (int num)
    {
      vector<int>& pr = ruleManager.prefixes[num];
      if (pr.size() == 0) return mk<TRUE>(m_efac);

      Expr pref = toExpr(pr);
      ExprSet quantified;
      filter (pref, bind::IsConst(), inserter (quantified, quantified.begin ()));
      for (auto & a : bindVars.back()) quantified.erase(a);
      pref = simpleQE(pref, quantified);
      return replaceAll(pref, bindVars.back(), ruleManager.chcs[ruleManager.cycles[num][0]].srcVars);
    }

    vector<ExprVector> bindVars;

    Expr toExpr(vector<int>& trace)
    {
      ExprVector ssa;
      getSSA(trace, ssa);
      return conjoin(ssa, m_efac);
    }

    void getSSA(vector<int>& trace, ExprVector& ssa)
    {
      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = ruleManager.chcs[trace[0]].srcVars;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int s = 0; s < trace.size(); s++)
      {
        auto &step = trace[s];
        bindVars2.clear();
        HornRuleExt& hr = ruleManager.chcs[step];
        Expr body = hr.body;
        if (!hr.isFact && extraLemmas != NULL) body = mk<AND>(extraLemmas, body);

        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          body = replaceAll(body, hr.srcVars[i], bindVars1[i]);
        }

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < hr.srcVars.size(); j++)
          {
            if (hr.dstVars[i] == hr.srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr.dstVars[i],new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        if (!hr.isQuery)
        {
          for (int i = 0; i < hr.locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr.locVars[i], new_name);

            body = replaceAll(body, hr.locVars[i], var);
          }
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }
    }

    bool exploreTraces(int cur_bnd, int bnd, bool print = false)
    {
      bool unsat = true;
      int num_traces = 0;

      if (print) outs () << "Exploring traces (up to bound): 1";     // GF: trace of length 1 is always empty
      while (unsat && cur_bnd <= bnd)
      {
        if (print) outs () << ", " << cur_bnd;
        vector<vector<int>> traces;
        vector<int> empttrace;

        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, cur_bnd++, vector<int>(), traces);

        for (auto &a : traces)
        {
          num_traces++;
          unsat = bool(!u.isSat(toExpr(a)));
          if (!unsat) break;
        }
      }

      if (print)
        outs () << "\nTotal number of traces explored: " << num_traces << "\n\n"
              << (unsat ? "UNSAT for all traces up to " : "SAT for a trace with ")
              << (cur_bnd - 1) << " steps\n";
      return unsat;
    }

    void exploreTracesCost(string init_cost, string final_cost, int unrolling)
    {
      Expr init_cost_var, final_cost_var;
      // find var:
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          for (int i = 0; i < hr.locVars.size(); i++)
          {
            if (lexical_cast<string>(hr.locVars[i]) == init_cost)
            {
              init_cost_var = hr.locVars[i];
            }
            if (lexical_cast<string>(hr.locVars[i]) == final_cost)
            {
              final_cost_var = hr.locVars[i];
            }
          }
        }
      }
      if (init_cost_var == NULL)
      {
        outs () << "Unable to locate cost var (" << init_cost << ")\n";
        exit(0);
      }

      if (final_cost_var == NULL)
      {
        outs () << "Unable to locate cost var (" << final_cost << ")\n";
        exit(0);
      }

      Expr init_assm = mk<EQ>(init_cost_var, bv::bvnum(0, bv::width(init_cost_var->first()->arg(1)), m_efac));
      outs () << " init_assm = " << *init_assm << "\n";

      int bnd = 1;
      // unrolling: number of unrollings of the loops 
      while (bnd < unrolling)
      {
        vector<vector<int>> traces;
        vector<int> empttrace;

        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, bnd, vector<int>(), traces);
        
        for (auto &a : traces)
        {
          outs () << "unrolling [ true";
          for (int i = 1; i < a.size(); i++) outs () << " -> " << *ruleManager.chcs[a[i]].srcRelation;
          outs () << " -> " << *ruleManager.chcs[a.back()].dstRelation << "]: ";

          if (!u.isSat(toExpr(a), init_assm))
          {
            outs () << "UNSAT\n";

            /*outs () << "UNSAT -- exiting\n";
            return;*/
          }
          else
          {
            outs () << "final_cost = " << *u.getMaxModel(final_cost_var) << "\n";
          }
        }
        bnd++;
      }
    }

    bool kIndIter(int bnd1, int bnd2)
    {
      assert (bnd1 <= bnd2);
      assert (bnd2 > 1);
      bool init = exploreTraces(bnd1, bnd2);
      if (!init)
      {
        outs() << "Base check failed at step " << bnd2 << "\n";
        exit(0);
      }

      k_ind = ruleManager.chcs.size(); // == 3

      for (int i = 0; i < k_ind; i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
      }

      ruleManager.chcs.push_back(HornRuleExt());   // trick for now: a new artificial CHC
      HornRuleExt& hr = ruleManager.chcs[k_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      hr.srcVars = tr.srcVars;
      hr.dstVars = tr.dstVars;
      hr.locVars = tr.locVars;

      hr.body = mk<AND>(tr.body, mkNeg(pr.body));

      if (extraLemmas != NULL) hr.body = mk<AND>(extraLemmas, hr.body);

      for (int i = 0; i < hr.srcVars.size(); i++)
      {
        hr.body = replaceAll(hr.body, pr.srcVars[i], hr.srcVars[i]);
      }

      vector<int> gen_trace;
      for (int i = 1; i < bnd2; i++) gen_trace.push_back(k_ind);
      gen_trace.push_back(pr_ind);
      Expr q = toExpr(gen_trace);
      bool res = bool(!u.isSat(q));

      if (bnd2 == 2) inv = mkNeg(pr.body);

      // prepare for the next iteration
      ruleManager.chcs.erase (ruleManager.chcs.begin() + k_ind);

      return res;
    }

    Expr getInv() { return inv; }

    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      int fc_ind;
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
        if (r.isFact) fc_ind = i;
      }

      HornRuleExt& fc = ruleManager.chcs[fc_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      Expr prop = pr.body;
      Expr init = fc.body;
      for (int i = 0; i < tr.srcVars.size(); i++)
      {
        init = replaceAll(init, tr.dstVars[i],  tr.srcVars[i]);
      }

      Expr itp;

      if (k == 0)
      {
        itp = getItp(init, prop);
      }
      else
      {
        vector<int> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr_ind);

        Expr unr = toExpr(trace);
        for (int i = 0; i < pr.srcVars.size(); i++)
        {
          prop = replaceAll(prop, pr.srcVars[i], bindVars.back()[i]);
        }
        itp = getItp(unr, prop);
        if (itp != NULL)
        {
          for (int i = 0; i < pr.srcVars.size(); i++)
          {
            itp = replaceAll(itp, bindVars.back()[i], pr.srcVars[i]);
          }
        }
        else
        {
          itp = getItp(init, mk<AND>(unr, prop));
        }
      }
      return itp;
    }

    //used for multiple loops to unroll inductive clauses k times and collect corresponding models
    bool unrollAndExecuteMultiple(
          map<Expr, ExprVector>& src_vars,
				  map<Expr, vector<vector<double> > > & models, int k = 10, Expr initVals=NULL)
    {
      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      map<int, bool> chcsConsidered;
      map<int, Expr> exprModels;

      for (int i = 0; i < ruleManager.cycles.size(); i++)
      {
        vector<int> mainInds;
        vector<int> arrInds;
        auto & loop = ruleManager.cycles[i];
        Expr srcRel = ruleManager.chcs[loop[0]].srcRelation;
        if (models[srcRel].size() > 0) continue;

        auto& hr = ruleManager.chcs[loop[0]];
        ExprVector vars;
        for (int j = 0; j < ruleManager.chcs[loop[0]].srcVars.size(); j++)
        {
          Expr var = ruleManager.chcs[loop[0]].srcVars[j];
          // errs() << "var: " << *var << "\n";
          if (bind::isIntConst(var))
          {
            mainInds.push_back(j);
            vars.push_back(var);
          }
          else if (isConst<ARRAY_TY> (var) && ruleManager.hasArrays[srcRel])
          {
            vars.push_back(mk<SELECT>(var, ruleManager.chcs[loop[0]].srcVars[ruleManager.iterator[srcRel]]));
            // Expr ind;
            // if (!ruleManager.arrayStores[i][j].empty())
            //   ind = ruleManager.arrayStores[i][j].back();
            // else
            //   ind = ruleManager.arraySelects[i][j].back();
            // errs() << "ind for array " << *ruleManager.chcs[i].srcVars[j] << " is " << *ind << "\n";
            // vars.push_back(mk<SELECT>(var, ind));
            mainInds.push_back(-1);
            arrInds.push_back(j);
          }
        }

        if (vars.size() < 2 && i == ruleManager.cycles.size() - 1)
          continue; // does not make much sense to run with only one var when it is the last cycle
        src_vars[srcRel] = vars;

        auto & prefix = ruleManager.prefixes[i];
        vector<int> trace;
        Expr lastModel = mk<TRUE>(m_efac);

        // if initVals is not empty, we do not add prefixes
        // if (!initVals)
        {
          for (int p = 0; p < prefix.size(); p++)
          {
            if (chcsConsidered[prefix[p]] == true)
            {
              Expr lastModelTmp = exprModels[prefix[p]];
              if (lastModelTmp != NULL) lastModel = lastModelTmp;
              trace.clear(); // to avoid CHCs at the beginning
            }
            trace.push_back(prefix[p]);
          }
        }

        int l = trace.size() - 1; // starting index (before the loop)
        if (ruleManager.hasArrays[srcRel]) l++; // first iter is usually useless

        for (int j = 0; j < k; j++)
          for (int m = 0; m < loop.size(); m++)
            trace.push_back(loop[m]);

        int backCHC = -1;
        for (int i = 0; i < ruleManager.chcs.size(); i++)
        {
          auto & r = ruleManager.chcs[i];
          if (i != loop[0] && !r.isQuery && r.srcRelation == srcRel)
          {
            backCHC = i;
            chcsConsidered[i] = true; // entry condition for the next loop
            trace.push_back(i);
            break;
          }
        }

        ExprVector ssa;
        getSSA(trace, ssa);

        // errs() << "Ssa 0: " << *ssa[0] << "\n";

        // might not work if trace has more than one prefixes
        if (initVals) 
        {
          // ssa[0] = mk<AND>(ssa[0], initVals);
          ssa[0] = replaceAll(initVals, ruleManager.chcs[loop[0]].dstVars, bindVars[0]);
        }
        // errs() << "ssa: \n";
        // for (auto it : ssa) errs() << *it << "\n";
        bindVars.pop_back();
        int traceSz = trace.size();

        bool toContinue = false;
        while (true)
        {
          if (ssa.size() < 2)
          {
            errs () << "Unable to find a suitable unrolling for " << *srcRel << "\n";
            toContinue = true;
            break;
          }

          if (u.isSat(lastModel, conjoin(ssa, m_efac)))
          {
            if (backCHC != -1 && trace.back() != backCHC &&
                trace.size() != traceSz - 1) // finalizing the unrolling (exit CHC)
            {
              trace.push_back(backCHC);
              ssa.clear();                           // encode from scratch
              getSSA(trace, ssa);
              bindVars.pop_back();
            }
            else break;
          }
          else
          {
            if (trace.size() == traceSz)
            {
              trace.pop_back();
              ssa.pop_back();
              bindVars.pop_back();
            }
            else
            {
              trace.resize(trace.size()-loop.size());
              ssa.resize(ssa.size()-loop.size());
              bindVars.resize(bindVars.size()-loop.size());
            }
          }
        }

        if (toContinue) continue;
        for (; l < bindVars.size(); l = l + loop.size())
        {
          vector<double> model;
         outs () << "model for " << l << ": [";
          int ai = 0;
          bool toSkip = false;
          for (int j = 0; j < vars.size(); j++) {
            int var = mainInds[j];
            Expr bvar;
            if (var >= 0)
            {
              if (ruleManager.hasArrays[srcRel])
                bvar = bindVars[l-1][var];
              else
                bvar = bindVars[l][var];
            }
            else
            {
              // Expr ind = replaceAll(vars[j]->arg(1), ruleManager.chcs[loop[0]].srcVars, bindVars[l-1]);
              // bvar = mk<SELECT>(bindVars[l][arrInds[ai]], ind);
              bvar = mk<SELECT>(bindVars[l][arrInds[ai]], bindVars[l-1][ruleManager.iterator[srcRel]]);
              ai++;
            }
            Expr m = u.getModel(bvar);
            double value;
            if (m == bvar) value = 0;
            else
            {
              if (lexical_cast<cpp_int>(m) > max_double ||
                  lexical_cast<cpp_int>(m) < -max_double)
              {
                toSkip = true;
                break;
              }
              value = lexical_cast<double>(m);
            }
            model.push_back(value);
           outs () << *bvar << " = " << *m << ", ";
          }
         outs () << "\b\b]\n";
          if (!toSkip) models[srcRel].push_back(model);
        }

        // although we care only about integer variables for the matrix above,
        // we still keep the entire model to bootstrap the model generation for the next loop
        if (chcsConsidered[trace.back()])
          exprModels[trace.back()] = replaceAll(u.getModel(bindVars.back()),
            bindVars.back(), ruleManager.chcs[trace.back()].srcVars);
      }
      return true;
    }

    bool unrollAndExecute(const Expr & invRel, vector<vector<double> > & models, int k = 10, Expr initCondn = nullptr)
    {
      int initIndex;
      int trIndex;
      bool initFound = false;

      for (int i = 0; i < ruleManager.chcs.size(); i++) {
        auto & r = ruleManager.chcs[i];
        if (r.isFact) {
          initIndex = i;
          initFound = true;
        }
        if (r.isInductive && r.srcRelation == invRel && r.dstRelation == invRel) {
          trIndex = i;
        }
      }

      if (!initFound && initCondn == nullptr) {
        cout << "ERR: init not found for given transition (index: " << trIndex << ")" << endl;
        return false;
      }

      Expr init = initCondn == nullptr ? ruleManager.chcs[initIndex].body : initCondn;

      HornRuleExt& tr = ruleManager.chcs[trIndex];

      for (int i = 0; i < tr.srcVars.size(); i++) {
        init = replaceAll(init, tr.dstVars[i], tr.srcVars[i]);
      }


      vector<int> trace;
      for (int i = 0; i < k; i++) {
        trace.push_back(trIndex);
      }

      Expr unrolledTr = toExpr(trace);

      //      cout << init << " && " << unrolledTr << endl;

      if (!u.isSat(init, unrolledTr)) {
        cout << init << " && " << unrolledTr << "\nfound to be unsat\n";
        return false;
      }

      for (auto vars : bindVars) {
        vector<double> model;
        for (auto var : vars) {
          double value = lexical_cast<double>(u.getModel(var));
          cout << value << "\t";//DEBUG
          model.push_back(value);
        }
        cout << endl;//DEBUG
        models.push_back(model);
      }

      return true;
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(ruleManager);
    ds.exploreTraces(bnd1, bnd2, true);
  };

  inline void getCost(string smt, string init_cost, string final_cost, int unrolling)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(ruleManager);
    ds.exploreTracesCost(init_cost, final_cost, unrolling);
  };

  inline bool kInduction(CHCs& ruleManager, int bnd)
  {
    if (ruleManager.chcs.size() != 3)
    {
      outs () << "currently not supported\n";
      return false;
    }

    BndExpl ds(ruleManager);

    bool success = false;
    int i;
    for (i = 2; i < bnd; i++)
    {
      if (ds.kIndIter(i, i))
      {
        success = true;
        break;
      }
    }

    outs () << "\n" <<
      (success ? "K-induction succeeded " : "Unknown result ") <<
      "after " << (i-1) << " iterations\n";

    return success;
  };

  inline void kInduction(string smt, int bnd)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    kInduction(ruleManager, bnd);
  };
}

#endif
