#ifndef HELPER__HPP__
#define HELPER__HPP__

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

  template <typename T>
  void setUnion(set<T> &result, set<T> set1, set<T> set2)
  {
    result = set1;
    result.insert(set2.begin(), set2.end());
  }

  template <typename T, typename T1>
  void concatenateMaps(map<T, T1> &result, map<T, T1> map1, map<T, T1> map2)
  {
    result = map1;
    result.insert(map2.begin(), map2.end());
  }

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

    void renameFdecl(Expr &fdecl, string varname)
    {
      Expr name;
      ExprVector args;
      if (isOpX<FDECL>(fdecl))
      {
        name = mkTerm<string> (varname + lexical_cast<string>(fdecl->arg(0)), fdecl->getFactory());
        for (auto it = fdecl->args_begin()+1; it != fdecl->args_end(); it++)
        {
          args.push_back(*it);
        }
        fdecl = bind::fdecl(name, args);
      }
    }

    void renameVars(ExprVector& vars, Expr& body, string varname)
    {
      for (int i = 0; i < vars.size(); i++)
      {
        Expr decl = vars[i]->arg(0);
        renameFdecl(decl, varname);
        body = replaceAll(body, bind::fapp(vars[i]->arg(0)), bind::fapp(decl));
        vars[i] = bind::fapp(decl);
      }
    }
}


#endif
