#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include <deque>

#include "ExtendedHorn.hpp"

namespace ufo
{
  // An implementation for paper "Synchronizing Constrained Horn Clauses",
  // https://easychair.org/publications/open/LlxW
  // by Dmitry Mordvinov and Grigory Fedyukovich

  /* 
   * Class defines a Product of two CHCs
   * that is required for Equivalence Checking of Programs
   */
  class ProductCHCs : public ExtendedCHCs
  {
    public:
      ExtendedCHCs* subRule1;
      ExtendedCHCs* subRule2;

      ProductCHCs(ExtendedCHCs &rules1, ExtendedCHCs &rules2, string n, int d = false) :
        ExtendedCHCs(rules1.m_efac, rules1.m_z3, n, d), subRule1(&rules1), subRule2(&rules2) {};

      Expr nonRecursiveProduct(HornRuleExt &chc1, HornRuleExt &chc2, ExprVector &vars)
      {
        ExprVector chc1NonRecPart, chc2NonRecPart;
        getNonRecurSrcRelations(chc1.srcRelation, chc1.dstRelation, chc1NonRecPart);
        getNonRecurSrcRelations(chc2.srcRelation, chc2.dstRelation, chc2NonRecPart);

        Expr product;
        if (!chc1NonRecPart.empty())
        {
          product = chc1NonRecPart[0];
          vars.insert(vars.end(), subRule1->invVars[product].begin(),
              subRule1->invVars[product].end());
          for (auto it = chc1NonRecPart.begin()+1; it != chc1NonRecPart.end(); it++)
          {
            Expr rel = *it;
            product = mk<AND>(product, rel);
            vars.insert(vars.end(), subRule1->invVars[rel].begin(), subRule1->invVars[rel].end());
          }
        }

        if (!chc2NonRecPart.empty())
        {
          Expr rel = chc2NonRecPart[0];
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
        return product;
      }


      void getNonRecurSrcRelations(Expr srcRelation, Expr dstRelation, ExprVector &partitions)
      {
        if (isOpX<AND>(srcRelation))
        {
          for (int i = 0; i < srcRelation->arity(); i++)
            getNonRecurSrcRelations(srcRelation->arg(i), dstRelation, partitions);
        }
        else if (!isOpX<TRUE>(srcRelation))
        {
          if (srcRelation != dstRelation)
            partitions.push_back(srcRelation);
        }
      }


      Expr RTransform(const HornRuleExt &chc, int ruleNum)
      {
        Expr decl;
        if (!chc.isInductive)
        {
          if (ruleNum == 0) decl = subRule1->getDeclByName(chc.dstRelation);
          else decl = subRule2->getDeclByName(chc.dstRelation);
          return bind::fapp(decl, chc.dstVars);
        }
        else
        {
          if (ruleNum == 0) decl = subRule1->getDeclByName(chc.srcRelation);
          else decl = subRule2->getDeclByName(chc.srcRelation);
          return bind::fapp(decl, chc.srcVars);
        }
      }


      Expr recursiveProduct(const HornRuleExt &chc1, const HornRuleExt &chc2, ExprVector &vars)
      {
        Expr transformed1 = RTransform(chc1, 0);
        Expr transformed2 = RTransform(chc2, 1);

        // might have to check if there are more than two relation symbols in transformed
        Expr rel1 = transformed1->left()->left();
        Expr rel2 = transformed2->left()->left();
        auto product = relationSymbolsProduct(rel1, rel2);

        // remove head(C) from body
        if (bind::fapp(transformed1->left(), chc1.dstVars) == transformed1
            && bind::fapp(transformed2->left(), chc2.dstVars) == transformed2)
        {
          product = NULL;
        }
        else
        {
          vars.insert(vars.end(), transformed1->args_begin()+1, transformed1->args_end());
          vars.insert(vars.end(), transformed2->args_begin()+1, transformed2->args_end());
          product = product->left();
        }
        return product;
      }


      void bodyProduct(HornRuleExt &chc1, HornRuleExt &chc2, HornRuleExt &newProductRule)
      {
        // non-recursive part product
        Expr nonRecursivePr = nonRecursiveProduct(chc1, chc2, newProductRule.srcVars);
        // recursive part product
        Expr recursivePr = recursiveProduct(chc1, chc2, newProductRule.srcVars);

        if (nonRecursivePr && recursivePr)
          newProductRule.srcRelation = mk<AND>(nonRecursivePr, recursivePr);
        else if (nonRecursivePr)
          newProductRule.srcRelation = nonRecursivePr;
        else if (recursivePr)
          newProductRule.srcRelation = recursivePr;
        else
          newProductRule.srcRelation = mk<TRUE>(m_efac);

        newProductRule.body = mk<AND>(chc1.body, chc2.body);
        newProductRule.isFact = (isOpX<TRUE>(newProductRule.srcRelation));
        newProductRule.isQuery = (newProductRule.dstRelation == failDecl);
        newProductRule.isInductive = (recursivePr != NULL);
      }


      /**
       * Calculates product of rules of given two predicates
       */
      vector<HornRuleExt> calculateProductOfRules(ExprVector predicates)
      {
        vector<HornRuleExt*> rules1, rules2;
        subRule1->rulesOfPredicate(predicates[0], rules1);
        subRule2->rulesOfPredicate(predicates[1], rules2);
        assert(rules1.size() == rules2.size());

        vector<HornRuleExt> rulesOfP;
        for (auto &r1 : rules1)
          for (auto &r2 : rules2)
            productOfCHCs(*r1, *r2, rulesOfP);

        return rulesOfP;
      }


      inline Expr stringProduct(Expr e1, Expr e2)
      {
        return mkTerm<string>(lexical_cast<string>(e1) + "*" + lexical_cast<string>(e2), m_efac);
      }


      HornRuleExt createProductQueries()
      {
        assert(subRule1->hasQuery && subRule2->hasQuery);
        auto query1 = subRule1->getQuery();
        auto query2 = subRule2->getQuery();

        HornRuleExt queryPr;
        queryPr.body = mk<AND>(query1->body, query2->body);
        queryPr.srcRelation = mk<AND>(query1->srcRelation, query2->srcRelation);
        queryPr.dstRelation = stringProduct(query1->dstRelation, query2->dstRelation);

        // queries do not have dstVars
        queryPr.dstVars = ExprVector{};
        concatenateVectors(queryPr.srcVars, query1->srcVars, query2->srcVars);
        concatenateVectors(queryPr.locVars, query1->locVars, query2->locVars);

        queryPr.isFact = false;
        queryPr.isQuery = true;
        queryPr.isInductive = false;
        hasQuery = true;
        if (!failDecl) addFailDecl(queryPr.dstRelation);

        return queryPr;
      }


      Expr relationSymbolsProduct(Expr rel1, Expr rel2)
      {
        Expr decl1 = subRule1->getDeclByName(rel1);
        Expr decl2 = subRule2->getDeclByName(rel2);
        ExprVector productTypes;
        productTypes.insert(productTypes.end(), decl1->args_begin()+1,
            decl1->args_begin()+decl1->arity()-1);
        productTypes.insert(productTypes.end(), decl2->args_begin()+1,
            decl2->args_begin()+decl2->arity()-1);
        productTypes.push_back(mk<BOOL_TY>(m_efac));
        Expr productRel = stringProduct(rel1, rel2);
        return bind::fdecl(productRel, productTypes);
      }


      /**
       * Calculates product of two CHCs
       */
      void productOfCHCs(HornRuleExt &chc1, HornRuleExt &chc2, vector<HornRuleExt> &rulesOfP)
      {
        // GF: use the global `debug` option for all such prints
        outs () << "  product of two CHCs: "
          << chc1.srcRelation << " -> " << chc1.dstRelation << " and "
          << chc2.srcRelation << " -> " << chc2.dstRelation << "\n";

        HornRuleExt newProductRule;
        // head product
        auto head = relationSymbolsProduct(chc1.dstRelation, chc2.dstRelation);
        newProductRule.dstRelation = head->left();
        concatenateVectors(newProductRule.dstVars, chc1.dstVars, chc2.dstVars);

        // body product
        bodyProduct(chc1, chc2, newProductRule);

        concatenateVectors(newProductRule.locVars, chc1.locVars, chc2.locVars);

        // do not push if one is inductive and other one is not. Push in all other cases
        if ((newProductRule.isInductive && chc1.isInductive && chc2.isInductive)
            || !newProductRule.isInductive)
          rulesOfP.push_back(newProductRule);
      }

      /**
       * renames variables from _v1_ and _v2_ to _pr_ variables for all the CHCs
       */
      void assignVarsAndRewrite()
      {
        for (auto &chc : chcs)
        {
          // might add dstVars of one of the CHCs to product locVars twice in some cases,
          // should not be a problem
          concatenateVectors(chc.locVars, chc.srcVars, chc.dstVars);
          chc.origSrc = chc.srcVars; chc.origDst = chc.dstVars;

          chc.srcVars.clear(); chc.dstVars.clear();
          chc.assignVarsAndRewrite(invVars[chc.srcRelation], invVarsPrime[chc.dstRelation]);
          chc.body = mk<AND>(chc.body, conjoin(chc.lin, m_efac));
        }
      }


      /**
       * generates the product CHC system of two CHC systems
       */
      void createProduct()
      {
        auto *query1 = subRule1->getQuery(), *query2 = subRule2->getQuery();
        std::deque<HornRuleExt> worklist(1, createProductQueries());
        while (!worklist.empty())
        {
          auto currentRule = worklist.front();
          worklist.pop_front();

          // AH: In the original algorithm, the operation PARTITION is used that is defined:
          // 'operator partition from a set to a set of its disjoint subsets'
          // Here, just one partition created of two symbols because there are only two
          // relation symbols here
          ExprVector partition;
          // getting non-recursive parts of the srcrelation
          getNonRecurSrcRelations(currentRule.srcRelation, currentRule.dstRelation, partition);

          Expr freshP;
          if (partition.size() >= 2)
          {
            // take product of relation symbols in partition,
            // true specified if product of rules of relations is to be calculated
            freshP = relationSymbolsProduct(partition[0], partition[1]);
            currentRule.srcRelation = freshP->left();

            auto rulesOfP = calculateProductOfRules(partition);
            worklist.insert(worklist.end(), rulesOfP.begin(), rulesOfP.end());
          }

          if (!isOpX<AND>(currentRule.srcRelation))
          {
            // if freshP is not NULL, it went into the if-statement (partition.size() >= 2)
            if (freshP) addDecl(freshP);
            chcs.push_back(std::move(currentRule));
          }
        }

        // changes variables from _v1_ and _v2_ prefixes to _pr_ with necessary changes
        assignVarsAndRewrite();
        findCycles();
        loopRel = loopheads[0];
        // prepare a version of wtoCHCs w/o queries
        dwtoCHCs = wtoCHCs;
        for (auto it = dwtoCHCs.begin(); it != dwtoCHCs.end();)
          if ((*it)->isQuery) it = dwtoCHCs.erase(it);
          else ++it;


        outs() << "\n--------------------------CALCULATING PRODUCT DONE-----------------------------\n\n";
      }
  };
}

#endif
