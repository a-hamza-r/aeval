#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"
#include "RndLearnerV2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

    void equivalenceTask(vector<HornRuleExt> &chcs1, vector<HornRuleExt> &chcs2, ExprFactory &m_efac)
    {
        // getInductiveRules(chcs1, chcs2);

        // learnInvariants2(ruleManagerDst, NULL, 2000000, 0, 3, 3, false, false);
        ExprVector candidates;
        
        ExprVector srcArrayVars1, dstArrayVars1, srcArrayVars2, dstArrayVars2;
        ExprVector srcBvVars1, dstBvVars1, srcBvVars2, dstBvVars2;
        ExprVector srcBoolVars1, dstBoolVars1, srcBoolVars2, dstBoolVars2;
        for (int i = 0; i < chcs1.size(); i++) {
            if (chcs1[i].isInductive && chcs2[i].isInductive)
            {
                chcs1[i].getTypeVars<ARRAY_TY>(srcArrayVars1, dstArrayVars1);
                chcs1[i].getTypeVars<BVSORT>(srcBvVars1, dstBvVars1);
                chcs1[i].getTypeVars<BOOL_TY>(srcBoolVars1, dstBoolVars1);

                chcs2[i].getTypeVars<ARRAY_TY>(srcArrayVars2, dstArrayVars2);
                chcs2[i].getTypeVars<BVSORT>(srcBvVars2, dstBvVars2);
                chcs2[i].getTypeVars<BOOL_TY>(srcBoolVars2, dstBoolVars2);

                for (auto it = srcBvVars1.begin(); it != srcBvVars1.end(); it++) {
                    errs() << **it << ", its type: " << *bind::typeOf(*it) << "\n";
                    errs() << bv::width(bind::typeOf(*it)) << "\n";
                    // errs() << bv::width(*it) << "\n";
                }


                // int numBvToCmp = srcBvVars.size() - srcArrayVars.size();
                Expr pre = mk<TRUE>(m_efac);
                for (auto it = srcBvVars1.begin(); it != srcBvVars1.end(); it++)
                {
                    for (auto it2 = srcBvVars2.begin(); it2 != srcBvVars2.end(); it2++)
                    {
                        pre = mk<AND>(pre, mk<EQ>(*it, *it2));
                    }
                }

                Expr post = mk<TRUE>(m_efac);
                for (auto it = dstBvVars1.begin(); it != dstBvVars1.end(); it++)
                {
                    for (auto it2 = dstBvVars2.begin(); it2 != dstBvVars2.end(); it2++)
                    {
                        post = mk<AND>(post, mk<EQ>(*it, *it2));
                    }
                }
                post = mk<NEG>(post);

                errs() << "post: " << *post << "\n";

                for (auto it = srcArrayVars1.begin(); it != srcArrayVars1.end(); it++)
                {
                    for (auto it2 = srcArrayVars2.begin(); it2 != srcArrayVars2.end(); it2++)
                    {
                        // pre = mk<AND>(post, )
                    }
                }
            }
        }
    }


    void headProduct(ExprSet &predicates, Expr &product, ExprFactory &m_efac)
    {
        Expr rel, productRel = mkTerm<string>("", m_efac);
        ExprVector productTypes;

        for (auto it = predicates.begin(); it != predicates.end(); it++)
        {
            rel = *it;
            if (!isFdecl(rel) || rel->arity() < 2) {
                product = NULL;
                return;
            }

            productRel = mkTerm<string> (lexical_cast<string>(productRel)+lexical_cast<string>(rel->arg(0))+"*", m_efac);
            for (int i = 1; i < (rel)->arity()-1; i++) 
                productTypes.push_back(rel->arg(i));
        }
        productTypes.push_back(mk<BOOL_TY>(m_efac));

        product = bind::fdecl (productRel, productTypes);
    }

    
    void constraintProduct(vector<HornRuleExt> &chcs, Expr &product, ExprFactory &m_efac)
    {
        product = mk<TRUE>(m_efac);
        for (auto it = chcs.begin(); it != chcs.end(); it++)
        {
            product = mk<AND>(product, it->body);
        }
        errs() << "constraintProduct: " << *product << "\n";
    }


    void nonRecursiveProduct(vector<HornRuleExt> &chcs, Expr &product, ExprFactory &m_efac)
    {
        Expr fapp;
        product = mk<TRUE>(m_efac);
        for (auto it = chcs.begin(); it != chcs.end(); it++)
        {
            if (!it->isFact && !it->isInductive)
            {
                fapp = bind::fapp(it->srcRelationDecl, it->srcVars);
                product = mk<AND>(product, fapp);
            }
        }
        errs() << "nonRecursiveProduct: " << *product << "\n";
    }


    void RTransform(HornRuleExt &chc)
    {
        if (!chc.isInductive)
        {

        }
    }


    void recursiveProduct(vector<HornRuleExt> &chcs, Expr &product, ExprFactory &m_efac)
    {

    }

    
    void bodyProduct(CHCs &rules, Expr &product, ExprFactory &m_efac)
    {
        Expr constraintPr, recursivePr, nonRecursivePr;
        constraintProduct(rules.chcs, constraintPr, m_efac);
        nonRecursiveProduct(rules.chcs, nonRecursivePr, m_efac);
        recursiveProduct(rules.chcs, recursivePr, m_efac);

        // product = constraintPr;
    }


    void Product(CHCs &product, CHCs &rules1, CHCs &rules2)
    {
	    Expr headPr;
	    Expr bodyPr;

        headProduct(rules1.decls, headPr, m_efac);
        errs() << *headPr << "\n";

        bodyProduct(rules1, bodyPr, m_efac);
        errs() << *bodyPr << "\n";

    }


	inline void createProduct(const char * chcfileSrc, const char * chcfileDst)
  	{
    	ExprFactory m_efac;
	    EZ3 z3(m_efac);

	    CHCs ruleManagerSrc(m_efac, z3, "_v1_");
	    ruleManagerSrc.parse(string(chcfileSrc));

	    CHCs ruleManagerDst(m_efac, z3, "_v2_");
	    ruleManagerDst.parse(string(chcfileDst));

	    for (auto it = ruleManagerSrc.chcs.begin(); it != ruleManagerSrc.chcs.end(); it++) {
	    	it->printMemberVars();
	    }

		for (auto it = ruleManagerDst.chcs.begin(); it != ruleManagerDst.chcs.end(); it++) {
	    	it->printMemberVars();
	    }

	    // auto chcs1 = ruleManagerSrc.chcs;
	    // auto chcs2 = ruleManagerDst.chcs;

	    // equivalenceTask(chcs1, chcs2, m_efac);

        CHCs ruleManagerProduct(m_efac, z3, "_pr_");

	    Product(ruleManagerProduct, ruleManagerSrc, ruleManagerDst);
  };
}

#endif
