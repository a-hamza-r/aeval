#ifndef PRODUCT__HPP__
#define PRODUCT__HPP__

#include "Horn.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

	template <typename O> ExprVector getTypeVars(Expr &varsDecl, ExprVector &vars)
	{
		ExprVector varsWithType;
		int i = 0;
		for (auto it = varsDecl->args_begin()+1; it != varsDecl->args_end()-1; it++) {
				errs() << **it << "\n";
			if (isOpX<O>(*it)) {
				varsWithType.push_back(vars[i]);
			}
			i++;
		}
		return varsWithType;
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

    auto chcs1 = ruleManagerSrc.chcs;
    auto chcs2 = ruleManagerDst.chcs;
    
    for (int i = 0; i < chcs1.size(); i++) {
    	if (chcs1[i].isInductive && chcs2[i].isInductive)
    	{
    		ExprVector srcArrayVars1 = getTypeVars<ARRAY_TY>(chcs1[i].srcRelationFdecl, chcs1[i].srcVars);
    		ExprVector dstArrayVars1 = getTypeVars<ARRAY_TY>(chcs1[i].dstRelationFdecl, chcs1[i].dstVars);
    		ExprVector srcBvVars1 = getTypeVars<BVSORT>(chcs1[i].srcRelationFdecl, chcs1[i].srcVars);
    		ExprVector dstBvVars1 = getTypeVars<BVSORT>(chcs1[i].dstRelationFdecl, chcs1[i].dstVars);

    		ExprVector srcArrayVars2 = getTypeVars<ARRAY_TY>(chcs2[i].srcRelationFdecl, chcs2[i].srcVars);
    		ExprVector dstArrayVars2 = getTypeVars<ARRAY_TY>(chcs2[i].dstRelationFdecl, chcs2[i].dstVars);
    		ExprVector srcBvVars2 = getTypeVars<BVSORT>(chcs2[i].srcRelationFdecl, chcs2[i].srcVars);
    		ExprVector dstBvVars2 = getTypeVars<BVSORT>(chcs2[i].dstRelationFdecl, chcs2[i].dstVars);

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


  };
}

#endif
