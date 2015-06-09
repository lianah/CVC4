/*********************                                                        */
/*! \file generated_ecodings.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Automatically generated encodings and other optimal encodings.
 **
 ** Implementation of bitblasting functions for various operators.
 **/

#ifndef __CVC4__GENERATED__ENCODINGS_H
#define __CVC4__GENERATED__ENCODINGS_H

#include "cvc4_private.h"
#include "expr/node.h"
#include "theory/bv/bitblast_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "prop/cnf_stream.h"
#include "theory/bv/options.h"

#include <ostream>
#include <cmath>

namespace CVC4 {

namespace theory {
namespace bv {

/******************************
* Reference encodings   
*    
*****************************/
  
template <class T>
T inline optimalUltGadget(const T &a,
			  const T &b,
			  const T &rest,
			  CVC4::prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalUltGadget<T> dummy" << std::endl;
  T eq = mkIff(a,b);
  return mkIte(eq, rest, mkNot(a));
}

template <>
Node optimalUltGadget(const Node &a,
			     const Node &b,
			     const Node &rest,
			     CVC4::prop::CnfStream* cnf);
 
 
template <class T>
T inline optimalSignGadget (const T& a, const T& b, const T &aLTbRec,
			      CVC4::prop::CnfStream* cnf) {
  // an and bn are the most significant bits
  // aLTb is the variable representing ULT(a[n-2:0], b[n-2:0])

  T neg_pos = mkAnd(a, mkNot(b));
  T aEQb = mkIff(a,b);
  T res = mkOr(neg_pos,
	       (mkAnd(aEQb,
		      aLTbRec)));
  return res;
}

template <>
Node optimalSignGadget (const Node& a,
			       const Node& b,
			       const Node &aLNodebRec,
			       CVC4::prop::CnfStream* cnf); 


template <class T>
std::pair<T,T> inline optimalFullAdder(const T a,
				       const T b,
				       const T cin,
                                       CVC4::prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalFullAdder<T> dummy" << std::endl;
  T cout = mkOr(mkAnd(a, b),
		mkAnd(mkXor(a, b),
		      cin));;
  T sum = mkXor(mkXor(a, b), cin);
  return std::make_pair(sum, cout);
}

template <>
std::pair<Node,Node> optimalFullAdder(const Node a,
				      const Node b,
				      const Node cin,
				      CVC4::prop::CnfStream* cnf);
 
/*****************************
*
* Helper functions that combine the optimal primitives
* 
******************************/

 
template <class T>
T optimalRippleCarryAdder(const std::vector<T>&av,
			  const std::vector<T>& bv,
			  std::vector<T>& res, T cin, prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalRippleCarryAdder" << std::endl;
  Assert (av.size() == bv.size() &&res.size() == 0);
  T carry = cin;
  std::pair<T, T> fa_res;
  for (unsigned i = 0 ; i < av.size(); ++i) {
    T a = av[i];
    T b = bv[i];
    fa_res = optimalFullAdder(a, b, carry, cnf);
    
    carry = fa_res.second;
    res.push_back(fa_res.first);
  }

  return carry;
}

template <class T>
T inline optimalUltBB(const std::vector<T>&a, const std::vector<T>& b,
		      unsigned k, bool orEqual, CVC4::prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalUltBB" << std::endl;
  Assert (a.size() && b.size());
  Assert (k <= a.size());
  
  T answer = orEqual? mkTrue<T>() : mkFalse<T>();
  for (int i = 0; i < k; ++i) {
    answer = optimalUltGadget(a[i], b[i], answer, cnf);
  }
  return answer;
}


}
}
}

#endif
