/*********************                                                        */
/*! \file generated_encodings.cpp
** \verbatim
** Original author: Liana Hadarean
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Automatically generated optimally propagating encodings.
**
** Automatically generated optimally propagating encodings.
**/

#include "cvc4_private.h"
#include "theory/bv/generated_encodings.h"
#include "prop/cnf_stream.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 

template<>
std::pair<Node, Node> CVC4::theory::bv::optimalFullAdder(const Node a,
							 const Node b,
							 const Node cin,
							 CVC4::prop::CnfStream* cnf) {

  Debug("optimal-encodings") << "optimalFullAdder generated" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node s = nm->mkSkolem("sum", nm->booleanType());
  Node cout = nm->mkSkolem("carry", nm->booleanType());

  // if (options::mergeCnf()) {
  //   Node cout_expr = mkOr(mkAnd(a, b),
  // 			  mkAnd(mkXor(a, b),
  // 				cin));
  //   Node sum_expr = mkXor(mkXor(a, b), cin);
  
  //   cnf->mergeInMap(cout_expr, cout);
  //   cnf->mergeInMap(sum_expr, s);
  // }
  Node na = nm->mkNode(kind::NOT, a);
  Node nb = nm->mkNode(kind::NOT, b);
  Node ncin = nm->mkNode(kind::NOT, cin);
  Node ncout = nm->mkNode(kind::NOT, cout);
  Node ns = nm->mkNode(kind::NOT, s);

  cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, ncin, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, nb, ncin, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, nb, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, ncin, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, ncin, s),
			false, false, RULE_INVALID, TNode::null());

  cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, cin, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, cin, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, cin, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a,b, cin,ns),
			false, false, RULE_INVALID, TNode::null());


  return std::make_pair(s, cout);
}

template <>
Node CVC4::theory::bv::optimalUltGadget(const Node &a, const Node &b, const Node &rest,
					CVC4::prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalUltGadget generated" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node answer = nm->mkSkolem("answer", nm->booleanType());
  
  Node a_iff_b = nm->mkSkolem("and", nm->booleanType());

  cnf->convertAndAssert(mkIff(a_iff_b, mkIff(a, b)), false, false, RULE_INVALID, TNode::null());
  
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, utils::mkNot(a), utils::mkNot(answer)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, b, utils::mkNot(answer)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, utils::mkNot(a_iff_b), utils::mkNot(answer)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, utils::mkNot(answer), a_iff_b),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, a, a_iff_b),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(b), a_iff_b),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), utils::mkNot(a), b),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), utils::mkNot(a_iff_b), answer),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), utils::mkNot(b), answer),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), a, answer),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), utils::mkNot(a_iff_b), a),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(a_iff_b), b),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), a, answer),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answer, a_iff_b, a),
			false, false, RULE_INVALID, TNode::null());
  return answer;
}

template<>
Node CVC4::theory::bv::optimalSignGadget(const Node& a,
					 const Node& b,
					 const Node &aLTb,
					 CVC4::prop::CnfStream* cnf) {
  Debug("optimal-encodings") << "optimalSignGadget generated" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node aSLTb = nm->mkSkolem("aSLTb", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b, aSLTb, utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, aSLTb, utils::mkNot(aLTb)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(aSLTb), aLTb),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(aSLTb), utils::mkNot(b)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, aLTb, utils::mkNot(aSLTb), utils::mkNot(b)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aLTb), aSLTb, utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());

  return aSLTb;
}


