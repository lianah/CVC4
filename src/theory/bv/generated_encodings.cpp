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

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 

std::pair<Node, Node> CVC4::theory::bv::optimalFullAdder(const Node a, const Node b,
							 const Node cin,
							 CVC4::prop::CnfStream* cnf) {

  NodeManager* nm = NodeManager::currentNM();
  Node s = nm->mkSkolem("sum", nm->booleanType());
  Node cout = nm->mkSkolem("carry", nm->booleanType());

  if (options::mergeCnf()) {
    Node cout_expr = mkOr(mkAnd(a, b),
			  mkAnd(mkXor(a, b),
				cin));
    Node sum_expr = mkXor(mkXor(a, b), cin);
  
    cnf->mergeInMap(cout_expr, cout);
    cnf->mergeInMap(sum_expr, s);
  }
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
std::pair<Node, std::pair<Node, Node> >
CVC4::theory::bv::add3DoubleCarryGadget(const Node x1,
                                        const Node x2,
                                        const Node x3,
                                        const std::pair<Node, Node>& carry,
                                        CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();

  Debug("encoding-generated") << "add3DoubleCarryGadget" << std::endl;
  Node sum = nm->mkSkolem("sum", nm->booleanType());
  Node carry_out0 = nm->mkSkolem("cout0", nm->booleanType());

  Node carry_out1 = nm->mkSkolem("cout1", nm->booleanType());

  // ((x1 XOR x2) XOR x3) AND carry0
  Node aux1 = nm->mkSkolem("aux", nm->booleanType());
  // (x1 AND x2) OR ((x1 XOR x2) AND x3)
  Node aux2 = nm->mkSkolem("aux", nm->booleanType());
  // x3 AND (x1 AND x2)
  Node aux3 = nm->mkSkolem("aux", nm->booleanType());

  Node carry0 = carry.first;
  Node carry1 = carry.second;

  if (options::mergeCnf()) {
    Node aux1_expr = mkAnd(mkXor(mkXor(x1,x2),x3),carry0);
    Node aux2_expr = mkXor(mkAnd(x1, x2), mkAnd(mkXor(x1, x2), x3));
    Node aux3_expr = mkAnd(x3, mkAnd(x1, x2));
    cnf->mergeInMap(aux1_expr, aux1);
    cnf->mergeInMap(aux2_expr, aux2);
    cnf->mergeInMap(aux3_expr, aux3);
  }


  std::vector<Node> clause;
  
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux3), x3), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux3), x1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux1), utils::mkNot(sum)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux3), x2), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, aux2, utils::mkNot(aux3)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux1), carry0), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux2), x2, x3), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux2), x3, x1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, utils::mkNot(aux2), utils::mkNot(carry1)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, utils::mkNot(aux2), carry_out0), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, utils::mkNot(aux2), utils::mkNot(aux1)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, utils::mkNot(carry1), utils::mkNot(aux1)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, carry_out0, utils::mkNot(aux1)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry1), carry_out0, carry_out1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x2), aux2), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x2), aux2), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry_out1, utils::mkNot(aux3), sum), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry_out0), utils::mkNot(carry_out1), aux3), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux3), carry_out1, utils::mkNot(carry0)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux2), utils::mkNot(aux1), aux3), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry1, utils::mkNot(carry_out1), aux3), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x1), aux2), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry1, utils::mkNot(carry_out1), aux1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry_out0), utils::mkNot(carry_out1), aux1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, carry1, utils::mkNot(carry_out0), utils::mkNot(carry_out1)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux2), x2, x1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry0), sum, aux1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux3), aux1, sum), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry0), utils::mkNot(aux3), aux1), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(carry_out1), aux1, aux2), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(sum); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x1)); 
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(aux3); 
  clause.push_back(utils::mkNot(x2)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x3)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x2)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x1)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x1)); 
  clause.push_back(sum); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(x1)); 
  clause.push_back(carry_out1); 
  clause.push_back(sum); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(sum); 
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x1)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(sum); 
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x2)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x3)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(x2)); 
  clause.push_back(carry_out1); 
  clause.push_back(sum); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x2)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x1)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x1)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x2)); 
  clause.push_back(sum); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x2)); 
  clause.push_back(utils::mkNot(carry0)); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(carry_out1); 
  clause.push_back(sum); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(sum); 
  clause.push_back(carry_out0); 
  clause.push_back(carry_out1); 
  clause.push_back(utils::mkNot(x3)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(aux3)); 
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(utils::mkNot(carry0)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(carry1); 
  clause.push_back(utils::mkNot(carry_out0)); 
  clause.push_back(aux1); 
  clause.push_back(aux2); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(aux2)); 
  clause.push_back(carry0); 
  clause.push_back(utils::mkNot(sum)); 
  clause.push_back(aux3); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(aux1)); 
  clause.push_back(x2); 
  clause.push_back(x3); 
  clause.push_back(x1); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(aux3)); 
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(sum); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(carry1)); 
  clause.push_back(carry_out0); 
  clause.push_back(utils::mkNot(aux1)); 
  clause.push_back(utils::mkNot(aux2)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x1); 
  clause.push_back(carry0); 
  clause.push_back(x2); 
  clause.push_back(utils::mkNot(sum)); 
  clause.push_back(x3); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause), false, false, RULE_INVALID, TNode::null());
  std::pair<Node, Node> carry_out = std::make_pair(carry_out0, carry_out1);
  return std::make_pair(sum, carry_out);
}

template <>
Node CVC4::theory::bv::optimalUltGadget(const Node &a, const Node &b, const Node &rest,
					CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Node answer = nm->mkSkolem("answer", nm->booleanType());
  
  Node a_iff_b = nm->mkSkolem("and", nm->booleanType());

  cnf->convertAndAssert(mkIff(a_iff_b, mkIff(a, b)), false, false, RULE_INVALID, TNode::null());
  
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, utils::mkNot(a), utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, b, utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, rest, utils::mkNot(a_iff_b), utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, utils::mkNot(answer), a_iff_b), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, a, a_iff_b), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(b), a_iff_b), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), utils::mkNot(a), b), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), utils::mkNot(a_iff_b), answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), utils::mkNot(b), answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), a, answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), utils::mkNot(a_iff_b), a), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(a_iff_b), b), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), a, answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answer, a_iff_b, a), false, false, RULE_INVALID, TNode::null());
  return answer;
}

template <>
Node CVC4::theory::bv::fromCnfUltGadget(const Node &a, const Node &b, const Node &rest,
					CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Node answer = nm->mkSkolem("answer", nm->booleanType());
  Node aux = nm->mkSkolem("aux", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), b, utils::mkNot(aux)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(b), utils::mkNot(aux)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(b), aux), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, aux), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), rest, utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux), rest, utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), aux, utils::mkNot(answer)), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(rest), answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aux), utils::mkNot(rest), answer), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, aux, answer), false, false, RULE_INVALID, TNode::null());
  return answer;
}


// old gadget 
// template <>
// Node CVC4::theory::bv::optimalUltGadget(const Node &a, const Node &b, const Node &rest,
// 					CVC4::prop::CnfStream* cnf) {
//   NodeManager* nm = NodeManager::currentNM();
//   Node answer = nm->mkSkolem("answer", nm->booleanType());

//   cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), rest, utils::mkNot(a)),
// 			false, false, RULE_INVALID, TNode::null());
//   cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), rest, b),
// 			false, false, RULE_INVALID, TNode::null());
//   cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), utils::mkNot(a), b),
// 			false, false, RULE_INVALID, TNode::null());
//   cnf->convertAndAssert(nm->mkNode(kind::OR, a, answer, utils::mkNot(b)),
// 			false, false, RULE_INVALID, TNode::null());
//   cnf->convertAndAssert(nm->mkNode(kind::OR, a, answer, utils::mkNot(rest)),
// 			false, false, RULE_INVALID, TNode::null());
//   cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(rest), utils::mkNot(b), answer),
// 			false, false, RULE_INVALID, TNode::null());
//   return answer;
// }


template<>
Node CVC4::theory::bv::optimalSignGadget(const Node& a,
					 const Node& b,
					 const Node &aLTb,
					 CVC4::prop::CnfStream* cnf) {
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

template <>
std::vector<Node> CVC4::theory::bv::optimalMultConst3Gadget(const std::vector<Node>& a,
							    prop::CnfStream* cnf) {

  Assert (a.size() == 2); 
  NodeManager* nm = NodeManager::currentNM();
  
  std::vector<Node> res;
  for (unsigned i = 0; i < 2*a.size(); ++i) {
    res.push_back(nm->mkSkolem("c", nm->booleanType()));
  }
      
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[2]), utils::mkNot(res[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[1]), utils::mkNot(res[3])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(res[3])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(res[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[0], utils::mkNot(a[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[1], utils::mkNot(res[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[1], a[1], utils::mkNot(res[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(res[1]), res[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[3], utils::mkNot(a[1]), res[2]), false, false, RULE_INVALID, TNode::null());
  
  Assert (res.size() == 4);
  return res; 
}

template <>
std::vector<Node> CVC4::theory::bv::optimalMultConst5Gadget(const std::vector<Node>& a,
							    prop::CnfStream* cnf) {
  Assert (a.size() == 3); 
  NodeManager* nm = NodeManager::currentNM();
  
  std::vector<Node> res;
  for (unsigned i = 0; i < 2*a.size(); ++i) {
    res.push_back(nm->mkSkolem("res", nm->booleanType()));
  }

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), res[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(res[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(res[4])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), utils::mkNot(res[4])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(res[5])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), utils::mkNot(res[3])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[2]), utils::mkNot(res[5])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(res[1])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[4], utils::mkNot(a[2]), res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[2]), res[4], res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), a[1], utils::mkNot(res[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), utils::mkNot(res[2]), utils::mkNot(a[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[0], utils::mkNot(res[3]), a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[4], utils::mkNot(res[3]), a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[2], res[0], utils::mkNot(a[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[1]), res[2], utils::mkNot(res[4])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[2], a[2], utils::mkNot(a[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[2], res[3], utils::mkNot(res[4])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[1]), res[3], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(res[4]), utils::mkNot(a[0])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), res[3], utils::mkNot(a[0])), false, false, RULE_INVALID, TNode::null());
  
  
  Assert (res.size() == 6);
  return res; 
}

template <>
std::vector<Node> CVC4::theory::bv::optimalMultConst7Gadget(const std::vector<Node>& a,
							    prop::CnfStream* cnf) {
  Assert (a.size() == 3); 
  NodeManager* nm = NodeManager::currentNM();
  
  std::vector<Node> res;
  for (unsigned i = 0; i < 2*a.size(); ++i) {
    res.push_back(nm->mkSkolem("res", nm->booleanType()));
  }

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), utils::mkNot(res[3])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), utils::mkNot(res[1])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(res[5])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), utils::mkNot(res[2])), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[1], utils::mkNot(a[1]), a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(a[2]), res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[4], utils::mkNot(res[2]), res[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), res[1], a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[2]), res[1], res[4]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[2]), res[4], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), res[2], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), res[0], a[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), res[3], a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[2]), res[2], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), res[1], res[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), res[2], a[1]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[0]), res[2], a[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[1]), res[2], a[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), res[1], a[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), a[1], a[2]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[3], utils::mkNot(a[1]), res[4]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[2]), res[3], res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[2]), res[3], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), a[1], res[4]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, res[3], utils::mkNot(a[2]), res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), res[2], res[5]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[1]), a[1], a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[5]), a[1], a[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[4]), res[2], res[0]), false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(res[3]), res[2], res[5]), false, false, RULE_INVALID, TNode::null());  
  
  Assert (res.size() == 6);
  return res; 
}



template<>
void CVC4::theory::bv::optimalMult2(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, prop::CnfStream* cnf) {
  
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2()" <<std::endl;
  unsigned bitwidth = 2;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }
  
  std::vector<Node> clause;
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[1]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(a[0]), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(b[0]), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, c[0], utils::mkNot(b[0]), utils::mkNot(a[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], b[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[1]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
}

template<>
void CVC4::theory::bv::optimalMult3(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3()" <<std::endl;
  unsigned bitwidth = 3;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[0]), b[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[0]), a[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), a[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), b[1], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(c[3]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[1], utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], b[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[1], c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[0]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(b[0]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[0]), utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[1], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[3]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), b[0], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, c[0], utils::mkNot(b[0]), utils::mkNot(a[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[3]), a[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(a[0]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[0], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[2]), utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), a[1], utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[0], a[2]),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(b[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(b[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[3]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[4])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(a[2]); 
  clause.push_back(c[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(a[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(a[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(b[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(b[2]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(b[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(b[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[0]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(a[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(a[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(b[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(a[2]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(a[2]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(a[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[5]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  clause.push_back(c[2]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[3]); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(a[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[3]); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(a[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(b[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[1]); 
  clause.push_back(c[3]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[0]); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[3]); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(c[0]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(c[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(b[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
clause.push_back(c[3]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(c[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(a[1]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[5]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(c[4]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[1]); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[2]); 
clause.push_back(b[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(c[1]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(a[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(b[2]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(b[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(c[2]); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(b[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(b[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[2]); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[2]); 
 clause.push_back(c[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[5])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[4]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[1]); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(c[0]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[4])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[4])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[1]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(b[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[0]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[3]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(b[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(a[2]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(b[0]); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[1]); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(a[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(a[1]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[1]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(a[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
}

template<>
void CVC4::theory::bv::optimalMult4(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult4()" <<std::endl;
  unsigned bitwidth = 4;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

template<>
inline void CVC4::theory::bv::optimalMult2Aux(const std::vector<Node>&a,
					      const std::vector<Node>& b,
					      std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Aux()" <<std::endl;
  unsigned bitwidth = 2;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}


template<>
inline void CVC4::theory::bv::optimalMult3Aux(const std::vector<Node>&a,
					      const std::vector<Node>& b,
					      std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3Aux()" <<std::endl;
  unsigned bitwidth = 3;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

template<>
inline void CVC4::theory::bv::optimalMult4Aux(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult4Aux()" <<std::endl;
  unsigned bitwidth = 4;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

inline void CVC4::theory::bv::optimalMult2Debug(const std::vector<Node>&a,
						const std::vector<Node>& b,
						std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  unsigned size = 2;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());

  std::vector<Node> clause;
  
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x2), x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());

  
}

inline void CVC4::theory::bv::optimalMult3Debug(const std::vector<Node>&a,
						const std::vector<Node>& b,
						std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  unsigned size = 3;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());
  Node x6 = nm->mkSkolem("x", nm->booleanType());
  Node x7 = nm->mkSkolem("x", nm->booleanType());
  Node x8 = nm->mkSkolem("x", nm->booleanType());
  Node x9 = nm->mkSkolem("x", nm->booleanType());
  Node x10 = nm->mkSkolem("x", nm->booleanType());
  Node x11 = nm->mkSkolem("x", nm->booleanType());
  Node x12 = nm->mkSkolem("x", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x2), x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[2]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[1]), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), utils::mkNot(x6), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x5), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x6), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(utils::mkNot(x5)); 
  clause.push_back(utils::mkNot(x6)); 
  clause.push_back(x8); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, x6, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, x5, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, x6, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x3); 
  clause.push_back(x5); 
  clause.push_back(x6); 
  clause.push_back(utils::mkNot(x8)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[2]), x9),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), x10, x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x9), x10, x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x12),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x11), c[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());

} 

inline void CVC4::theory::bv::optimalMult4Debug(const std::vector<Node>&a,
			      const std::vector<Node>& b,
			      std::vector<Node>& c, prop::CnfStream* cnf) {
  unsigned size = 4;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());
  Node x6 = nm->mkSkolem("x", nm->booleanType());
  Node x7 = nm->mkSkolem("x", nm->booleanType());
  Node x8 = nm->mkSkolem("x", nm->booleanType());
  Node x9 = nm->mkSkolem("x", nm->booleanType());
  Node x10 = nm->mkSkolem("x", nm->booleanType());
  Node x11 = nm->mkSkolem("x", nm->booleanType());
  Node x12 = nm->mkSkolem("x", nm->booleanType());
  Node x13 = nm->mkSkolem("x", nm->booleanType());
  Node x14 = nm->mkSkolem("x", nm->booleanType());
  Node x15 = nm->mkSkolem("x", nm->booleanType());
  Node x16 = nm->mkSkolem("x", nm->booleanType());
  Node x17 = nm->mkSkolem("x", nm->booleanType());
  Node x18 = nm->mkSkolem("x", nm->booleanType());
  Node x19 = nm->mkSkolem("x", nm->booleanType());
  Node x20 = nm->mkSkolem("x", nm->booleanType());
  Node x21 = nm->mkSkolem("x", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x1), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x2, x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x2, x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[2]), x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[1]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), utils::mkNot(x5), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x4), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x5), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x2)); 
  clause.push_back(utils::mkNot(x4)); 
  clause.push_back(utils::mkNot(x5)); 
  clause.push_back(x7); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, x5, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, x4, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, x5, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x2); 
  clause.push_back(x4); 
  clause.push_back(x5); 
  clause.push_back(utils::mkNot(x7)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[3], utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[3]), x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[2]), x9),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), utils::mkNot(x8), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x9), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x6)); 
  clause.push_back(utils::mkNot(x8)); 
  clause.push_back(utils::mkNot(x9)); 
  clause.push_back(x21); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, x8, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x6); 
  clause.push_back(x8); 
  clause.push_back(x9); 
  clause.push_back(utils::mkNot(x21)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[2]), x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x7), utils::mkNot(x11), x12),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x7), x12, x13),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x11), x12, x13),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, x11, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, x11, utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x14)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x14)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[2]), x14),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), utils::mkNot(x14), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), utils::mkNot(x12), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), utils::mkNot(x14), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x14), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x21)); 
  clause.push_back(utils::mkNot(x12)); 
  clause.push_back(utils::mkNot(x14)); 
  clause.push_back(x16); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, x14, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, x12, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, x14, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x14, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x21); 
  clause.push_back(x12); 
  clause.push_back(x14); 
  clause.push_back(utils::mkNot(x16)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[3], utils::mkNot(x17)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x17)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[3]), x17),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x16), utils::mkNot(x17), x18),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x16), x18, x19),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x17), x18, x19),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, x17, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x17, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x17, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, x17, utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x20)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x20)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x20),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x20), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x20, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x13), c[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x13, utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x19), c[3]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x19, utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
} 
