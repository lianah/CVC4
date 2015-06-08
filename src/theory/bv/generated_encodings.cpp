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

