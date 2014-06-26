/*********************                                                        */
/*! \file hybrid_bitblaster.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): lianah
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief 
 **
 ** Bitblaster for the hybrid bv solver. 
 **/

#include "cvc4_private.h"

#include "theory/bv/bitblaster_template.h"
#include "theory/bv/options.h"
#include "theory/theory_model.h"
#include "theory/bv/theory_bv.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 

HybridBitblaster::HybridBitblaster(TheoryBV* theory_bv)
  : TBitblaster<Node>()
  , d_bv(theory_bv)
  , d_bbAtoms()
{}

HybridBitblaster::~HybridBitblaster() {
}

/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void HybridBitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;
  if (node.getKind() == kind::BITVECTOR_BITOF)
    return; 
  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-hybrid-bitblast") << "Bitblasting node " << node <<"\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
      Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
      normalized;
  // asserting that the atom is true iff the definition holds
  Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);
  d_bv->lemma(atom_definition);
}

void HybridBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  // no need to store the definition for the lazy bit-blaster
  d_bbAtoms.insert(atom); 
}

bool HybridBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end(); 
}

void HybridBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-hybrid-bitblast") << "Bitblasting node " << node <<"\n";

  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert (bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}

void HybridBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i)); 
  }
  d_variables.insert(var); 
}

Node HybridBitblaster::getBBAtom(TNode node) const {
  return node; 
}


/**
 * Returns the value a is currently assigned to in the SAT solver
 * or null if the value is completely unassigned.
 *
 * @param a
 * @param fullModel whether to create a "full model," i.e., add
 * constants to equivalence classes that don't already have them
 *
 * @return
 */
Node HybridBitblaster::getVarValue(TNode a, bool fullModel) {
  if (!hasBBTerm(a)) {
    return Node(); 
  }
  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() -1; i >= 0; --i) {
    TNode bit = bits[i];
    Assert (bit.getKind() == kind::BITVECTOR_BITOF);
    
    TNode bit_value = utils::mkFalse();
    theory::Valuation& valuation = d_bv->getValuation();
    if (valuation.isSatLiteral(bit)) {
      bit_value = valuation.getSatValue(bits[i]);
    }

    // if bit is Null() i.e. unassigned just set the value to false
    Integer bit_int = bit_value == utils::mkTrue() ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(BitVector(bits.size(), value));
}

void HybridBitblaster::collectModelInfo(TheoryModel* m, bool fullModel) {
  TNodeSet::const_iterator it = d_variables.begin();
  for (; it!= d_variables.end(); ++it) {
    TNode var = *it;
    if (Theory::theoryOf(var) == theory::THEORY_BV || isSharedTerm(var))  {
      Node const_value = getVarValue(var, fullModel);
      Assert (!const_value.isNull()); 
      Debug("bitvector-model") << "TLazyBitblaster::collectModelInfo (assert (= "
                               << var << " "
                               << const_value << "))\n";
      m->assertEquality(var, const_value, true);
    }
  }
}

bool HybridBitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end();
}
