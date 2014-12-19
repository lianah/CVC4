/*********************                                                        */
/*! \file encoding_manager.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/encoding_manager.h"
#include "prop/bvminisat/bvminisat.h"
#include "prop/cnf_stream.h"
#include "theory/bv/bitblaster_template.h"


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

EncodingManager* EncodingManager::d_currentEM = NULL;

EncodingManager::EncodingManager()
  : d_bb(NULL)
  , d_cnf(NULL)
  , d_solver(NULL)
  , d_multToId()
  , d_multCount(0)
  , d_finalized(false)
  , d_sameCircuitLearned(0)
  , d_totalLearned(0)
{}

EncodingManager::~EncodingManager() {}

EncodingManager* EncodingManager::currentEM() {
  if (d_currentEM == NULL) {
    d_currentEM = new EncodingManager(); 
  }
  return d_currentEM; 
}

void EncodingManager::setBitblaster(theory::bv::TBitblaster<Node>* bb) {
  Assert (d_bb == NULL);
  d_bb = bb; 
}
void EncodingManager::setCnfStream(prop::CnfStream* cnf) {
  //  Assert (d_cnf == NULL);
  // d_cnf = cnf; 
}
void EncodingManager::setSatSolver(prop::BVSatSolverInterface* solver) {
  Assert (d_solver == NULL);
  d_solver = solver; 
}

void EncodingManager::registerMultiplier(TNode mult) {
  Assert(!d_finalized);
  Assert (mult.getKind() == kind::BITVECTOR_MULT);
  Assert (d_multToId.find(mult) == d_multToId.end());
  unsigned id = d_multCount++;
  Debug("encoding") << "EncodingManager::registerMultiplier " << mult <<" => " << id <<"\n"; 
  d_multToId[mult] = id;
}

void EncodingManager::finalizeEncoding() {
  Assert (!d_finalized);
  d_finalized = true;
  MultToId::const_iterator it = d_multToId.begin();
  for (; it != d_multToId.end(); ++it) {
    TNode mult = it->first;
    Assert (mult.getNumChildren() == 2);
    TNode a = mult[0];
    TNode b = mult[1];
    std::vector<Node> a_bits;
    std::vector<Node> b_bits;
    d_bb->getBBTerm(a, a_bits);
    d_bb->getBBTerm(b, b_bits);

    TNodeSet fringe;
    for (unsigned i = 0; i < a_bits.size(); ++i) {
      fringe.insert(a_bits[i]);
      fringe.insert(b_bits[i]);
    }
    
    unsigned id = it->second;

    std::vector<Node> bits;
    d_bb->getBBTerm(mult, bits);
    for (unsigned i  = 0; i < bits.size(); ++i) {
      TNode bit = bits[i];
      TNodeSet cache;
      markSatVariables(bit, id, cache, fringe);
    }
    markAtoms(mult, id);
  }
}

void EncodingManager::markAtoms(TNode mult, unsigned id) {
  TNodeMap::const_iterator it = d_atoms.begin();
  for (; it != d_atoms.end(); ++it) {
    TNode atom = it->first;
    if (atom.hasSubterm(mult)) {
      TNode def = it->second;
      Assert (d_cnf->hasLiteral(def));
      Assert (d_cnf->hasLiteral(atom));
      prop::SatLiteral lit_atom = d_cnf->getLiteral(atom);
      prop::SatLiteral lit_def = d_cnf->getLiteral(def);
      std::cout << "marking literal " << lit_atom << " with " << id <<"\n";
      std::cout << "marking literal " << lit_def << " with " << id <<"\n"; 
      d_solver->markLiteral(lit_atom, id);
      d_solver->markLiteral(lit_def, id);
    }
  }
}

// TODO: for more complex terms define fringe!
void EncodingManager::markSatVariables(TNode bit, unsigned id, TNodeSet& cache, TNodeSet& fringe) {
  if (cache.find(bit) != cache.end()) return;
  Assert (bit.getType().isBoolean());
  
  if (bit.isConst()) return;
  Assert (d_cnf->hasLiteral(bit));
  prop::SatLiteral lit = d_cnf->getLiteral(bit);

  Debug("encoding-detailed") << "markSatVariabls " << bit <<" => " << id <<"\n"; 
  d_solver->markLiteral(lit, id);

  if (bit.getKind() == kind::BITVECTOR_BITOF ||
      fringe.find(bit) != fringe.end()) {
    // do not dig deeper
    cache.insert(bit);
    return;
  }
  
  for (unsigned i = 0; i < bit.getNumChildren(); ++i) {
    markSatVariables(bit[i], id, cache, fringe);
  }
  cache.insert(bit);
}

void EncodingManager::printResult() {
  Assert(d_finalized);
  Trace("encoding") << "TotalLearned " << d_totalLearned <<"\n";
  Trace("encoding") << "SameCircuit  " << d_sameCircuitLearned <<"\n";
  Trace("encoding") << d_totalLearned <<", " << d_sameCircuitLearned << "\n";
}

void EncodingManager::registerAtom(TNode atom, TNode atom_def) {
  Assert (d_atoms.find(atom) == d_atoms.end());
  d_atoms[atom] = atom_def;
}


