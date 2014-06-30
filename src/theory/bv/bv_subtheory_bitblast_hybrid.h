/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters, Andrew Reynolds, Liana Hadarean, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bitblaster_template.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * BitblastSolver
 */
class BitblastHybridSolver : public SubtheorySolver {
  struct Statistics {
    IntStat d_numCallstoCheck;
    IntStat d_numBBLemmas;
    Statistics();
    ~Statistics();
  };

  HybridBitblaster* d_bitblaster;
  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_modelCache;
  context::CDO<bool> d_validModelCache;
  context::CDQueue<TNode> d_bitblastQueue;

  Statistics d_statistics;
  
  Node getModelValueRec(TNode node);
public:
  BitblastHybridSolver(context::Context* c, TheoryBV* bv);
  ~BitblastHybridSolver();

  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions) { Unreachable(); }
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void collectModelInfo(TheoryModel* m, bool fullModel);
  Node getModelValue(TNode node);
  bool isComplete() { return true; }
};

}
}
}
