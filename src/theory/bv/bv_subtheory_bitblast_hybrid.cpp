/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Liana Hadarean, Clark Barrett
 ** Minor contributors (to current version): Morgan Deters, Andrew Reynolds, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_bitblast_hybrid.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/options.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

BitblastHybridSolver::BitblastHybridSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv)
  , d_bitblaster(new HybridBitblaster(bv))
  , d_modelCache()
  , d_validModelCache(c, true)
  , d_bitblastQueue(c)
  , d_statistics()
{}

BitblastHybridSolver::~BitblastHybridSolver() {
}

BitblastHybridSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::BitblastHybridSolver::NumCallsToCheck", 0)
  , d_numBBLemmas("theory::bv::BitblastHybridSolver::NumTimesLemmasBB", 0)
{
  StatisticsRegistry::registerStat(&d_numCallstoCheck);
  StatisticsRegistry::registerStat(&d_numBBLemmas);
}
BitblastHybridSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numCallstoCheck);
  StatisticsRegistry::unregisterStat(&d_numBBLemmas);
}


bool BitblastHybridSolver::check(Theory::Effort e) {
  Debug("bv-bitblast-hybrid") << "BitblastHybridSolver::check (" << e << ")\n";
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_HYBRID); 

  ++(d_statistics.d_numCallstoCheck);

  // Processing assertions
  while (!done()) {
    Assert(!d_bv->inConflict());
    
    TNode fact = get();
    TNode atom = fact.getKind() == kind::NOT? fact[0] : fact;
    if (fact.getKind() == kind::BITVECTOR_BITOF)
      continue;

    d_bitblastQueue.push(fact);
    //  d_bitblaster->bbAtom(atom);
    d_validModelCache = false;
    Debug("bv-bitblast-hybrid") << "  fact " << fact << ")\n";
  }
  
  if (e == Theory::EFFORT_FULL) {
    if (options::bitvectorLazyHybrid()) {
      // extra lazy and only bit-blast one atom
      TNode atom = d_bitblastQueue.front();
      d_bitblastQueue.pop();
      d_bitblaster->bbAtom(atom);
      return true; 
    }
    while (!d_bitblastQueue.empty()) {
      TNode atom = d_bitblastQueue.front();
      d_bitblastQueue.pop();
      d_bitblaster->bbAtom(atom);
    }
  }

  return true;
}

EqualityStatus BitblastHybridSolver::getEqualityStatus(TNode a, TNode b) {
  Node a_val = getModelValue(a);
  Node b_val = getModelValue(b);
  if (a_val == b_val)
    return EQUALITY_TRUE_IN_MODEL;
  return EQUALITY_UNKNOWN;
}

void BitblastHybridSolver::collectModelInfo(TheoryModel* m, bool fullModel) {
  return d_bitblaster->collectModelInfo(m, fullModel);
}

Node BitblastHybridSolver::getModelValue(TNode node) {
  if (!d_validModelCache) {
    d_modelCache.clear();
    d_validModelCache = true;
  }
  return getModelValueRec(node);
}

Node BitblastHybridSolver::getModelValueRec(TNode node) {
  Node val;
  if (node.isConst()) {
    return node;
  }
  NodeMap::iterator it = d_modelCache.find(node);
  if (it != d_modelCache.end()) {
    val = (*it).second;
    Debug("bitvector-model") << node << " => (cached) " << val <<"\n";
    return val;
  }
  if (d_bv->isLeaf(node)) {
    val = d_bitblaster->getVarValue(node);
    if (val == Node()) {
      // If no value in model, just set to 0
      val = utils::mkConst(utils::getSize(node), (unsigned)0);
    }
  } else {
    NodeBuilder<> valBuilder(node.getKind());
    if (node.getMetaKind() == kind::metakind::PARAMETERIZED) {
      valBuilder << node.getOperator();
    }
    for (unsigned i = 0; i < node.getNumChildren(); ++i) {
      valBuilder << getModelValueRec(node[i]);
    }
    val = valBuilder;
    val = Rewriter::rewrite(val);
  }
  Assert(val.isConst());
  d_modelCache[node] = val;
  Debug("bitvector-model") << node << " => " << val <<"\n";
  return val;
}
