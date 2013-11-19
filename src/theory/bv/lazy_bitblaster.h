/*********************                                                        */
/*! \file lazy_bitblaster.h
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
 ** Bitblaster for the lazy bv solver. 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__LAZY__BITBLASTER_H
#define __CVC4__LAZY__BITBLASTER_H


#include "bitblaster_template.h"
#include "theory_bv_utils.h"
#include "theory/rewriter.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/options.h"
#include "theory/model.h"

namespace CVC4 {
namespace theory {
namespace bv {

TLazyBitblaster::TLazyBitblaster(context::Context* c, bv::TheoryBV* bv)
  : TBitblaster()
  , d_bv(bv)
  , d_bvOutput(bv->d_out)
  , d_assertedAtoms(c)
  , d_variables()
  , d_statistics()
{
    d_satSolver = prop::SatSolverFactory::createMinisat(c);
    d_cnfStream = new prop::TseitinCnfStream(d_satSolver,
                                             new prop::NullRegistrar(),
                                             new context::Context());

    MinisatNotify* notify = new MinisatNotify(d_cnfStream, bv);
    d_satSolver->setNotify(notify);
  }

TLazyBitblaster::~TLazyBitblaster() {
  delete d_cnfStream;
  delete d_satSolver;
}


/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void TLazyBitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  if (hasBBAtom(node)) {
    return;
  }

  // make sure it is marked as an atom
  addAtom(node);

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numAtoms;
  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
      Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
      normalized;
  // asserting that the atom is true iff the definition holds
  Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);
  storeBBAtom(node);
    
  if (!options::bitvectorEagerBitblast()) {
    d_cnfStream->convertAndAssert(atom_definition, false, false);
  } else {
    d_bvOutput->lemma(atom_definition, false);
  }
}

void TLazyBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i)); 
  }
  d_variables.insert(var); 
}

uint64_t TLazyBitblaster::computeAtomWeight(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  Node atom_bb = Rewriter::rewrite(d_atomBBStrategies[node.getKind()](node, this));
  uint64_t size = utils::numNodes(atom_bb);
  return size;
}

// cnf conversion ensures the atom represents itself
Node TLazyBitblaster::getBBAtom(TNode node) const {
  return node; 
}

void TLazyBitblaster::bbTerm(TNode node, Bits& bits) {

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numTerms;

  d_termBBStrategies[node.getKind()] (node, bits,this);

  Assert (bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}

// Node TLazyBitblaster::bbOptimize(TNode node) {
//   std::vector<Node> children;

//    if (node.getKind() == kind::BITVECTOR_PLUS) {
//     if (RewriteRule<BBPlusNeg>::applies(node)) {
//       Node res = RewriteRule<BBPlusNeg>::run<false>(node);
//       return res;
//     }
//     //  if (RewriteRule<BBFactorOut>::applies(node)) {
//     //   Node res = RewriteRule<BBFactorOut>::run<false>(node);
//     //   return res;
//     // }

//   } else if (node.getKind() == kind::BITVECTOR_MULT) {
//     if (RewriteRule<MultPow2>::applies(node)) {
//       Node res = RewriteRule<MultPow2>::run<false>(node);
//       return res;
//     }
//   }

//   return node;
// }

/// Public methods

void TLazyBitblaster::addAtom(TNode atom) {
  if (!options::bitvectorEagerBitblast()) {
    d_cnfStream->ensureLiteral(atom);
    prop::SatLiteral lit = d_cnfStream->getLiteral(atom);
    d_satSolver->addMarkerLiteral(lit);
  }
}

void TLazyBitblaster::explain(TNode atom, std::vector<TNode>& explanation) {
  std::vector<prop::SatLiteral> literal_explanation;
  d_satSolver->explain(d_cnfStream->getLiteral(atom), literal_explanation);
  for (unsigned i = 0; i < literal_explanation.size(); ++i) {
    explanation.push_back(d_cnfStream->getNode(literal_explanation[i]));
  }
}


/*
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be asserted
 *
 */

bool TLazyBitblaster::propagate() {
  return d_satSolver->propagate() == prop::SAT_VALUE_TRUE;
}

bool TLazyBitblaster::assertToSat(TNode lit, bool propagate) {
  // strip the not
  TNode atom;
  if (lit.getKind() == kind::NOT) {
    atom = lit[0];
  } else {
    atom = lit;
  }

  Assert (hasBBAtom(atom));

  prop::SatLiteral markerLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    markerLit = ~markerLit;
  }

  Debug("bitvector-bb") << "TheoryBV::TLazyBitblaster::assertToSat asserting node: " << atom <<"\n";
  Debug("bitvector-bb") << "TheoryBV::TLazyBitblaster::assertToSat with literal:   " << markerLit << "\n";

  prop::SatValue ret = d_satSolver->assertAssumption(markerLit, propagate);

  d_assertedAtoms.push_back(markerLit);

  Assert(ret != prop::SAT_VALUE_UNKNOWN);
  return ret == prop::SAT_VALUE_TRUE;
}

/**
 * Calls the solve method for the Sat Solver.
 * passing it the marker literals to be asserted
 *
 * @return true for sat, and false for unsat
 */

bool TLazyBitblaster::solve(bool quick_solve) {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "TLazyBitblaster::solve() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms.begin();
    for (; it != d_assertedAtoms.end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "TLazyBitblaster::solve() asserted atoms " << d_assertedAtoms.size() <<"\n";
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}

void TLazyBitblaster::getConflict(std::vector<TNode>& conflict) {
  prop::SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);

  for (unsigned i = 0; i < conflictClause.size(); i++) {
    prop::SatLiteral lit = conflictClause[i];
    TNode atom = d_cnfStream->getNode(lit);
    Node  not_atom;
    if (atom.getKind() == kind::NOT) {
      not_atom = atom[0];
    } else {
      not_atom = NodeManager::currentNM()->mkNode(kind::NOT, atom);
    }
    conflict.push_back(not_atom);
  }
}

TLazyBitblaster::Statistics::Statistics() :
  d_numTermClauses("theory::bv::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::NumberOfAtomSatClauses", 0),
  d_numTerms("theory::bv::NumberOfBitblastedTerms", 0),
  d_numAtoms("theory::bv::NumberOfBitblastedAtoms", 0),
  d_bitblastTimer("theory::bv::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_numTerms);
  StatisticsRegistry::registerStat(&d_numAtoms);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


TLazyBitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_numTerms);
  StatisticsRegistry::unregisterStat(&d_numAtoms);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}

bool TLazyBitblaster::MinisatNotify::notify(prop::SatLiteral lit) {
  return d_bv->storePropagation(d_cnf->getNode(lit), SUB_BITBLAST);
};

void TLazyBitblaster::MinisatNotify::notify(prop::SatClause& clause) {
  if (clause.size() > 1) {
    NodeBuilder<> lemmab(kind::OR);
    for (unsigned i = 0; i < clause.size(); ++ i) {
      lemmab << d_cnf->getNode(clause[i]);
    }
    Node lemma = lemmab;
    d_bv->d_out->lemma(lemma);
  } else {
    d_bv->d_out->lemma(d_cnf->getNode(clause[0]));
  }
};

void TLazyBitblaster::MinisatNotify::safePoint() {
  d_bv->d_out->safePoint();
}

EqualityStatus TLazyBitblaster::getEqualityStatus(TNode a, TNode b) {

  // We don't want to bit-blast every possibly expensive term for the sake of equality checking
  if (hasBBTerm(a) && hasBBTerm(b)) {

  Bits a_bits, b_bits;
  getBBTerm(a, a_bits);
  getBBTerm(b, b_bits);
  theory::EqualityStatus status = theory::EQUALITY_TRUE_IN_MODEL;
  for (unsigned i = 0; i < a_bits.size(); ++ i) {
    if (d_cnfStream->hasLiteral(a_bits[i]) && d_cnfStream->hasLiteral(b_bits[i])) {
      prop::SatLiteral a_lit = d_cnfStream->getLiteral(a_bits[i]);
      prop::SatValue a_lit_value = d_satSolver->value(a_lit);
      if (a_lit_value != prop::SAT_VALUE_UNKNOWN) {
        prop::SatLiteral b_lit = d_cnfStream->getLiteral(b_bits[i]);
        prop::SatValue b_lit_value = d_satSolver->value(b_lit);
        if (b_lit_value != prop::SAT_VALUE_UNKNOWN) {
          if (a_lit_value != b_lit_value) {
            return theory::EQUALITY_FALSE_IN_MODEL;
          }
        } else {
          status = theory::EQUALITY_UNKNOWN;
        }
      } {
        status = theory::EQUALITY_UNKNOWN;
      }
    } else {
      status = theory::EQUALITY_UNKNOWN;
    }
  }

  return status;

  } else {
    return theory::EQUALITY_UNKNOWN;
  }
}


bool TLazyBitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end();
}

bool TLazyBitblaster::hasValue(TNode a) {
  Assert (hasBBTerm(a)); 
  Bits bits;
  getBBTerm(a, bits); 
  for (int i = bits.size() -1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      if (bit_value ==  prop::SAT_VALUE_UNKNOWN)
        return false;
    } else {
      return false;
    }
  }
  return true;
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
Node TLazyBitblaster::getVarValue(TNode a, bool fullModel) {
  if (!hasBBTerm(a)) {
    Assert(isSharedTerm(a));
    return Node();
  }
  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() -1; i >= 0; --i) {
     prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
       prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert (bit_value != prop::SAT_VALUE_UNKNOWN);
    } else {
      //TODO: return Node() if fullModel=false?
      // the bit is unconstrainted so we can give it an arbitrary value
      bit_value = prop::SAT_VALUE_FALSE;
    }
    Integer bit_int = bit_value == prop::SAT_VALUE_TRUE ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(BitVector(bits.size(), value));
}

void TLazyBitblaster::collectModelInfo(TheoryModel* m, bool fullModel) {
  __gnu_cxx::hash_set<TNode, TNodeHashFunction>::iterator it = d_variables.begin();
  for (; it!= d_variables.end(); ++it) {
    TNode var = *it;
    if (Theory::theoryOf(var) == theory::THEORY_BV || isSharedTerm(var))  {
      Node const_value = getVarValue(var, fullModel);
      if(const_value == Node()) {
        if( fullModel ){
          // if the value is unassigned just set it to zero
          const_value = utils::mkConst(BitVector(utils::getSize(var), 0u));
        }
      }
      if(const_value != Node()) {
        Debug("bitvector-model") << "TLazyBitblaster::collectModelInfo (assert (= "
                                  << var << " "
                                  << const_value << "))\n";
        m->assertEquality(var, const_value, true);
      }
    }
  }
}

} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

#endif
