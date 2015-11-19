/*********************                                                        */
/*! \file bitvector_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector proof
 **
 ** Bitvector proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITVECTOR__PROOF_H
#define __CVC4__BITVECTOR__PROOF_H

#include <iostream>
#include <stdint.h>
#include <vector>
#include <set>
#include <ext/hash_map>
#include <ext/hash_set>
#include <sstream>
#include "expr/expr.h"
#include "proof/theory_proof.h"
#include "prop/bvminisat/core/Solver.h"

// namespace BVMinisat {
// class Solver;
// }

namespace CVC4 {

namespace prop {
class CnfStream;
}
namespace theory {
namespace bv{
class TheoryBV;
template <class T> class TBitblaster;
}
}

class CnfProof;

template <class Solver> class TSatProof;
typedef TSatProof< ::BVMinisat::Solver> BVSatProof;

template <class Solver> class LFSCSatProof;
typedef LFSCSatProof< ::BVMinisat::Solver> LFSCBVSatProof;

typedef __gnu_cxx::hash_set<Expr, ExprHashFunction> ExprSet;
typedef __gnu_cxx::hash_map<Expr, ClauseId, ExprHashFunction> ExprToClauseId;
typedef __gnu_cxx::hash_map<Expr, unsigned, ExprHashFunction> ExprToId;
typedef __gnu_cxx::hash_map<Expr, Expr, ExprHashFunction> ExprToExpr;

class BitVectorProof : public TheoryProof {
protected:
  ExprSet d_declarations;

  // ExprToId d_terms; // bit-vector terms appearing in the problem
  // ExprToId d_atoms; // bit-vector atoms appearing in the problem

  ExprSet d_usedBB; // terms and formulas that are actually relevant to the proof

  ExprSet d_seenBBTerms; // terms that need to be bit-blasted
  std::vector<Expr> d_bbTerms; // order of bit-blasting
  ExprToExpr d_bbAtoms; // atoms that need to be bit-blasted

  //  unsigned d_bbIdCount;

  // map from Expr representing normalized lemma to ClauseId in SAT solver
  ExprToClauseId d_bbConflictMap;
  BVSatProof* d_resolutionProof;

  CnfProof* d_cnfProof;

  bool d_isAssumptionConflict;
  theory::bv::TBitblaster<Node>* d_bitblaster;
  // unsigned newBBId();
  // unsigned getBBId(Expr expr);
  std::string getBBTermName(Expr expr);
public:
  BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine);

  void initSatProof(::BVMinisat::Solver* solver);
  void initCnfProof(prop::CnfStream* cnfStream, context::Context* ctx);
  void setBitblaster(theory::bv::TBitblaster<Node>* bb);

  BVSatProof* getSatProof();
  CnfProof* getCnfProof() {return d_cnfProof; }
  void finalizeConflicts(std::vector<Expr>& conflicts);

  void startBVConflict(::BVMinisat::Solver::TCRef cr);
  void startBVConflict(::BVMinisat::Solver::TLit lit);
  /**
   * All the
   *
   * @param confl an inconsistent set of bv literals
   */
  void endBVConflict(const BVMinisat::Solver::TLitVec& confl);
  void markAssumptionConflict() { d_isAssumptionConflict = true; }
  bool isAssumptionConflict() { return d_isAssumptionConflict; }

  void registerTermBB(Expr term);
  void registerAtomBB(Expr atom, Expr atom_bb);

  virtual void registerTerm(Expr term);

  virtual void printTermBitblasting(Expr term, std::ostream& os) = 0;
  virtual void printAtomBitblasting(Expr term, std::ostream& os) = 0;
  
  virtual void printBitblasting(std::ostream& os, std::ostream& paren) = 0;
  virtual void printResolutionProof(std::ostream& os, std::ostream& paren) = 0;

};

class LFSCBitVectorProof: public BitVectorProof {

  void printConstant(Expr term, std::ostream& os);
  void printOperatorNary(Expr term, std::ostream& os, const LetMap& map);
  void printOperatorUnary(Expr term, std::ostream& os, const LetMap& map);
  void printPredicate(Expr term, std::ostream& os, const LetMap& map);
  void printOperatorParametric(Expr term, std::ostream& os, const LetMap& map);
  void printBitOf(Expr term, std::ostream& os);
public:
  LFSCBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    :BitVectorProof(bv, proofEngine)
  {}
  virtual void printTerm(Expr term, std::ostream& os, const LetMap& map);
  virtual void printSort(Type type, std::ostream& os);
  virtual void printTermBitblasting(Expr term, std::ostream& os);
  virtual void printAtomBitblasting(Expr term, std::ostream& os);
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren);
  virtual void printDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printBitblasting(std::ostream& os, std::ostream& paren);
  virtual void printResolutionProof(std::ostream& os, std::ostream& paren);
};

}/* CVC4 namespace */

#endif /* __CVC4__BITVECTOR__PROOF_H */