/*********************                                                        */
/*! \file bvminisat.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2014  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include "prop/sat_solver.h"
#include <cryptominisat4/cryptominisat.h>

namespace CVC4 {
namespace prop {

class CryptoMinisatSolver : public SatSolver {

private:
  CMSat::SATSolver* d_solver;
  unsigned d_numVariables;
public:
  CryptoMinisatSolver(const std::string& name = "");
  ~CryptoMinisatSolver() throw(AssertionException);

  void addClause(SatClause& clause, bool removable, uint64_t proof_id);
  void addXorClause(SatClause& clause, bool rhs, bool removable, uint64_t proof_id);

  SatVariable newVar(bool isTheoryAtom = false, bool preRegister = false, bool canErase = true);

  SatVariable trueVar();
  SatVariable falseVar();

  void markUnremovable(SatLiteral lit);

  void interrupt();
  
  SatValue solve();
  SatValue solve(long unsigned int&);
  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);

  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal Minisat representation

  static SatVariable toSatVariable(CMSat::Var var);
  static CMSat::Lit toInternalLit(SatLiteral lit);
  static SatLiteral toSatLiteral(CMSat::Lit lit);
  static SatValue toSatLiteralValue(bool res);
  static SatValue toSatLiteralValue(CMSat::lbool res);

  static void  toInternalClause(SatClause& clause, std::vector<CMSat::Lit>& internal_clause);
  static void  toSatClause (std::vector<CMSat::Lit>& clause, SatClause& sat_clause);

  class Statistics {
  public:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
    ReferenceStat<int> d_statEliminatedVars;
    IntStat d_statCallsToSolve;
    BackedStat<double> d_statSolveTime;
    bool d_registerStats;
    Statistics(const std::string& prefix);
    ~Statistics();
    void init(CMSat::SATSolver* cryptominisat);
  };

  Statistics d_statistics;
};

}
}




