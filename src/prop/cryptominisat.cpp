/*********************                                                        */
/*! \file cryptominisat.cpp
 ** \verbatim
 ** Original author: lianah
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
 ** Implementation of the cryptominisat for cvc4 (bitvectors).
 **/

#include "prop/cryptominisat.h"

using namespace CVC4;
using namespace prop;

CryptoMinisatSolver::CryptoMinisatSolver(const std::string& name)
: d_solver(new CMSat::SATSolver())
, d_numVariables(0)
, d_statistics(name)
{
  d_statistics.init(d_solver); 
}


CryptoMinisatSolver::~CryptoMinisatSolver() throw(AssertionException) {
  delete d_solver;
}

void CryptoMinisatSolver::addXorClause(SatClause& clause,
				       bool rhs,
				       bool removable,
				       uint64_t proof_id) {
  Debug("sat::cryptominisat") << "Add xor clause " << clause <<" = " << rhs << "\n";
  // ensure all sat literals have positive polarity by pushing
  // the negation on the result
  std::vector<CMSat::Var> xor_clause;
  for (unsigned i = 0; i < clause.size(); ++i) {
    xor_clause.push_back(clause[i].getSatVariable());
    rhs ^= clause[i].isNegated();
  }
  d_solver->add_xor_clause(xor_clause, rhs); // check return status?
}

void CryptoMinisatSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Debug("sat::cryptominisat") << "Add clause " << clause <<"\n";
  std::vector<CMSat::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  d_solver->add_clause(internal_clause); // check return status?
}

SatVariable  CryptoMinisatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  d_solver->new_var();
  ++d_numVariables;
  Assert (d_numVariables == d_solver->nVars());
  return d_numVariables - 1;
}

SatVariable CryptoMinisatSolver::trueVar() {
  SatVariable v = newVar();
  std::vector<CMSat::Lit> clause;
  clause.push_back(CMSat::Lit(v, false));
  d_solver->add_clause(clause);
  return v;
}

SatVariable CryptoMinisatSolver::falseVar() {
  SatVariable v = newVar();
  std::vector<CMSat::Lit> clause;
  clause.push_back(CMSat::Lit(v, true));
  d_solver->add_clause(clause);
  return v;
}

void CryptoMinisatSolver::markUnremovable(SatLiteral lit) {
  // cryptominisat supports dynamically adding back variables (?)
  // so this is a no-op
  return;
}

void CryptoMinisatSolver::interrupt(){
  d_solver->interrupt_asap();
}

SatValue CryptoMinisatSolver::solve(){
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve());
}

SatValue CryptoMinisatSolver::solve(long unsigned int& resource) {
  // CMSat::SalverConf conf = d_solver->getConf();
  Unreachable("Not sure how to set different limits for calls to solve in Cryptominisat"); 
  return solve();
}

SatValue CryptoMinisatSolver::value(SatLiteral l){
  const std::vector<CMSat::lbool> model = d_solver->get_model();
  CMSat::Var var = l.getSatVariable();
  Assert (var < model.size());
  CMSat::lbool value = model[var];
  return toSatLiteralValue(value);
}

SatValue CryptoMinisatSolver::modelValue(SatLiteral l){
  return value(l); 
}

unsigned CryptoMinisatSolver::getAssertionLevel() const {
  Unreachable("No interface to get assertion level in Cryptominisat");
  return -1; 
}

// converting from internal sat solver representation

SatVariable CryptoMinisatSolver::toSatVariable(CMSat::Var var) {
  if (var == CMSat::var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

CMSat::Lit CryptoMinisatSolver::toInternalLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return CMSat::lit_Undef;
  }
  return CMSat::Lit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral CryptoMinisatSolver::toSatLiteral(CMSat::Lit lit) {
  Assert (lit != CMSat::lit_Error);
  if (lit == CMSat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(lit.var()),
                    lit.sign());
}

SatValue CryptoMinisatSolver::toSatLiteralValue(CMSat::lbool res) {
  if(res == CMSat::l_True) return SAT_VALUE_TRUE;
  if(res == CMSat::l_Undef) return SAT_VALUE_UNKNOWN;
  Assert(res == CMSat::l_False);
  return SAT_VALUE_FALSE;
}

void CryptoMinisatSolver::toInternalClause(SatClause& clause,
                                           std::vector<CMSat::Lit>& internal_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    internal_clause.push_back(toInternalLit(clause[i]));
  }
  Assert(clause.size() == internal_clause.size());
}

void CryptoMinisatSolver::toSatClause(std::vector<CMSat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert(clause.size() == sat_clause.size());
}


// Satistics for CryptoMinisatSolver

CryptoMinisatSolver::Statistics::Statistics(const std::string& prefix) :
  d_statStarts("theory::bv::"+prefix+"bvminisat::starts"),
  d_statDecisions("theory::bv::"+prefix+"bvminisat::decisions"),
  d_statRndDecisions("theory::bv::"+prefix+"bvminisat::rnd_decisions"),
  d_statPropagations("theory::bv::"+prefix+"bvminisat::propagations"),
  d_statConflicts("theory::bv::"+prefix+"bvminisat::conflicts"),
  d_statClausesLiterals("theory::bv::"+prefix+"bvminisat::clauses_literals"),
  d_statLearntsLiterals("theory::bv::"+prefix+"bvminisat::learnts_literals"),
  d_statMaxLiterals("theory::bv::"+prefix+"bvminisat::max_literals"),
  d_statTotLiterals("theory::bv::"+prefix+"bvminisat::tot_literals"),
  d_statEliminatedVars("theory::bv::"+prefix+"bvminisat::eliminated_vars"),
  d_statCallsToSolve("theory::bv::"+prefix+"bvminisat::calls_to_solve", 0),
  d_statSolveTime("theory::bv::"+prefix+"bvminisat::solve_time", 0),
  d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
    return;

  StatisticsRegistry::registerStat(&d_statStarts);
  StatisticsRegistry::registerStat(&d_statDecisions);
  StatisticsRegistry::registerStat(&d_statRndDecisions);
  StatisticsRegistry::registerStat(&d_statPropagations);
  StatisticsRegistry::registerStat(&d_statConflicts);
  StatisticsRegistry::registerStat(&d_statClausesLiterals);
  StatisticsRegistry::registerStat(&d_statLearntsLiterals);
  StatisticsRegistry::registerStat(&d_statMaxLiterals);
  StatisticsRegistry::registerStat(&d_statTotLiterals);
  StatisticsRegistry::registerStat(&d_statEliminatedVars);
  StatisticsRegistry::registerStat(&d_statCallsToSolve);
  StatisticsRegistry::registerStat(&d_statSolveTime);
}

CryptoMinisatSolver::Statistics::~Statistics() {
  if (!d_registerStats)
    return;
  StatisticsRegistry::unregisterStat(&d_statStarts);
  StatisticsRegistry::unregisterStat(&d_statDecisions);
  StatisticsRegistry::unregisterStat(&d_statRndDecisions);
  StatisticsRegistry::unregisterStat(&d_statPropagations);
  StatisticsRegistry::unregisterStat(&d_statConflicts);
  StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
  StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
  StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
  StatisticsRegistry::unregisterStat(&d_statTotLiterals);
  StatisticsRegistry::unregisterStat(&d_statEliminatedVars);
  StatisticsRegistry::unregisterStat(&d_statCallsToSolve);
  StatisticsRegistry::unregisterStat(&d_statSolveTime);
}

void CryptoMinisatSolver::Statistics::init(CMSat::SATSolver* solver){
  if (!d_registerStats)
    return;
  // FIXME seems to only have print stats no get stats
  
  // d_statStarts.setData(minisat->starts);
  // d_statDecisions.setData(minisat->decisions);
  // d_statRndDecisions.setData(minisat->rnd_decisions);
  // d_statPropagations.setData(minisat->propagations);
  // d_statConflicts.setData(minisat->conflicts);
  // d_statClausesLiterals.setData(minisat->clauses_literals);
  // d_statLearntsLiterals.setData(minisat->learnts_literals);
  // d_statMaxLiterals.setData(minisat->max_literals);
  // d_statTotLiterals.setData(minisat->tot_literals);
  // d_statEliminatedVars.setData(minisat->eliminated_vars);
}
