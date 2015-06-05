/*********************                                                        */
/*! \file riss.cpp
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
 ** Implementation of the riss sat solver for cvc4 (bitvectors).
 **/

#include "prop/riss.h"
#include "smt/options.h"

using namespace CVC4;
using namespace prop;

RissSolver::RissSolver(const std::string& name)
  : d_config()
  , d_solver(new RissMinisat::SimpSolver(d_config))
  , d_statistics(name)
{
  if (CVC4::options::produceModels()) {
    // FIXME: we don't want to freeze everything
    d_solver->use_elim  = false;
  }
  d_statistics.init(d_solver);
  d_true = newVar();
  d_false = newVar();
  d_solver->addClause(RissMinisat::mkLit(d_true, false));
  d_solver->addClause(RissMinisat::mkLit(d_false, true));
}


RissSolver::~RissSolver() throw(AssertionException) {
  delete d_solver;
}

void RissSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Debug("sat::glucose") << "Add clause " << clause <<"\n";

  if (!d_solver->okay()) {
    Debug("sat::glucose") << "Solver unsat: not adding clause.\n";
    return;
  }
  
  ++(d_statistics.d_clausesAdded);
  
  RissMinisat::vec<RissMinisat::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  d_solver->addClause(internal_clause); // check return status?
}

SatVariable  RissSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  return d_solver->newVar();
}

SatVariable RissSolver::trueVar() {
  return d_true;
}

SatVariable RissSolver::falseVar() {
  return d_false;
}

void RissSolver::markUnremovable(SatLiteral lit) {
  d_solver->setFrozen(lit.getSatVariable(), true);
  return;
}

void RissSolver::interrupt(){
  d_solver->interrupt();
}

SatValue RissSolver::solve(){
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve());
}

SatValue RissSolver::solve(long unsigned int& resource) {
  if(resource == 0) {
    d_solver->budgetOff();
  } else {
    d_solver->setConfBudget(resource);
  }
  return solve();
}

SatValue RissSolver::value(SatLiteral l){
  Assert (! d_solver->isEliminated(RissMinisat::var(toInternalLit(l))));
  return toSatLiteralValue(d_solver->value(toInternalLit(l)));
}

SatValue RissSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_solver->modelValue(toInternalLit(l)));
}

unsigned RissSolver::getAssertionLevel() const {
  Unreachable("No interface to get assertion level in Riss");
  return -1; 
}

// converting from internal sat solver representation

SatVariable RissSolver::toSatVariable(RissMinisat::Var var) {
  if (var == RissMinisat::Var(-1)) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

RissMinisat::Lit RissSolver::toInternalLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return RissMinisat::lit_Undef;
  }
  return RissMinisat::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral RissSolver::toSatLiteral(RissMinisat::Lit lit) {
  if (lit == RissMinisat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(RissMinisat::var(lit)),
                    RissMinisat::sign(lit));
}

SatValue RissSolver::toSatLiteralValue(RissMinisat::lbool res) {
  if(res == RissMinisat::lbool((uint8_t)0)/*RissMinisat::l_True*/) return SAT_VALUE_TRUE;
  if(res == RissMinisat::lbool((uint8_t)2)/*RissMinisat::l_Undef*/) return SAT_VALUE_UNKNOWN;
  Assert(res == RissMinisat::lbool((uint8_t)1)/*RissMinisat::l_False*/);
  return SAT_VALUE_FALSE;
}

SatValue RissSolver::toSatLiteralValue(bool res) {
  if(res) return SAT_VALUE_TRUE;
  return SAT_VALUE_FALSE;
}


void RissSolver::toInternalClause(SatClause& clause,
                                           RissMinisat::vec<RissMinisat::Lit>& internal_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    internal_clause.push(toInternalLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)internal_clause.size());
}

void RissSolver::toSatClause(RissMinisat::vec<RissMinisat::Lit>& clause,
				SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


// Satistics for RissSolver

RissSolver::Statistics::Statistics(const std::string& prefix) :
  // d_statStarts("theory::bv::"+prefix+"::glucose::starts"),
  // d_statDecisions("theory::bv::"+prefix+"::glucose::decisions"),
  // d_statRndDecisions("theory::bv::"+prefix+"::glucose::rnd_decisions"),
  // d_statPropagations("theory::bv::"+prefix+"::glucose::propagations"),
  // d_statConflicts("theory::bv::"+prefix+"::glucose::conflicts"),
  // d_statClausesLiterals("theory::bv::"+prefix+"::glucose::clauses_literals"),
  // d_statLearntsLiterals("theory::bv::"+prefix+"::glucose::learnts_literals"),
  // d_statMaxLiterals("theory::bv::"+prefix+"::glucose::max_literals"),
  // d_statTotLiterals("theory::bv::"+prefix+"::glucose::tot_literals"),
  // d_statEliminatedVars("theory::bv::"+prefix+"::glucose::eliminated_vars"),
  d_statCallsToSolve("theory::bv::"+prefix+"::glucose::calls_to_solve", 0),
  d_xorClausesAdded("theory::bv::"+prefix+"::glucose::xor_clauses", 0),
  d_clausesAdded("theory::bv::"+prefix+"::glucose::clauses", 0),
  // d_statSolveTime("theory::bv::"+prefix+"::glucose::solve_time", 0),
  d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
    return;

  // StatisticsRegistry::registerStat(&d_statStarts);
  // StatisticsRegistry::registerStat(&d_statDecisions);
  // StatisticsRegistry::registerStat(&d_statRndDecisions);
  // StatisticsRegistry::registerStat(&d_statPropagations);
  // StatisticsRegistry::registerStat(&d_statConflicts);
  // StatisticsRegistry::registerStat(&d_statClausesLiterals);
  // StatisticsRegistry::registerStat(&d_statLearntsLiterals);
  // StatisticsRegistry::registerStat(&d_statMaxLiterals);
  // StatisticsRegistry::registerStat(&d_statTotLiterals);
  // StatisticsRegistry::registerStat(&d_statEliminatedVars);
  StatisticsRegistry::registerStat(&d_statCallsToSolve);
  StatisticsRegistry::registerStat(&d_xorClausesAdded);
  StatisticsRegistry::registerStat(&d_clausesAdded);
  // StatisticsRegistry::registerStat(&d_statSolveTime);
}

RissSolver::Statistics::~Statistics() {
  if (!d_registerStats)
    return;
  // StatisticsRegistry::unregisterStat(&d_statStarts);
  // StatisticsRegistry::unregisterStat(&d_statDecisions);
  // StatisticsRegistry::unregisterStat(&d_statRndDecisions);
  // StatisticsRegistry::unregisterStat(&d_statPropagations);
  // StatisticsRegistry::unregisterStat(&d_statConflicts);
  // StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
  // StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
  // StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
  // StatisticsRegistry::unregisterStat(&d_statTotLiterals);
  // StatisticsRegistry::unregisterStat(&d_statEliminatedVars);
  StatisticsRegistry::unregisterStat(&d_statCallsToSolve);
  StatisticsRegistry::unregisterStat(&d_xorClausesAdded);
  StatisticsRegistry::unregisterStat(&d_clausesAdded);
  // StatisticsRegistry::unregisterStat(&d_statSolveTime);
}

void RissSolver::Statistics::init(RissMinisat::SimpSolver* solver){
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
