/*********************                                                        */
/*! \file glucose.cpp
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
 ** Implementation of the glucose sat solver for cvc4 (bitvectors).
 **/

#include "prop/glucose.h"
#include "smt/options.h"

using namespace CVC4;
using namespace prop;

GlucoseSolver::GlucoseSolver(const std::string& name)
: d_solver(new Glucose::SimpSolver())
, d_statistics(name)
{
  d_solver->verbosity = -1;
  if (CVC4::options::produceModels()) {
    // FIXME: we don't want to freeze everything
    d_solver->use_elim  = false;
  }
  d_statistics.init(d_solver);
  d_true = newVar();
  d_false = newVar();
  d_solver->addClause(Glucose::mkLit(d_true, false));
  d_solver->addClause(Glucose::mkLit(d_false, true));
}


GlucoseSolver::~GlucoseSolver() throw(AssertionException) {
  delete d_solver;
}

void GlucoseSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Debug("sat::glucose") << "Add clause " << clause <<"\n";

  if (!d_solver->okay()) {
    Debug("sat::glucose") << "Solver unsat: not adding clause.\n";
    return;
  }
  
  ++(d_statistics.d_clausesAdded);
  
  Glucose::vec<Glucose::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  d_solver->addClause(internal_clause); // check return status?
}

SatVariable  GlucoseSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  return d_solver->newVar();
}

SatVariable GlucoseSolver::trueVar() {
  return d_true;
}

SatVariable GlucoseSolver::falseVar() {
  return d_false;
}

void GlucoseSolver::markUnremovable(SatLiteral lit) {
  d_solver->setFrozen(lit.getSatVariable(), true);
  return;
}

void GlucoseSolver::interrupt(){
  d_solver->interrupt();
}

SatValue GlucoseSolver::solve(){
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve());
}

SatValue GlucoseSolver::solve(long unsigned int& resource) {
  if(resource == 0) {
    d_solver->budgetOff();
  } else {
    d_solver->setConfBudget(resource);
  }
  return solve();
}

SatValue GlucoseSolver::value(SatLiteral l){
  Assert (! d_solver->isEliminated(Glucose::var(toInternalLit(l))));
  // For some reason value returns unknown for glucose
  return toSatLiteralValue(d_solver->modelValue(toInternalLit(l)));
}

SatValue GlucoseSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_solver->modelValue(toInternalLit(l)));
}

unsigned GlucoseSolver::getAssertionLevel() const {
  Unreachable("No interface to get assertion level in Glucose");
  return -1; 
}

// converting from internal sat solver representation

SatVariable GlucoseSolver::toSatVariable(Glucose::Var var) {
  if (var == Glucose::Var(-1)) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

Glucose::Lit GlucoseSolver::toInternalLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return Glucose::lit_Undef;
  }
  return Glucose::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral GlucoseSolver::toSatLiteral(Glucose::Lit lit) {
  if (lit == Glucose::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(Glucose::var(lit)),
                    Glucose::sign(lit));
}

SatValue GlucoseSolver::toSatLiteralValue(Glucose::lbool res) {
  if(res == Glucose::lbool((uint8_t)0)/*Glucose::l_True*/) return SAT_VALUE_TRUE;
  if(res == Glucose::lbool((uint8_t)2)/*Glucose::l_Undef*/) return SAT_VALUE_UNKNOWN;
  Assert(res == Glucose::lbool((uint8_t)1)/*Glucose::l_False*/);
  return SAT_VALUE_FALSE;
}

SatValue GlucoseSolver::toSatLiteralValue(bool res) {
  if(res) return SAT_VALUE_TRUE;
  return SAT_VALUE_FALSE;
}


void GlucoseSolver::toInternalClause(SatClause& clause,
                                           Glucose::vec<Glucose::Lit>& internal_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    internal_clause.push(toInternalLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)internal_clause.size());
}

void GlucoseSolver::toSatClause(Glucose::vec<Glucose::Lit>& clause,
				SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


// Satistics for GlucoseSolver

GlucoseSolver::Statistics::Statistics(const std::string& prefix) :
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

GlucoseSolver::Statistics::~Statistics() {
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

void GlucoseSolver::Statistics::init(Glucose::SimpSolver* solver){
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
