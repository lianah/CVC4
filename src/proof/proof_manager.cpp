/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
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

#include "proof/proof_manager.h"
#include "util/proof.h"
#include "proof/sat_proof.h"
#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "util/cvc4_assert.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/output_channel.h"
#include "theory/valuation.h"
#include "util/node_visitor.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/arrays/theory_arrays.h"
#include "context/context.h"
#include "util/hash.h"

namespace CVC4 {

std::string append(const std::string& str, uint64_t num) {
  std::ostringstream os;
  os << str << num;
  return os.str();
}

ProofManager::ProofManager(ProofFormat format):
  d_satProof(NULL),
  d_cnfProof(NULL),
  d_theoryProof(NULL),
  d_fullProof(NULL),
  d_format(format),
  d_deps()
{
}

ProofManager::~ProofManager() {
  delete d_satProof;
  delete d_cnfProof;
  delete d_theoryProof;
  delete d_fullProof;

  for(IdToClause::iterator it = d_inputClauses.begin();
      it != d_inputClauses.end();
      ++it) {
    delete it->second;
  }

  for(OrderedIdToClause::iterator it = d_theoryLemmas.begin();
      it != d_theoryLemmas.end();
      ++it) {
    delete it->second;
  }

  // FIXME: memory leak because there are deleted theory lemmas that
  // were not used in the SatProof
}

ProofManager* ProofManager::currentPM() {
  return smt::currentProofManager();
}

Proof* ProofManager::getProof(SmtEngine* smt) {
  if (currentPM()->d_fullProof != NULL) {
    return currentPM()->d_fullProof;
  }
  Assert (currentPM()->d_format == LFSC);

  currentPM()->d_fullProof = new LFSCProof(smt,
                                           (LFSCSatProof*)getSatProof(),
                                           (LFSCCnfProof*)getCnfProof(),
                                           (LFSCTheoryProof*)getTheoryProof());
  return currentPM()->d_fullProof;
}

SatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof;
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

TheoryProof* ProofManager::getTheoryProof() {
  //Assert (currentPM()->d_theoryProof);
  return currentPM()->d_theoryProof;
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new LFSCSatProof(solver);
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream) {
  Assert (currentPM()->d_cnfProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_cnfProof = new LFSCCnfProof(cnfStream);
}

void ProofManager::initTheoryProof() {
  Assert (currentPM()->d_theoryProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_theoryProof = new LFSCTheoryProof();
}

std::string ProofManager::getInputClauseName(ClauseId id) { return append("pb", id); }
std::string ProofManager::getLemmaName(ClauseId id) { return append("lem", id); }
std::string ProofManager::getLemmaClauseName(ClauseId id) { return append("lemc", id); }
std::string ProofManager::getLearntClauseName(ClauseId id) { return append("cl", id); }
std::string ProofManager::getVarName(prop::SatVariable var) { return append("var", var); }
std::string ProofManager::getAtomName(prop::SatVariable var) { return append("atom", var); }
std::string ProofManager::getLitName(prop::SatLiteral lit) { return append("lit", lit.toInt()); }

std::string ProofManager::getAtomName(TNode atom) {
  prop::SatLiteral lit = currentPM()->d_cnfProof->getLiteral(atom);
  Assert(!lit.isNegated());
  return getAtomName(lit.getSatVariable());
}
std::string ProofManager::getLitName(TNode lit) {
  return getLitName(currentPM()->d_cnfProof->getLiteral(lit));
}

void ProofManager::traceDeps(TNode n) {
  Debug("cores") << "trace deps " << n << std::endl;
  if(d_inputCoreFormulas.find(n.toExpr()) != d_inputCoreFormulas.end()) {
    // originating formula was in core set
    Debug("cores") << " -- IN INPUT CORE LIST!" << std::endl;
    d_outputCoreFormulas.insert(n.toExpr());
  } else {
    Debug("cores") << " -- NOT IN INPUT CORE LIST!" << std::endl;
    if(d_deps.find(n) == d_deps.end()) {
      InternalError("Cannot trace dependence information back to input assertion:\n`%s'", n.toString().c_str());
    }
    Assert(d_deps.find(n) != d_deps.end());
    std::vector<Node> deps = (*d_deps.find(n)).second;
    for(std::vector<Node>::const_iterator i = deps.begin(); i != deps.end(); ++i) {
      Debug("cores") << " + tracing deps: " << n << " -deps-on- " << *i << std::endl;
      traceDeps(*i);
    }
  }
}

void ProofManager::addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind) {
  /*for (unsigned i = 0; i < clause->size(); ++i) {
    prop::SatLiteral lit = clause->operator[](i);
    d_propVars.insert(lit.getSatVariable());
  }*/
  if (kind == INPUT) {
    d_inputClauses.insert(std::make_pair(id, clause));
    Assert(d_satProof->d_inputClauses.find(id) != d_satProof->d_inputClauses.end());
    Debug("cores") << "core id is " << d_satProof->d_inputClauses[id] << std::endl;
    if(d_satProof->d_inputClauses[id] == uint64_t(-1)) {
      Debug("cores") << " + constant unit (true or false)" << std::endl;
    } else if(options::unsatCores()) {
      Expr e = d_cnfProof->getAssertion(d_satProof->d_inputClauses[id] & 0xffffffff);
      Debug("cores") << "core input assertion from CnfStream is " << e << std::endl;
      Debug("cores") << "with proof rule " << ((d_satProof->d_inputClauses[id] & 0xffffffff00000000llu) >> 32) << std::endl;
      // Invalid proof rules are currently used for parts of CVC4 that don't
      // support proofs (these are e.g. unproven theory lemmas) or don't need
      // proofs (e.g. split lemmas).  We can ignore these safely when
      // constructing unsat cores.
      if(((d_satProof->d_inputClauses[id] & 0xffffffff00000000llu) >> 32) != RULE_INVALID) {
        // trace dependences back to actual assertions
        traceDeps(Node::fromExpr(e));
      }
    }
  } else {
    Assert(kind == THEORY_LEMMA);
    d_theoryLemmas.insert(std::make_pair(id, clause));
  }
}

void ProofManager::addAssertion(Expr formula, bool inUnsatCore) {
  Debug("cores") << "assert: " << formula << std::endl;
  d_inputFormulas.insert(formula);
  d_deps[Node::fromExpr(formula)]; // empty vector of deps
  if(inUnsatCore || options::dumpUnsatCores() || options::checkUnsatCores()) {
    Debug("cores") << "adding to input core forms: " << formula << std::endl;
    d_inputCoreFormulas.insert(formula);
  }
}

void ProofManager::addDependence(TNode n, TNode dep) {
  if(dep != n) {
    Debug("cores") << "dep: " << n << " : " << dep << std::endl;
    if(d_deps.find(dep) == d_deps.end()) {
      Debug("cores") << "WHERE DID " << dep << " come from ??" << std::endl;
    }
    //Assert(d_deps.find(dep) != d_deps.end());
    d_deps[n].push_back(dep);
  }
}

void ProofManager::setLogic(const LogicInfo& logic) {
  d_logic = logic;
}

void ProofManager::printProof(std::ostream& os, TNode n) {
  // no proofs here yet
}

LFSCProof::LFSCProof(SmtEngine* smtEngine, LFSCSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProof* theory)
  : d_satProof(sat)
  , d_cnfProof(cnf)
  , d_theoryProof(theory)
  , d_smtEngine(smtEngine)
{
  d_satProof->constructProof();
}

void LFSCProof::toStream(std::ostream& out) {
  smt::SmtScope scope(d_smtEngine);
  std::ostringstream paren;
  out << "(check\n";
  out << " ;; Declarations\n";
  if (d_theoryProof == NULL) {
    d_theoryProof = new LFSCTheoryProof();
  }
  /*for(LFSCCnfProof::iterator i = d_cnfProof->begin_atom_mapping();
      i != d_cnfProof->end_atom_mapping();
      ++i) {
    d_theoryProof->addDeclaration(*i);
  }*/
  d_theoryProof->printAssertions(out, paren);
  out << " ;; Proof of empty clause follows\n";
  out << "(: (holds cln)\n";
  d_cnfProof->printClauses(out, paren);
  d_satProof->printResolutions(out, paren);
  paren <<")))\n;;";
  out << paren.str();
  out << "\n";
}

} /* CVC4  namespace */
