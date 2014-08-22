/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for Proofs
 **
 ** A manager for Proofs.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_MANAGER_H
#define __CVC4__PROOF_MANAGER_H

#include <iostream>
#include "proof/proof.h"
#include "util/proof.h"


// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace CVC4 {

namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class SmtEngine;

typedef int ClauseId;

class Proof;
template <class Solver> class TSatProof; 
typedef TSatProof< ::Minisat::Solver> CoreSatProof;
class CnfProof;
class TheoryProofEngine;
class UFProof;
class ArrayProof;
class BitVectorProof;

template <class Solver> class LFSCSatProof; 
typedef LFSCSatProof< ::Minisat::Solver> LFSCCoreSatProof;
class LFSCCnfProof;
class LFSCTheoryProofEngine;
class LFSCUFProof;
class LFSCBitVectorProof;

template <class Solver> class ProofProxy;
typedef ProofProxy< ::Minisat::Solver> CoreProofProxy; 

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
}/* CVC4::prop namespace */

// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};/* enum ProofFormat */

std::string append(const std::string& str, uint64_t num);

typedef __gnu_cxx::hash_map < ClauseId, const prop::SatClause* > IdToClause;
typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > ExprSet;
typedef __gnu_cxx::hash_set<prop::SatVariable> SatVarSet;
typedef __gnu_cxx::hash_map<Expr, prop::SatVariable, ExprHashFunction > ExprToSatVar;
typedef __gnu_cxx::hash_map<prop::SatVariable, Expr> SatVarToExpr;

typedef int ClauseId;

enum ClauseKind {
  INPUT,
  THEORY_LEMMA,
  LEARNT
};/* enum ClauseKind */

class ProofManager {
  CoreSatProof*    d_satProof;
  CnfProof*    d_cnfProof;
  TheoryProofEngine* d_theoryProof;

  // information that will need to be shared across proofs
  IdToClause d_inputClauses;
  IdToClause d_theoryLemmas;
  ExprSet    d_inputFormulas;
  ExprToSatVar d_atomToSatVar;
  SatVarToExpr d_satVarToAtom;
  SatVarSet d_propVars;
  Proof* d_fullProof;
  ProofFormat d_format; // used for now only in debug builds

protected:
  std::string d_logic;

public:
  ProofManager(ProofFormat format = LFSC);
  ~ProofManager();

  static ProofManager* currentPM();

  // initialization
  static void         initSatProof(Minisat::Solver* solver);
  static void         initCnfProof(CVC4::prop::CnfStream* cnfStream);
  static void         initTheoryProofEngine();

  // getting various proofs
  static Proof*         getProof(SmtEngine* smt);
  static CoreSatProof*  getSatProof();
  static CnfProof*      getCnfProof();
  static TheoryProofEngine* getTheoryProofEngine();
  
  static UFProof* getUfProof();
  static BitVectorProof* getBitVectorProof();
  static ArrayProof* getArrayProof();
  
  // iterators over data shared by proofs
  typedef IdToClause::const_iterator clause_iterator;
  typedef ExprSet::const_iterator assertions_iterator;
  typedef ExprToSatVar::const_iterator atom_iterator;
  typedef SatVarToExpr::const_iterator var_iterator;

  // iterate over the problem clauses
  clause_iterator begin_input_clauses() const { return d_inputClauses.begin(); }
  clause_iterator end_input_clauses() const { return d_inputClauses.end(); }

  // iterate over the theory lemmas
  clause_iterator begin_lemmas() const { return d_theoryLemmas.begin(); }
  clause_iterator end_lemmas() const { return d_theoryLemmas.end(); }

  // iterate over the assertions (these are arbitrary boolean formulas)
  assertions_iterator begin_assertions() const { return d_inputFormulas.begin(); }
  assertions_iterator end_assertions() const { return d_inputFormulas.end(); }

  // iterate over all theory atoms
  atom_iterator begin_atoms() const { return d_atomToSatVar.begin(); }
  atom_iterator end_atoms() const { return d_atomToSatVar.end(); }

  // iterate over all sat variables
  var_iterator begin_vars() const { return d_satVarToAtom.begin(); }
  var_iterator end_vars() const { return d_satVarToAtom.end(); }

  prop::SatVariable getSatVarForAtom(Expr atom) {
    Assert (d_atomToSatVar.find(atom) != d_atomToSatVar.end()); 
    return d_atomToSatVar.find(atom)->second;
  }
  Expr getAtomForSatVar(prop::SatVariable var) {
    Assert (d_satVarToAtom.find(var) != d_satVarToAtom.end()); 
    return d_satVarToAtom.find(var)->second;
  }

  void registerTheoryAtom(Expr atom, prop::SatVariable var);
  
  void addAssertion(Expr formula);
  void addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind);

  // variable prefixes
  static std::string getInputClauseName(ClauseId id);
  static std::string getLemmaClauseName(ClauseId id);
  static std::string getLearntClauseName(ClauseId id);

  static std::string getVarName(prop::SatVariable var);
  static std::string getAtomName(prop::SatVariable var);
  static std::string getLitName(prop::SatLiteral lit);

  void setLogic(const std::string& logic_string);
  const std::string getLogic() const { return d_logic; }

  
};/* class ProofManager */

class LFSCProof : public Proof {
  LFSCCoreSatProof* d_satProof;
  LFSCCnfProof* d_cnfProof;
  LFSCTheoryProofEngine* d_theoryProof;
  SmtEngine* d_smtEngine;
public:
  LFSCProof(SmtEngine* smtEngine, LFSCCoreSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProofEngine* theory);
  virtual void toStream(std::ostream& out);
  virtual ~LFSCProof() {}
};/* class LFSCProof */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_MANAGER_H */
