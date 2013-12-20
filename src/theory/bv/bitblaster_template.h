/*********************                                                        */
/*! \file bitblaster.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): lianah, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Wrapper around the SAT solver used for bitblasting
 **
 ** Wrapper around the SAT solver used for bitblasting.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLASTER_TEMPLATE_H
#define __CVC4__BITBLASTER_TEMPLATE_H


#include "expr/node.h"
#include <vector>
#include <ext/hash_map>

#include "bitblast_strategies_template.h"
#include "prop/sat_solver.h"
#include "theory/valuation.h"

class Abc_Obj_t_;
typedef Abc_Obj_t_ Abc_Obj_t;

class Abc_Ntk_t_;
typedef Abc_Ntk_t_ Abc_Ntk_t;

class Abc_Aig_t_;
typedef Abc_Aig_t_ Abc_Aig_t;

class Cnf_Dat_t_;
typedef Cnf_Dat_t_ Cnf_Dat_t;


namespace CVC4 {
namespace prop {
class CnfStream;
class BVSatSolverInterface;
}

namespace theory {
class OutputChannel;
class TheoryModel;

namespace bv {


class AbstractionModule;

/**
 * The Bitblaster that manages the mapping between Nodes
 * and their bitwise definition
 *
 */

template <class T>
class TBitblaster {
protected:
  typedef std::vector<T> Bits;
  typedef __gnu_cxx::hash_map <Node, Bits, TNodeHashFunction>  TermDefMap;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction>        AtomSet;

  typedef void  (*TermBBStrategy) (TNode, Bits&, TBitblaster<T>*);
  typedef T     (*AtomBBStrategy) (TNode, TBitblaster<T>*);

  // caches and mappings
  TermDefMap                   d_termCache;

  void initAtomBBStrategies();
  void initTermBBStrategies();
protected:
  /// function tables for the various bitblasting strategies indexed by node kind
  TermBBStrategy d_termBBStrategies[kind::LAST_KIND];
  AtomBBStrategy d_atomBBStrategies[kind::LAST_KIND]; 
public:
  TBitblaster(); 
  virtual ~TBitblaster() {}
  virtual void bbAtom(TNode node) = 0; 
  virtual void bbTerm(TNode node, Bits&  bits) = 0;
  virtual void makeVariable(TNode node, Bits& bits) = 0;
  virtual T getBBAtom(TNode atom) const = 0;
  virtual bool hasBBAtom(TNode atom) const = 0;
  virtual void storeBBAtom(TNode atom, T atom_bb) = 0;
  
  bool hasBBTerm(TNode node) const;
  void getBBTerm(TNode node, Bits& bits) const;
  void storeBBTerm(TNode term, const Bits& bits); 
}; 


class TheoryBV; 

class TLazyBitblaster :  public TBitblaster<Node> {
  typedef std::vector<Node> Bits;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> VarSet;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> AtomSet;
  
  /** This class gets callbacks from minisat on propagations */
  class MinisatNotify : public prop::BVSatSolverInterface::Notify {
    prop::CnfStream* d_cnf;
    TheoryBV *d_bv;
  public:
    MinisatNotify(prop::CnfStream* cnf, TheoryBV *bv)
    : d_cnf(cnf)
    , d_bv(bv)
    {}
    bool notify(prop::SatLiteral lit);
    void notify(prop::SatClause& clause);
    void safePoint();
  };


  TheoryBV *d_bv;

  // sat solver used for bitblasting and associated CnfStream
  theory::OutputChannel*             d_bvOutput;
  prop::BVSatSolverInterface*        d_satSolver;
  prop::CnfStream*                   d_cnfStream;

  context::CDList<prop::SatLiteral>  d_assertedAtoms; /**< context dependent list storing the atoms
                                                       currently asserted by the DPLL SAT solver. */
  VarSet d_variables;
  AtomSet d_bbAtoms; 
  AbstractionModule* d_abstraction;
  
  void addAtom(TNode atom);
  bool hasValue(TNode a);
public:
  void bbTerm(TNode node, Bits&  bits);
  void bbAtom(TNode node);
  Node getBBAtom(TNode atom) const;
  void storeBBAtom(TNode atom, Node atom_bb);
  bool hasBBAtom(TNode atom) const; 
  TLazyBitblaster(context::Context* c, bv::TheoryBV* bv);
  ~TLazyBitblaster();
  bool assertToSat(TNode node, bool propagate = true);
  bool propagate();
  bool solve(bool quick_solve = false);
  void getConflict(std::vector<TNode>& conflict);
  void explain(TNode atom, std::vector<TNode>& explanation);
  void setAbstraction(AbstractionModule* abs);
  
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);
  /**
   * Return a constant Node representing the value of a variable
   * in the current model.
   * @param a
   *
   * @return
   */
  Node getVarValue(TNode a, bool fullModel=true);
  /**
   * Adds a constant value for each bit-blasted variable in the model.
   *
   * @param m the model
   * @param fullModel whether to create a "full model," i.e., add
   * constants to equivalence classes that don't already have them
   */
  void collectModelInfo(TheoryModel* m, bool fullModel);
  /**
   * Creates the bits corresponding to the variable (or non-bv term). 
   *
   * @param var
   */
  void makeVariable(TNode var, Bits& bits);

  bool isSharedTerm(TNode node);
  uint64_t computeAtomWeight(TNode node);

private:

  class Statistics {
  public:
    IntStat d_numTermClauses, d_numAtomClauses;
    IntStat d_numTerms, d_numAtoms;
    TimerStat d_bitblastTimer;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

class MinisatEmptyNotify : public prop::BVSatSolverInterface::Notify {
public:
  MinisatEmptyNotify() {}
  bool notify(prop::SatLiteral lit) { return true; }
  void notify(prop::SatClause& clause) { }
  void safePoint() {}
};


class EagerBitblaster : public TBitblaster<Node> {
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;
  // sat solver used for bitblasting and associated CnfStream
  prop::BVSatSolverInterface*        d_satSolver;
  prop::CnfStream*                   d_cnfStream;
  TNodeSet d_bbAtoms; 
public:
  void addAtom(TNode atom);
  void makeVariable(TNode node, Bits& bits);
  void bbTerm(TNode node, Bits&  bits);
  void bbAtom(TNode node);
  Node getBBAtom(TNode node) const;
  bool hasBBAtom(TNode atom) const; 
  void bbFormula(TNode formula);
  void storeBBAtom(TNode atom, Node atom_bb);
  EagerBitblaster(); 
  ~EagerBitblaster();
  bool assertToSat(TNode node, bool propagate = true);
  bool solve(); 
};

class AigBitblaster : public TBitblaster<Abc_Obj_t*> {
  typedef std::hash_map<TNode, Abc_Obj_t*, TNodeHashFunction > TNodeAigMap;
  typedef std::hash_map<Node, Abc_Obj_t*, NodeHashFunction > NodeAigMap;
  
  static Abc_Ntk_t* abcAigNetwork;
  prop::BVSatSolverInterface* d_satSolver;
  TNodeAigMap d_aigCache;
  NodeAigMap d_bbAtoms;
  
  NodeAigMap d_nodeToAigInput;
  // the thing we are checking for sat
  Abc_Obj_t* d_aigOutputNode;

  void addAtom(TNode atom);
  void simplifyAig();
  void storeBBAtom(TNode atom, Abc_Obj_t* atom_bb);
  Abc_Obj_t* getBBAtom(TNode atom) const;
  bool hasBBAtom(TNode atom) const;
  void cacheAig(TNode node, Abc_Obj_t* aig);
  bool hasAig(TNode node);
  Abc_Obj_t* getAig(TNode node);
  Abc_Obj_t* mkInput(TNode input);
  bool hasInput(TNode input);
  void convertToCnfAndAssert();
  void assertToSatSolver(Cnf_Dat_t* pCnf);

public:
  AigBitblaster();
  ~AigBitblaster();

  void makeVariable(TNode node, Bits& bits);
  void bbTerm(TNode node, Bits&  bits);
  void bbAtom(TNode node);
  Abc_Obj_t* bbFormula(TNode formula);
  bool solve(TNode query); 
  static Abc_Aig_t* currentAigM();
  static Abc_Ntk_t* currentAigNtk();
  
private:
  class Statistics {
  public:
    IntStat     d_numClauses;
    IntStat     d_numVariables; 
    TimerStat   d_simplificationTime;
    TimerStat   d_cnfConversionTime;
    TimerStat   d_solveTime; 
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};


// Bitblaster implementation

template <class T> void TBitblaster<T>::initAtomBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_atomBBStrategies[i] = UndefinedAtomBBStrategy<T>;
  }
  /// setting default bb strategies for atoms
  d_atomBBStrategies [ kind::EQUAL ]           = DefaultEqBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_ULT ]   = DefaultUltBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_ULE ]   = DefaultUleBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_UGT ]   = DefaultUgtBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_UGE ]   = DefaultUgeBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_SLT ]   = DefaultSltBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_SLE ]   = DefaultSleBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_SGT ]   = DefaultSgtBB<T>;
  d_atomBBStrategies [ kind::BITVECTOR_SGE ]   = DefaultSgeBB<T>;
}

template <class T> void TBitblaster<T>::initTermBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_termBBStrategies[i] = DefaultVarBB<T>;
  }
  /// setting default bb strategies for terms:
  d_termBBStrategies [ kind::CONST_BITVECTOR ]        = DefaultConstBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_NOT ]          = DefaultNotBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_CONCAT ]       = DefaultConcatBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_AND ]          = DefaultAndBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_OR ]           = DefaultOrBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_XOR ]          = DefaultXorBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_XNOR ]         = DefaultXnorBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_NAND ]         = DefaultNandBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_NOR ]          = DefaultNorBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_COMP ]         = DefaultCompBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_MULT ]         = DefaultMultBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_PLUS ]         = DefaultPlusBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_SUB ]          = DefaultSubBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_NEG ]          = DefaultNegBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_UDIV ]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies [ kind::BITVECTOR_UREM ]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies [ kind::BITVECTOR_UDIV_TOTAL ]   = DefaultUdivBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_UREM_TOTAL ]   = DefaultUremBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_SDIV ]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies [ kind::BITVECTOR_SREM ]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies [ kind::BITVECTOR_SMOD ]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies [ kind::BITVECTOR_SHL ]          = DefaultShlBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_LSHR ]         = DefaultLshrBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_ASHR ]         = DefaultAshrBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_EXTRACT ]      = DefaultExtractBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_REPEAT ]       = DefaultRepeatBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_ZERO_EXTEND ]  = DefaultZeroExtendBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_SIGN_EXTEND ]  = DefaultSignExtendBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_RIGHT ] = DefaultRotateRightBB<T>;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_LEFT ]  = DefaultRotateLeftBB<T>;
}

template <class T>
TBitblaster<T>::TBitblaster()
  : d_termCache()
{
  initAtomBBStrategies();
  initTermBBStrategies(); 
}

template <class T>
bool TBitblaster<T>::hasBBTerm(TNode node) const {
  return d_termCache.find(node) != d_termCache.end();
}
template <class T>
void TBitblaster<T>::getBBTerm(TNode node, Bits& bits) const {
  Assert (hasBBTerm(node));
  bits = d_termCache.find(node)->second;
}

template <class T>
void TBitblaster<T>::storeBBTerm(TNode node, const Bits& bits) {
  d_termCache.insert(std::make_pair(node, bits)); 
}


} /* bv namespace */

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BITBLASTER_H */
