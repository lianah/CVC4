/*********************                                                        */
/*! \file aig.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none.
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/bitblaster.h"
#include "theory/bv/aig.h"
#include "theory/rewriter.h"
#include "prop/bvminisat/bvminisat.h"

extern "C" {
#include "sat/cnf/cnf.h"
}

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 
using namespace std;

/** 
 * Abc CNF conversion utilities
 * 
  */

// FIXME: sketchy copy paste because the function is defined as static in ABC
static inline int Cnf_Lit2Var( int Lit ) { return (Lit & 1)? -(Lit >> 1)-1 : (Lit >> 1)+1;  }

extern "C" {
extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

void AbcAssertToSatSolver(Cnf_Dat_t* pCnf, prop::BVSatSolverInterface* satSolver) {
  unsigned numVariables = pCnf->nVars;
  unsigned numClauses = pCnf->nClauses;
  
  // create variables in the sat solver
  std::vector<prop::SatVariable> sat_variables;
  for (unsigned i = 0; i < numVariables; ++i) {
    sat_variables.push_back(satSolver->newVar(false, false, false)); 
  }

  // construct clauses and add to sat solver
  int * pLit, * pStop;
  for (unsigned i = 0; i < numClauses; i++ ) {
    prop::SatClause clause; 
    for (pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ ) {
      int int_lit = Cnf_Lit2Var(*pLit);
      Assert (int_lit != 0); 
      unsigned index = int_lit < 0? -int_lit : int_lit;
      Assert (index - 1 < sat_variables.size()); 
      prop::SatLiteral lit(sat_variables[index-1], int_lit < 0); 
      clause.push_back(lit); 
    }
    satSolver->addClause(clause, false); 
  }
}

void AbcConvertToCnf(Abc_Ntk_t * pNtk, prop::BVSatSolverInterface* satSolver) {
    Aig_Man_t * pMan;
    Cnf_Dat_t * pCnf = NULL;
    assert( Abc_NtkIsStrash(pNtk) );

    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    Assert (pMan != NULL);
    Assert (Aig_ManCheck(pMan));
    // TODO: figure out meaning of this
    bool fFastAlgo = true; 
    // derive CNF
    if ( fFastAlgo )
        pCnf = Cnf_DeriveFast( pMan, 0 );
    else
        pCnf = Cnf_Derive( pMan, 0 );
    
    // Cnf_DataTranformPolarity( pCnf, 0 );
    // TODO collect stats
    // pCnf->nVars, pCnf->nClauses, pCnf->nLiterals 

    AbcAssertToSatSolver( pCnf, satSolver);
    
    Cnf_DataFree( pCnf );
    Cnf_ManFree();
    Aig_ManStop( pMan );
}


AigBitblaster::AigBitblaster(AigSimplifier* aigSimplifier)
  : d_aigSimplifer(aigSimplifier)
{}

AigBitblaster::~AigBitblaster() {}

void AigBitblaster::storeVariable(TNode var) {
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    Node bit_i = utils::mkBitOf(var, i);
    d_aigSimplifer->mkInput(bit_i); 
  }
}

void AigBitblaster::bbFormula(TNode node) {
  Assert (node.getType().isBoolean());
  Debug("bitvector-bitblast") << "AigBitblaster::bbFormula "<< node << "\n"; 
  switch (node.getKind()) {
  case kind::AND:
  case kind::OR:
  case kind::IFF:
  case kind::XOR:
  case kind::IMPLIES:
  case kind::ITE:
  case kind::NOT:
    for (unsigned i = 0; i < node.getNumChildren(); ++i) {
      bbFormula(node[i]); 
    }
    break;
  case kind::CONST_BOOLEAN:
    break;
  case kind::VARIABLE:
    // must be a boolean variable
    if (!d_aigSimplifer->hasAig(node)) {
      d_aigSimplifer->mkInput(node);
    }
    break; 
  default:
    bbAtom(node); 
  }
}

void AigBitblaster::bbAtom(TNode node) {
  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting atom " << node <<"\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
      Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
      normalized;

  // converting the atom to Aig
  Abc_Obj_t* result = d_aigSimplifer->convertToAig(atom_bb);
  // cache the atom as well
  d_aigSimplifer->cacheAig(node, result); 
  storeBBAtom(node);
  Debug("bitvector-bitblast") << "Done bitblasting atom " << node <<"\n";
}

void AigBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting term " << node <<"\n";
  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert (bits.size() == utils::getSize(node));
  storeBBTerm(node, bits);
}



AigSimplifier::AigSimplifier(prop::BVSatSolverInterface* solver)
  : d_satSolver(solver)
  , d_asserted(false)
  , d_aigCache()
  , d_nodeToAigInput()
    //  , d_aigInputToNode()
  , d_aigOutput(NULL)
{

  Abc_Start();
  d_abcAigNetwork = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1); 
  char pName[] = "CVC4::theory::bv::AigNetwork";
  d_abcAigNetwork->pName = Extra_UtilStrsav(pName);
  d_trueAigNode = Abc_AigConst1(d_abcAigNetwork);
  d_falseAigNode = Abc_ObjNot(d_trueAigNode); 
}

AigSimplifier::~AigSimplifier() {
  Abc_Stop();
  delete d_abcAigNetwork;
}

Abc_Obj_t* AigSimplifier::convertToAig(TNode node) {
  if (hasAig(node))
    return getAig(node);

  Abc_Aig_t* man = (Abc_Aig_t*)d_abcAigNetwork->pManFunc;
  Abc_Obj_t* result = NULL;
  
  Debug("bitvector-aig") << "AigSimplifier::convertToAig " << node <<"\n"; 
  switch (node.getKind()) {
  case kind::AND:
    {
      result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigAnd(man, result, child);
      }
      break;
    }
  case kind::OR:
    {
      result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigOr(man, result, child);
      }
      break;
    }
  case kind::IFF:
    {
      Assert (node.getNumChildren() == 2); 
      Abc_Obj_t* child1 = convertToAig(node[0]);
      Abc_Obj_t* child2 = convertToAig(node[1]);

      // bit-blasting as ~(child1 xor child2)
      Abc_Obj_t* different = Abc_AigXor(man, child1, child2);
      result = Abc_ObjNot(different);
      break;
    }
  case kind::XOR:
    {
      result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigXor(man, result, child);
      }
      break;
    }
  case kind::IMPLIES:
    {
      Assert (node.getNumChildren() == 2); 
      Abc_Obj_t* child1 = convertToAig(node[0]);
      Abc_Obj_t* child2 = convertToAig(node[1]);
      Abc_Obj_t* not_child1 = Abc_ObjNot(child1);
      result = Abc_AigOr(man, not_child1, child2);
      break;
    }
  case kind::ITE:
    {
      Assert (node.getNumChildren() == 3); 
      Abc_Obj_t* a = convertToAig(node[0]);
      Abc_Obj_t* b = convertToAig(node[1]);
      Abc_Obj_t* c = convertToAig(node[2]);
      result = Abc_AigMux(man, a, b, c); 
      break;
    }
  case kind::NOT:
    {
      Abc_Obj_t* child1 = convertToAig(node[0]);
      result = Abc_ObjNot(child1);
      break;
    }
  case kind::CONST_BOOLEAN:
    {
      result = node.getConst<bool>() ? d_trueAigNode : d_falseAigNode; 
      break;
    }
  default:
    Unreachable("Can't convert to AIG."); 
  }

  cacheAig(node, result);
  Debug("bitvector-aig") << "AigSimplifier::convertToAig done " << node << " => " << result <<"\n"; 
  return result; 
}

void AigSimplifier::cacheAig(TNode node, Abc_Obj_t* aig) {
  Assert (!hasAig(node));
  d_aigCache.insert(make_pair(node, aig));
}
bool AigSimplifier::hasAig(TNode node) {
  return d_aigCache.find(node) != d_aigCache.end(); 
}
Abc_Obj_t* AigSimplifier::getAig(TNode node) {
  Assert(hasAig(node));
  Debug("bitvector-aig") << "AigSimplifer::getAig " << node << " => " << d_aigCache.find(node)->second <<"\n"; 
  return d_aigCache.find(node)->second; 
}

void AigSimplifier::mkInput(TNode input) {
  Assert (!hasInput(input));
  Assert(input.getKind() == kind::BITVECTOR_BITOF ||
         (input.getType().isBoolean() &&
          input.getKind() == kind::VARIABLE));
  Abc_Obj_t* aig_input = Abc_NtkCreatePi(d_abcAigNetwork);
  d_aigCache.insert(make_pair(input, aig_input));
  d_nodeToAigInput.insert(make_pair(input, aig_input));
  Debug("bitvector-aig") << "AigSimplifer::mkInput " << input << " " << aig_input <<"\n"; 
  // d_aigInputToNode.insert(make_pair(aig_input, input)); 
}

bool AigSimplifier::hasInput(TNode input) {
  return d_nodeToAigInput.find(input) != d_nodeToAigInput.end(); 
}

void AigSimplifier::simplifyAig() {
  Assert (!d_asserted);
  Abc_AigCleanup((Abc_Aig_t*)d_abcAigNetwork->pManFunc);
  Assert (Abc_NtkCheck(d_abcAigNetwork));

 
  // run simplifications
  
  d_asserted = true; 
}

void AigSimplifier::convertToCnfAndAssert() {
  // char fileName[] = "temp.dimacs";
  // char command[100];
  // Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
  // Abc_FrameSetCurrentNetwork(pAbc, d_abcAigNetwork);
  // sprintf( command, "write_cnf %s", fileName );
  // if ( Cmd_CommandExecute( pAbc, command ) ) {
  //   fprintf( stdout, "Cannot execute command \"%s\".\n", command );
  //   exit(-1); 
  // }
  AbcConvertToCnf(d_abcAigNetwork, d_satSolver);
}

bool AigSimplifier::solve() {
  prop::SatValue result = d_satSolver->solve();
  Assert (result != prop::SAT_VALUE_UNKNOWN); 
  return result == prop::SAT_VALUE_TRUE; 
}

void AigSimplifier::setOutput(TNode query) {
  Assert(d_aigOutput == NULL); 
  Abc_Obj_t* aig_query = convertToAig(query);
  d_aigOutput = Abc_NtkCreatePo(d_abcAigNetwork); 
  Abc_ObjAddFanin(d_aigOutput, aig_query); 
}

