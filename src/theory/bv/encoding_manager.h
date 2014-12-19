/*********************                                                        */
/*! \file encoding_manager.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 **/

#include "cvc4_public.h"

#ifndef __CVC4__ENCODING_MANAGER_H
#define __CVC4__ENCODING_MANAGER_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace bv {
template <class T> class TBitblaster;
}
}

namespace prop {
class CnfStream;
class BVSatSolverInterface;
}

class EncodingManager {
  typedef __gnu_cxx::hash_map<TNode, unsigned, TNodeHashFunction> MultToId;
  typedef __gnu_cxx::hash_map<TNode, TNode, TNodeHashFunction> TNodeMap;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;
  
  CVC4::theory::bv::TBitblaster<Node>* d_bb;
  prop::CnfStream* d_cnf;
  prop::BVSatSolverInterface* d_solver;
  static EncodingManager* d_currentEM;
  MultToId d_multToId;
  TNodeMap d_atoms;
  unsigned d_multCount;
  bool d_finalized; 
  void markSatVariables(TNode bit, unsigned id, TNodeSet& cache, TNodeSet& fringe);
  void markAtoms(TNode mult, unsigned id);
public:
  unsigned d_sameCircuitLearned;
  unsigned d_totalLearned;

  EncodingManager();
  ~EncodingManager();

  static EncodingManager* currentEM();
  
  void setBitblaster(theory::bv::TBitblaster<Node>* bb);
  void setCnfStream(prop::CnfStream* cnf);
  void setSatSolver(prop::BVSatSolverInterface* solver); 
  void registerAtom(TNode atom, TNode atom_def); 
  void registerMultiplier(TNode mult);
  void finalizeEncoding();
  void printResult();
  

};/* class EncodingManager */


}/* CVC4 namespace */

#endif /* __CVC4__PROOF_MANAGER_H */
