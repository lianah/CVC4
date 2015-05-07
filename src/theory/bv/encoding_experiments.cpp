/*********************                                                        */
/*! \file encoding_experiments.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "theory/bv/encoding_experiments.h"
#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/multiplier_zoo.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "main/options.h"

#include <stdlib.h>
#include <fstream>

using namespace std;
using namespace CVC4;
using namespace CVC4::prop;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

CVC4::theory::bv::MultiplyEncoding CVC4::theory::bv::MultiplyEncoding::s_current; 

// fixed are literals that represent the fixed values of the bits
// according to some heuristic
void selectBits(Options& opts, std::vector<int>& fixed) {
  unsigned  num_bits = opts[options::encodingNumFixed];
  unsigned width = opts[options::encodingBitwidth];
  std::vector<bool> picked(width, false);

  for (unsigned i = 0; i < num_bits; ++i) {
    unsigned nbit;
    do {
      nbit = rand() % width;
    } while (picked[nbit]);
    picked[nbit] = true;
    nbit = rand() % 2 ? -nbit : nbit;
    fixed.push_back(nbit);
  }
  Assert (fixed.size() == num_bits);
}

void fixBits(EncodingBitblaster::Bits& bits, std::vector<int>& fixed, std::vector<Node>& assumps) {
  for (unsigned i = 0; i < fixed.size(); ++i) {
    int n = fixed[i] < 0 ? - fixed[i] : fixed[i];
    Node bit =fixed[i] < 0 ? utils::mkNot(bits[n]) : bits[n];
    assumps.push_back(bit);
  }
}


void printSatVars(EncodingBitblaster& bb, EncodingBitblaster::Bits& bits) {
  for (unsigned i = 0; i < bits.size(); ++i) {
    std::cout << bb.getCnfStream()->getLiteral(bits[i]).toString() << " ";
  }
  std::cout << std::endl;
}

enum EncodingOrder{
  EQUAL =1,
  LESS =2,
  GREATER =3,
  INCOMPARABLE =4
};

EncodingOrder comparePropagations(EncodingBitblaster::EncodingNotify& en1,
				  EncodingBitblaster::EncodingNotify& en2,
				  EncodingBitblaster& bb1, EncodingBitblaster& bb2) {
    unsigned en1_unique = 0;
    unsigned both = 0;
    for (TNodeSet::const_iterator it = en1.begin(); it != en1.end(); ++it) {
      if (en2.isPropagated(*it)) {
	++both; 
      } else {
	++en1_unique;
      }
    }

    unsigned en2_unique = 0;
    for (TNodeSet::const_iterator it = en2.begin(); it != en2.end(); ++it) {
      if (! en1.isPropagated(*it)) {
	++en2_unique;
      }
    }

    Debug("encoding-experiment") << "  Both propagate " << both << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " unique propagate # " << en1_unique << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " total propagations # " << en1.d_numTotalPropagations << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " shared propagations # " << en1.d_numSharedPropagations << std::endl;
										  
    Debug("encoding-experiment") << "  " << bb2.getName() << " unique propagate # " << en2_unique << std::endl;
    Debug("encoding-experiment") << "  " << bb2.getName() << " total propagations # " << en2.d_numTotalPropagations << std::endl;
    Debug("encoding-experiment") << "  " << bb2.getName() << " shared propagations # " << en2.d_numSharedPropagations << std::endl;
    
    
    if (en1_unique == 0 && en2_unique == 0)
      return EQUAL;

    if (en1_unique == 0 && en2_unique != 0)
      return LESS;

    if (en2_unique == 0 && en1_unique != 0)
      return GREATER;

    return INCOMPARABLE;
}


class Runner {
  std::string d_name;
public:
  Runner(std::string name)
    : d_name(name) {}
  virtual void run(const std::vector<int>& assumps) = 0;
  virtual ~Runner() {}
  const std::string& getName() { return d_name; }
};


void sampleAssignments(unsigned num_fixed, unsigned num, Runner* runner, bool random_walk) {
  std::vector<unsigned> permutation;
  for (unsigned i = 0; i < num; ++i)
    permutation.push_back(i); 
  std::random_shuffle (permutation.begin(), permutation.end());

  unsigned num_iter = std::pow(2, num_fixed);
  std::cout << "Running "<< runner->getName() << std::endl;
  for (unsigned iter = 0; iter < num_iter; ++iter) {
    if (iter % 10000 == 0) {
      std::cout << "sampleAssignments iteration="<< iter <<"/"<< num_iter << "\r";
      std::cout.flush();
    }
    Trace("encoding") << "RUNNING iteration " << iter << std::endl;
    std::vector<int> assumps;
    
    for (unsigned j = 0; j < num_fixed; ++j) {
      // if the jth bit of i is 1 negate the assumption
      if ((iter & (1 << j)) != 0) {
	//std::cout << "-" << permutation[j]<<" ";
	assumps.push_back(-permutation[j]);
      } else {
	//std::cout << permutation[j]<<" ";
	assumps.push_back(permutation[j]);
      }
    }

    if (random_walk) {
      // finish via random walk
      for (unsigned j = assumps.size(); j < permutation.size(); ++j) {
	bool negate = rand()%2;
	if (negate) {
	  assumps.push_back(-permutation[j]);
	} else {
	  assumps.push_back(permutation[j]);
	}
      }
    }

    runner->run(assumps); 
  }
}


struct ComparisonResult {
  std::string d_name1, d_name2;
  unsigned first_better;
  unsigned second_better;
  unsigned incomparable;
  unsigned equal;
  unsigned total;
  ComparisonResult(std::string name1, std::string name2)
    : d_name1(name1)
    , d_name2(name2)
    , first_better(0)
    , second_better(0)
    , incomparable(0)
    , equal(0)
    , total(0) {}

  void add(EncodingOrder order) {
    ++total;
    switch(order) {
    case EQUAL: ++equal; break;
    case LESS: ++second_better; break;
    case GREATER: ++first_better; break;
    case INCOMPARABLE: ++incomparable; break;
    default:
      Unreachable();
    }
  }
  friend  std::ostream& operator<<(std::ostream& os, const ComparisonResult& obj);
};

std::ostream& operator<<(std::ostream& os, const ComparisonResult& obj)
{
  os << obj.d_name1 << " better: " << obj.first_better << "("<<float(obj.first_better*100)/ obj.total <<"%)" <<std::endl;
  os << obj.d_name2 << " better: " << obj.second_better << "("<<float(obj.second_better*100)/ obj.total <<"%)" <<std::endl;
  os << "incomparable: " << obj.incomparable << "("<<float(obj.incomparable*100)/ obj.total <<"%)" <<std::endl;
  os << "equal: " << obj.equal << "("<<float(obj.equal*100)/ obj.total <<"%)" <<std::endl;
  os << "total: "<< obj.total << std::endl;
  return os;
}

class EncodingComparator : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name1;
  std::string d_name2;
  EncodingBitblaster d_encodingBB1;
  EncodingBitblaster d_encodingBB2;
  EncodingBitblaster::EncodingNotify* d_encodingNotify1;
  EncodingBitblaster::EncodingNotify* d_encodingNotify2;
 
  ComparisonResult d_cresult;
  Node d_assertion;
  vector<Node> d_all_bits1;
  vector<Node> d_all_bits2;
  bool d_keepLearned;
public:
  EncodingComparator(unsigned bitwidth, Kind k, bool keep_learned, 
		     TBitblaster<Node>::TermBBStrategy e1, std::string name1,
		     TBitblaster<Node>::TermBBStrategy e2, std::string name2)
    : Runner(name1+" vs "+name2+" comparator")
    , d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name1(name1)
    , d_name2(name2)
    , d_encodingBB1(d_ctx, d_name1)
    , d_encodingBB2(d_ctx, d_name2)
    , d_encodingNotify1(NULL)
    , d_encodingNotify2(NULL)
    , d_cresult(name1, name2)
    , d_assertion()
    , d_all_bits1()
    , d_all_bits2()
    , d_keepLearned(keep_learned)
  {
    CnfStream* cnf1 = d_encodingBB1.getCnfStream();
    d_encodingBB1.setTermBBStrategy(k, e1);
    
    CnfStream* cnf2 = d_encodingBB2.getCnfStream();
    d_encodingBB2.setTermBBStrategy(k, e2);

    d_encodingNotify1 = new EncodingBitblaster::EncodingNotify(cnf2, &d_encodingBB1);
    d_encodingNotify2 = new EncodingBitblaster::EncodingNotify(cnf1, &d_encodingBB2);
    d_encodingBB1.setNotify(d_encodingNotify1);
    d_encodingBB2.setNotify(d_encodingNotify2);

    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = utils::mkVar(d_bitwidth);

    Node a_op_b = utils::mkNode(d_kind, a, b);
    d_assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

    d_encodingBB1.assertFact(d_assertion);
    d_encodingBB2.assertFact(d_assertion);

    EncodingBitblaster::Bits a1_bits, b1_bits, c1_bits;
    d_encodingBB1.getBBTerm(a, a1_bits);
    d_encodingBB1.getBBTerm(b, b1_bits);
    d_encodingBB1.getBBTerm(c, c1_bits);

    EncodingBitblaster::Bits a2_bits, b2_bits, c2_bits;
    d_encodingBB2.getBBTerm(a, a2_bits);
    d_encodingBB2.getBBTerm(b, b2_bits);
    d_encodingBB2.getBBTerm(c, c2_bits);

    d_all_bits1.insert(d_all_bits1.begin(), a1_bits.begin(), a1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), b1_bits.begin(), b1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), c1_bits.begin(), c1_bits.end());

    d_all_bits2.insert(d_all_bits2.begin(), a2_bits.begin(), a2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), b2_bits.begin(), b2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), c2_bits.begin(), c2_bits.end());
  }

  virtual ~EncodingComparator() {
    delete d_encodingNotify1;
    delete d_encodingNotify2;
    delete d_ctx;
  }
  
  void run(const vector<int>& assump_index) {
    d_ctx->push();
    
    bool res1 = true;
    bool res2 = true;

    Debug("encoding") << "Fixed bits "<< std::endl;
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      if (!d_keepLearned) {
	d_encodingBB1.clearLearnedClauses();
	d_encodingBB2.clearLearnedClauses();
      }

      TNode bit1, bit2;
      if(assump_index[i] < 0) {
	bit1 = utils::mkNot(d_all_bits1[-assump_index[i]]);
	bit2 = utils::mkNot(d_all_bits2[-assump_index[i]]);
      } else {
	bit1 = d_all_bits1[assump_index[i]];
	bit2 = d_all_bits2[assump_index[i]];
      }

      Debug("encoding") << bit1 << " ";
      d_encodingBB1.assumeLiteral(bit1);
      res1 = d_encodingBB1.propagate();
      d_encodingBB2.assumeLiteral(bit2);
      res2 = d_encodingBB2.propagate();
      
      if (!res1 && res2)
	++d_cresult.first_better;
      if (!res2 && res1)
	++d_cresult.second_better;
      
      if (!res1 || ! res2)
	break;

      // check which one wins
      EncodingOrder order = comparePropagations(*d_encodingNotify1, *d_encodingNotify2,
						d_encodingBB1, d_encodingBB2);
      d_cresult.add(order);
    }
    Debug("encoding") << std::endl;


    // call solve to ensure that the encodings are correct
    res1 = res1 ? d_encodingBB1.solve() : res1;
    Debug("encoding") << "  " << d_encodingBB1.getName() <<" full solve result " << res1 << std::endl;
    Debug("encoding") << "   number of learned clauses " << d_encodingBB1.getNumLearnedClauses() << std::endl;
    res2 = res2 ? d_encodingBB2.solve() : res2;
    Debug("encoding") << "  " << d_encodingBB2.getName() <<" full solve result " << res2 << std::endl;
    Debug("encoding") << "   number of learned clauses " << d_encodingBB2.getNumLearnedClauses() << std::endl;
    
    Assert( res1 == res2);
    d_encodingNotify1->clear();
    d_encodingNotify2->clear();

    d_ctx->pop();
  }

  void printResults(std::ostream& os) {
    os << d_cresult;
  }
};

class BruteForceTermOptChecker : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name1;
  std::string d_name2;
  EncodingBitblaster d_encodingBB1;
  EncodingBitblaster d_encodingBB2;
  EncodingBitblaster::EncodingNotify* d_encodingNotify1;
  EncodingBitblaster::EncodingNotify* d_encodingNotify2;
 
  Node d_assertion;
  vector<Node> d_all_bits1;
  vector<Node> d_all_bits2;
public:
  BruteForceTermOptChecker(unsigned bitwidth, Kind k,  
		     TBitblaster<Node>::TermBBStrategy e1, std::string name1,
		     TBitblaster<Node>::TermBBStrategy e2, std::string name2)
    : Runner(name1+" vs "+name2+" opt checker")
    , d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name1(name1)
    , d_name2(name2)
    , d_encodingBB1(d_ctx, d_name1)
    , d_encodingBB2(d_ctx, d_name2)
    , d_assertion()
  {
    d_encodingBB1.setTermBBStrategy(k, e1);
    
    d_encodingBB2.setTermBBStrategy(k, e2);

    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = utils::mkVar(d_bitwidth);

    Node a_op_b = utils::mkNode(d_kind, a, b);
    d_assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

    d_encodingBB1.assertFact(d_assertion);
    d_encodingBB2.assertFact(d_assertion);

    EncodingBitblaster::Bits a1_bits, b1_bits, c1_bits;
    d_encodingBB1.getBBTerm(a, a1_bits);
    d_encodingBB1.getBBTerm(b, b1_bits);
    d_encodingBB1.getBBTerm(c, c1_bits);

    EncodingBitblaster::Bits a2_bits, b2_bits, c2_bits;
    d_encodingBB2.getBBTerm(a, a2_bits);
    d_encodingBB2.getBBTerm(b, b2_bits);
    d_encodingBB2.getBBTerm(c, c2_bits);

    d_all_bits1.insert(d_all_bits1.begin(), a1_bits.begin(), a1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), b1_bits.begin(), b1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), c1_bits.begin(), c1_bits.end());

    d_all_bits2.insert(d_all_bits2.begin(), a2_bits.begin(), a2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), b2_bits.begin(), b2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), c2_bits.begin(), c2_bits.end());
  }

  virtual ~BruteForceTermOptChecker() {
    delete d_ctx;
  }
  
  void run(const vector<int>& assump_index) {
    d_ctx->push();
    
    bool res1 = true;
    bool res2 = true;

    Debug("encoding") << "Fixed bits "<< std::endl;
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      //d_encodingBB1.clearLearnedClauses();

      TNode bit1, bit2;
      if(assump_index[i] < 0) {
	bit1 = utils::mkNot(d_all_bits1[-assump_index[i]]);
	bit2 = utils::mkNot(d_all_bits2[-assump_index[i]]);
      } else {
	bit1 = d_all_bits1[assump_index[i]];
	bit2 = d_all_bits2[assump_index[i]];
      }

      Debug("encoding") << bit1 << "/ "<<  bit2 <<" " <<std::endl;
      d_encodingBB1.assumeLiteral(bit1);
      res1 = d_encodingBB1.solve();
      d_encodingBB2.assumeLiteral(bit2);
      res2 = d_encodingBB2.solve();
      
      Assert (res1 == res2);

      std::cout << "result "<< res1<< std::endl;
      std::cout << d_encodingBB1.getName() << " learned clauses "
		<< d_encodingBB1.getNumLearnedClauses() << std::endl;

      std::cout << d_encodingBB2.getName() << " learned clauses "
		<< d_encodingBB2.getNumLearnedClauses() << std::endl;
    }

    d_ctx->pop();
  }

  void printResults() {
    d_encodingBB1.printLearned(std::cout);
    d_encodingBB2.printLearned(std::cout);
  }
};

class BruteForceAtomOptChecker : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name1;
  std::string d_name2;
  EncodingBitblaster d_encodingBB1;
  EncodingBitblaster d_encodingBB2;
  EncodingBitblaster::EncodingNotify* d_encodingNotify1;
  EncodingBitblaster::EncodingNotify* d_encodingNotify2;
 
  Node d_assertion;
  vector<Node> d_all_bits1;
  vector<Node> d_all_bits2;
public:
  BruteForceAtomOptChecker(unsigned bitwidth, Kind k,  
		     TBitblaster<Node>::AtomBBStrategy e1, std::string name1,
		     TBitblaster<Node>::AtomBBStrategy e2, std::string name2)
    : Runner(name1+" vs "+name2+" opt checker")
    , d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name1(name1)
    , d_name2(name2)
    , d_encodingBB1(d_ctx, d_name1)
    , d_encodingBB2(d_ctx, d_name2)
    , d_assertion()
  {
    d_encodingBB1.setAtomBBStrategy(k, e1);
    d_encodingBB2.setAtomBBStrategy(k, e2);

    NodeManager* nm = NodeManager::currentNM();
    
    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = nm->mkSkolem("atom", nm->booleanType()); 

    Node a_op_b = utils::mkNode(d_kind, a, b);
    d_assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

    d_encodingBB1.assertFact(d_assertion);
    d_encodingBB2.assertFact(d_assertion);

    EncodingBitblaster::Bits a1_bits, b1_bits;
    d_encodingBB1.getBBTerm(a, a1_bits);
    d_encodingBB1.getBBTerm(b, b1_bits);

    EncodingBitblaster::Bits a2_bits, b2_bits;
    d_encodingBB2.getBBTerm(a, a2_bits);
    d_encodingBB2.getBBTerm(b, b2_bits);

    d_all_bits1.insert(d_all_bits1.begin(), a1_bits.begin(), a1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), b1_bits.begin(), b1_bits.end());
    d_all_bits1.push_back(c);
    
    d_all_bits2.insert(d_all_bits2.begin(), a2_bits.begin(), a2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), b2_bits.begin(), b2_bits.end());
    d_all_bits2.push_back(c);
  }

  virtual ~BruteForceAtomOptChecker() {
    delete d_ctx;
  }
  
  void run(const vector<int>& assump_index) {
    d_ctx->push();
    
    bool res1 = true;
    bool res2 = true;

    Debug("encoding") << "Fixed bits "<< std::endl;
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      //d_encodingBB1.clearLearnedClauses();

      TNode bit1, bit2;
      if(assump_index[i] < 0) {
	bit1 = utils::mkNot(d_all_bits1[-assump_index[i]]);
	bit2 = utils::mkNot(d_all_bits2[-assump_index[i]]);
      } else {
	bit1 = d_all_bits1[assump_index[i]];
	bit2 = d_all_bits2[assump_index[i]];
      }

      Debug("encoding") << bit1 << "/ "<<  bit2 <<" " <<std::endl;
      d_encodingBB1.assumeLiteral(bit1);
      res1 = d_encodingBB1.solve();
      d_encodingBB2.assumeLiteral(bit2);
      res2 = d_encodingBB2.solve();
      
      Assert (res1 == res2);

      std::cout << "result "<< res1<< std::endl;
      std::cout << d_encodingBB1.getName() << " learned clauses "
		<< d_encodingBB1.getNumLearnedClauses() << std::endl;

      std::cout << d_encodingBB2.getName() << " learned clauses "
		<< d_encodingBB2.getNumLearnedClauses() << std::endl;
    }

    d_ctx->pop();
  }

  void printResults() {
    d_encodingBB1.printLearned(std::cout);
    d_encodingBB2.printLearned(std::cout);
  }
};


class EncodingContradiction : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name;
  EncodingBitblaster d_encodingBB;
  EncodingBitblaster d_oracleBB;
  //  EncodingBitblaster::EncodingNotify d_notify;
  std::vector<Node> d_allBits;
  unsigned d_missedContradictions;
public:
  EncodingContradiction(unsigned bitwidth, Kind k, 
		        TBitblaster<Node>::TermBBStrategy e, std::string name)
    : Runner(name+" detect conflicts")
    , d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name(name)
    , d_encodingBB(d_ctx, d_name)
    , d_oracleBB(d_ctx, d_name+"oracle")
    // , d_notify(d_encodingBB.getCnfStream(), d_encodingBB1)
    // , d_notify_oracle(d_oracleBB.getCnfStream(), d_oracle)
    , d_allBits()
    , d_missedContradictions(0)
  {
    d_encodingBB.setTermBBStrategy(k, e);
    d_oracleBB.setTermBBStrategy(k, e);
    
    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = utils::mkVar(d_bitwidth);

    Node a_op_b = utils::mkNode(d_kind, a, b);
    Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);
    
    d_encodingBB.assertFact(assertion);
    d_oracleBB.assertFact(assertion);
    
    EncodingBitblaster::Bits a_bits, b_bits, c_bits;
    d_encodingBB.getBBTerm(a, a_bits);
    d_encodingBB.getBBTerm(b, b_bits);
    d_encodingBB.getBBTerm(c, c_bits);

    d_allBits.insert(d_allBits.begin(), a_bits.begin(), a_bits.end());
    d_allBits.insert(d_allBits.begin(), b_bits.begin(), b_bits.end());
    d_allBits.insert(d_allBits.begin(), c_bits.begin(), c_bits.end());
  }

  void run(const std::vector<int>& assump_index) {
    d_ctx->push();
    Debug("encoding") << "Push() " <<std::endl;
    
    bool res = true, res_oracle = true;
    
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      d_encodingBB.clearLearnedClauses();

      TNode bit;
      if(assump_index[i] < 0) {
	bit = utils::mkNot(d_allBits[-assump_index[i]]);
      } else {
	bit = d_allBits[assump_index[i]];
      }

      Debug("encoding") << "Assuming bit " << bit <<std::endl;
      d_encodingBB.assumeLiteral(bit);
      d_oracleBB.assumeLiteral(bit);
      
      res = d_encodingBB.propagate();
      res_oracle = d_oracleBB.solve();
      
      if (!res_oracle && res) {
	++d_missedContradictions;
      }
      Assert (res || !res_oracle);
    }
    Debug("encoding") << "Pop() " <<std::endl;

    d_ctx->pop();
  }

  void print(ostream& os) {
    os << d_name << " missed contradictions " << d_missedContradictions << endl;
  }
};

void printTermEncodingSharing(Kind k, std::vector<TBitblaster<Node>::TermBBStrategy>& es, std::string name,
                              unsigned n, bool auxiliaries = false, bool truncated = true) {

  std::ostringstream os;
  os << name << (truncated? "": "2n") << "_" << n<< (auxiliaries? "_aux" : "");
  name = os.str();

  std::cout << "Writing file " << name << ".cnf"<<std::endl;
  ofstream outfile;
  outfile.open ((name+".cnf").c_str());

  unsigned bitwidth = truncated ? n : 2*n;

  EncodingBitblaster eb(new context::Context(), name);
  for (unsigned i = 0; i < es.size(); ++i) {
    eb.setTermBBStrategy(k, es[i]);
  }
  Node a = utils::mkVar("a", bitwidth);
  Node b = utils::mkVar("b", bitwidth);
  Node c = utils::mkVar("c", bitwidth);

  Node a_op_b = utils::mkNode(k, a, b);
  Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

  eb.assertFact(assertion);

  EncodingBitblaster::Bits bits;
  NodeSet all_bits;
  eb.getBBTerm(a, bits);
  bits.resize(n); // for not truncated
  all_bits.insert(bits.begin(), bits.end());

  eb.getBBTerm(b, bits);
  bits.resize(n);
  all_bits.insert(bits.begin(), bits.end());

  eb.getBBTerm(c, bits);
  all_bits.insert(bits.begin(), bits.end());

  CVC4::prop::CnfStream* cnf = eb.getCnfStream();
  EncodingBitblaster::Bits a_bits, b_bits;
  eb.getBBTerm(a, a_bits);
  eb.getBBTerm(b, b_bits);

  // for multiplication optionally print auxiliaries
  if (k == kind::BITVECTOR_MULT && auxiliaries) {
    NodeManager* nm = NodeManager::currentNM();
    
    for (unsigned i = 0; i < n; ++i) {
      for (unsigned j = 0; j < n; ++j) {
	Node a_and_b = nm->mkNode(kind::AND, b_bits[i], a_bits[j]);
	if (!cnf->hasLiteral(a_and_b)) {
	  a_and_b = nm->mkNode(kind::AND, a_bits[j], b_bits[i]);
	  if (!cnf->hasLiteral(a_and_b)) {
	    continue;
	  }
	}
	all_bits.insert(a_and_b);
      }
    }
  }

  outfile << "c " << eb.getName() << std::endl;
  outfile << "c i ";
  // print variables that should be decided
  NodeSet::const_iterator it = all_bits.begin();
  for (; it != all_bits.end(); ++it) {
    CVC4::prop::SatLiteral var = cnf->getLiteral(*it);
    Assert (!var.isNegated());
    outfile << var <<" ";
  }
  outfile << "0" << std::endl;

  eb.printCnfMapping(outfile, all_bits);
  eb.printProblemClauses(outfile);

  // assert that the top n bits are zero as units
  if (!truncated) {
    for(unsigned i = n; i < 2*n; ++i) {
      CVC4::prop::SatLiteral lit_a = cnf->getLiteral(a_bits[i]);
      CVC4::prop::SatLiteral lit_b = cnf->getLiteral(b_bits[i]);
      outfile << (~lit_a) <<" 0"<< std::endl;
      outfile << (~lit_b) <<" 0"<< std::endl;
    }
  }

  outfile.close();
}


// TODO: refactor this to take expression it is bit-blasting to ensure the common alphabet matches exactly
void printTermEncoding(Kind k, TBitblaster<Node>::TermBBStrategy e, std::string name,
		       unsigned n, bool auxiliaries = false, bool truncated = true) {

  std::ostringstream os;
  os << name << (truncated? "": "2n") << "_" << n<< (auxiliaries? "_aux" : "");
  name = os.str();

  std::cout << "Writing file " << name << ".cnf"<<std::endl;
  ofstream outfile;
  outfile.open ((name+".cnf").c_str());

  unsigned bitwidth = truncated ? n : 2*n;

  EncodingBitblaster eb(new context::Context(), name);
  eb.setTermBBStrategy(k, e);
  Node a = utils::mkVar("a", bitwidth);
  Node b = utils::mkVar("b", bitwidth);
  Node c = utils::mkVar("c", bitwidth);

  Node a_op_b = utils::mkNode(k, a, b);
  Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

  eb.assertFact(assertion);

  EncodingBitblaster::Bits bits;
  NodeSet all_bits;
  eb.getBBTerm(a, bits);
  bits.resize(n); // for not truncated
  all_bits.insert(bits.begin(), bits.end());

  eb.getBBTerm(b, bits);
  bits.resize(n);
  all_bits.insert(bits.begin(), bits.end());

  eb.getBBTerm(c, bits);
  all_bits.insert(bits.begin(), bits.end());

  CVC4::prop::CnfStream* cnf = eb.getCnfStream();
  EncodingBitblaster::Bits a_bits, b_bits;
  eb.getBBTerm(a, a_bits);
  eb.getBBTerm(b, b_bits);

  // for multiplication optionally print auxiliaries
  if (k == kind::BITVECTOR_MULT && auxiliaries) {
    NodeManager* nm = NodeManager::currentNM();
    
    for (unsigned i = 0; i < n; ++i) {
      for (unsigned j = 0; j < n; ++j) {
	Node a_and_b = nm->mkNode(kind::AND, b_bits[i], a_bits[j]);
	if (!cnf->hasLiteral(a_and_b)) {
	  a_and_b = nm->mkNode(kind::AND, a_bits[j], b_bits[i]);
	  if (!cnf->hasLiteral(a_and_b)) {
	    continue;
	  }
	}
	all_bits.insert(a_and_b);
      }
    }
  }

  outfile << "c " << eb.getName() << std::endl;
  outfile << "c i ";
  // print variables that should be decided
  NodeSet::const_iterator it = all_bits.begin();
  for (; it != all_bits.end(); ++it) {
    CVC4::prop::SatLiteral var = cnf->getLiteral(*it);
    Assert (!var.isNegated());
    outfile << var <<" ";
  }
  outfile << "0" << std::endl;

  eb.printCnfMapping(outfile, all_bits, true);
  eb.printProblemClauses(outfile);

  // assert that the top n bits are zero as units
  if (!truncated) {
    for(unsigned i = n; i < 2*n; ++i) {
      CVC4::prop::SatLiteral lit_a = cnf->getLiteral(a_bits[i]);
      CVC4::prop::SatLiteral lit_b = cnf->getLiteral(b_bits[i]);
      outfile << (~lit_a) <<" 0"<< std::endl;
      outfile << (~lit_b) <<" 0"<< std::endl;
    }
  }

  outfile.close();
}


void printTermEncodingConst(Kind k, TBitblaster<Node>::TermBBStrategy e, std::string name,
                            unsigned n, unsigned K, bool truncated = true) {

  std::ostringstream os;
  os << name << "_const"<<K<<"_" << (truncated? "": "2n") << "_" << n;
  name = os.str();

  std::cout << "Writing file " << name << ".cnf"<<std::endl;
  ofstream outfile;
  outfile.open ((name+".cnf").c_str());

  unsigned bitwidth = truncated ? n : 2*n;

  EncodingBitblaster eb(new context::Context(), name);
  eb.setTermBBStrategy(k, e);
  Node a = utils::mkVar("a", bitwidth);
  Node b = utils::mkConst(bitwidth, K);
  Node c = utils::mkVar("c", bitwidth);

  Node a_op_b = utils::mkNode(k, a, b);
  Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

  eb.assertFact(assertion);

  EncodingBitblaster::Bits bits;
  NodeSet all_bits;
  eb.getBBTerm(a, bits);
  bits.resize(n); // for not truncated
  all_bits.insert(bits.begin(), bits.end());

  // eb.getBBTerm(b, bits);
  // bits.resize(n);
  // all_bits.insert(bits.begin(), bits.end());

  eb.getBBTerm(c, bits);
  all_bits.insert(bits.begin(), bits.end());

  CVC4::prop::CnfStream* cnf = eb.getCnfStream();
  EncodingBitblaster::Bits a_bits, b_bits;
  eb.getBBTerm(a, a_bits);
  eb.getBBTerm(b, b_bits);


  outfile << "c " << eb.getName() << std::endl;
  outfile << "c i ";
  // print variables that should be decided
  NodeSet::const_iterator it = all_bits.begin();
  for (; it != all_bits.end(); ++it) {
    
    CVC4::prop::SatLiteral var = cnf->getLiteral(*it);
    Assert (!var.isNegated());
    outfile << var <<" ";
  }
  outfile << "0" << std::endl;

  eb.printCnfMapping(outfile, all_bits);
  eb.printProblemClauses(outfile);

  // assert that the top n bits are zero as units
  if (!truncated) {
    for(unsigned i = n; i < 2*n; ++i) {
      if (cnf->hasLiteral(a_bits[i])) {
        CVC4::prop::SatLiteral lit_a = cnf->getLiteral(a_bits[i]);
        //CVC4::prop::SatLiteral lit_b = cnf->getLiteral(b_bits[i]);
      outfile << (~lit_a) <<" 0"<< std::endl;
      //outfile << (~lit_b) <<" 0"<< std::endl;
      }
    }
  }

  outfile.close();
}


void printAtomEncoding(Kind k, TBitblaster<Node>::AtomBBStrategy e, std::string name, unsigned bitwidth) {
  std::ostringstream os;
  os << name << "_" << bitwidth;
  name = os.str();
  ofstream outfile;
  outfile.open ((name+".cnf").c_str());

  EncodingBitblaster eb(new context::Context(), name);
  eb.setAtomBBStrategy(k, e);
  Node a = utils::mkVar("a", bitwidth);
  Node b = utils::mkVar("b", bitwidth);
  Node a_op_b = utils::mkNode(k, a, b);
  
  eb.bbAtom(a_op_b);

  EncodingBitblaster::Bits all_bits, bits;
  eb.getBBTerm(a, bits);
  all_bits.insert(all_bits.end(), bits.begin(), bits.end());
  eb.getBBTerm(b, bits);
  all_bits.insert(all_bits.end(), bits.begin(), bits.end());

  CVC4::prop::CnfStream* cnf = eb.getCnfStream();
  Assert (cnf->hasLiteral(a_op_b));
  all_bits.push_back(a_op_b);

  outfile << "c " << eb.getName() << std::endl;
  outfile << "c i ";
  for (unsigned i = 0; i < all_bits.size(); ++i) {
    CVC4::prop::SatLiteral var = cnf->getLiteral(all_bits[i]);
    Assert (!var.isNegated());
    outfile << var <<" ";
  }
  outfile << "0" << std::endl;    

  eb.printCnfMapping(outfile);
  eb.printProblemClauses(outfile);
  outfile.close();
}

void makeFullAdder(std::ostream& out) {
  EncodingBitblaster eb(new context::Context(), "FullAdder");
  NodeManager* nm = NodeManager::currentNM();
  Node a = nm->mkSkolem("a", nm->booleanType());
  Node b = nm->mkSkolem("b", nm->booleanType());
  Node carry = nm->mkSkolem("c", nm->booleanType());

  std::pair<Node, Node> fa_res;
  
  fa_res = theory::bv::fullAdder<Node>(a, b, carry);

  Node sum = fa_res.first;
  Node carry_out = fa_res.second;

  CVC4::prop::CnfStream* cnf  = eb.getCnfStream();
  cnf->ensureLiteral(sum);
  cnf->ensureLiteral(carry_out);

  CVC4::prop::SatLiteral sum_lit = cnf->getLiteral(sum);
  CVC4::prop::SatLiteral carry_out_lit = cnf->getLiteral(carry_out);
  out << "c " << eb.getName() << std::endl;
  out << "c " << sum_lit << " : sum" << std::endl;
  out << "c " << carry_out_lit << " : carry_out_lit" << std::endl;
  out << "c i "<< sum_lit <<" "
      << carry_out_lit << " "
      << cnf->getLiteral(a) <<" "
      << cnf->getLiteral(b) <<" "
      << cnf->getLiteral(carry) <<"0"
      << std::endl;
  eb.printCnfMapping(out, NodeSet(), true);
  eb.printProblemClauses(out);
}


void makeLTNewGadget(std::ostream& out) {
  EncodingBitblaster eb(new context::Context(), "LTGadget");
  out << "c " << eb.getName()  << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node a = nm->mkSkolem("a", nm->booleanType());
  Node b = nm->mkSkolem("b", nm->booleanType());
  Node rest = nm->mkSkolem("rest", nm->booleanType());

  // Node ans_found_out = utils::mkSkolem("ans_found_out", nm->booleanType());
  // Node answer_out = utils::mkSkolem("answer_out", nm->booleanType());
  
  Node answ = theory::bv::optimalUltGadgetSpec(a, b, rest, eb.getCnfStream());

  eb.getCnfStream()->ensureLiteral(answ);

  out << "c i " << eb.getCnfStream()->getLiteral(a) <<" "
      << eb.getCnfStream()->getLiteral(b) <<" "
      << eb.getCnfStream()->getLiteral(rest) <<" "
      << eb.getCnfStream()->getLiteral(answ);
  
  out << "0"<< std::endl;
  CVC4::prop::SatLiteral answ_lit = eb.getCnfStream()->getLiteral(answ);
  out << "c " << answ_lit << " : answ" << std::endl;
  NodeSet inputs;
  inputs.insert(a);
  inputs.insert(b);
  inputs.insert(rest);
  eb.printCnfMapping(out, inputs, true);
  eb.printProblemClauses(out);
}

void makeSignedGadget(std::ostream& out) {
  EncodingBitblaster eb(new context::Context(), "SignedGadget");
  out << "c " << eb.getName() << std::endl;
  
  NodeManager* nm = NodeManager::currentNM();
  Node a = nm->mkSkolem("a", nm->booleanType());
  Node b = nm->mkSkolem("b", nm->booleanType());
  Node aLTb = nm->mkSkolem("aLTb", nm->booleanType());

  Node res = theory::bv::optimalSignGadget(a, b, aLTb, eb.getCnfStream());

  eb.getCnfStream()->ensureLiteral(res);
  
  out << "c i " << eb.getCnfStream()->getLiteral(a) <<" "
      << eb.getCnfStream()->getLiteral(b) <<" "
      << eb.getCnfStream()->getLiteral(aLTb) <<" "
      << eb.getCnfStream()->getLiteral(res) <<"0 " << std::endl;
  

  CVC4::prop::SatLiteral aSLTb = eb.getCnfStream()->getLiteral(res);
  out << "c " << aSLTb << " : aSLTb" << std::endl;
  out << "c " << eb.getCnfStream()->getLiteral(aLTb) <<" : aLTb"<< std::endl; 
  eb.printCnfMapping(out, NodeSet(), true);
  eb.printProblemClauses(out);
}


void makeAdd3DoubleCarryGadget(std::ostream& out) {
  EncodingBitblaster eb(new context::Context(), "Add3DoubleCarryGadget");
  out << "c " << eb.getName() << std::endl;
  
  NodeManager* nm = NodeManager::currentNM();
  Node x1 = nm->mkSkolem("x1", nm->booleanType());
  Node x2 = nm->mkSkolem("x2", nm->booleanType());
  Node x3 = nm->mkSkolem("x3", nm->booleanType());

  Node carry0 = nm->mkSkolem("carry0", nm->booleanType());
  Node carry1 = nm->mkSkolem("carry1", nm->booleanType());

  pair<Node, Node> carry_pair(carry0, carry1);
  CVC4::prop::CnfStream* cnf = eb.getCnfStream();
  pair<Node, pair<Node, Node> > res = theory::bv::add3DoubleCarryGadget(x1,
                                                                      x2,
                                                                      x3,
                                                                      carry_pair,
                                                                      cnf);
  Node sum = res.first;
  Node carry_out0 = res.second.first;
  Node carry_out1 = res.second.second;
  
  eb.getCnfStream()->ensureLiteral(sum);
  eb.getCnfStream()->ensureLiteral(carry_out0);
  eb.getCnfStream()->ensureLiteral(carry_out1);

  // auxiliary mayhem!
  std::vector<Node> aux;
  aux.push_back(utils::mkAnd(x1, x2));
  aux.push_back(utils::mkAnd(x3, utils::mkAnd(x1, x2)));

  aux.push_back(utils::mkAnd(carry0, carry1));
  aux.push_back(utils::mkAnd(carry_out0, utils::mkAnd(carry0, carry1)));


  for (unsigned i = 0; i < aux.size(); ++i) {
    eb.getCnfStream()->ensureLiteral(aux[i]);
  }
  CVC4::prop::SatLiteral sum_lit = eb.getCnfStream()->getLiteral(sum);
  out << "c " << sum_lit << " : sum" << std::endl;
  CVC4::prop::SatLiteral carry_out0_lit = eb.getCnfStream()->getLiteral(carry_out0);
  out << "c " << carry_out0_lit << " : carry_out0" << std::endl;
  CVC4::prop::SatLiteral carry_out1_lit = eb.getCnfStream()->getLiteral(carry_out1);
  out << "c " << carry_out1_lit << " : carry_out1" << std::endl;

  out << "c i "
      << eb.getCnfStream()->getLiteral(x1) <<" "
      << eb.getCnfStream()->getLiteral(x2) <<" "
      << eb.getCnfStream()->getLiteral(x3) <<" "
      << eb.getCnfStream()->getLiteral(carry0) <<" "
      << eb.getCnfStream()->getLiteral(carry1) <<" "
      << eb.getCnfStream()->getLiteral(sum) <<" "
      << eb.getCnfStream()->getLiteral(carry_out0) <<" "
      << eb.getCnfStream()->getLiteral(carry_out1) << "0" << std::endl;

  
  NodeSet inputs;
  inputs.insert(sum);
  inputs.insert(carry_out0);
  inputs.insert(carry_out1);
  
  inputs.insert(x1);
  inputs.insert(x2);
  inputs.insert(x3);
  inputs.insert(carry0);
  inputs.insert(carry1);
  eb.printCnfMapping(out, inputs, true);
  eb.printProblemClauses(out);
}

void makeAdd3Optimal(unsigned width, std::ostream&out) {
    
  EncodingBitblaster eb(new context::Context(), "Add3Optimal");
  NodeManager* nm = NodeManager::currentNM();

  out << "c " << eb.getName() << std::endl;
  std::vector<Node> bits_a1(width);
  std::vector<Node> bits_a2(width);
  std::vector<Node> bits_a3(width);

  NodeSet inputs;
  
  for (unsigned  i = 0; i < width; ++i){
    bits_a1[i] = nm->mkSkolem("a1", nm->booleanType());
    bits_a2[i] = nm->mkSkolem("a2", nm->booleanType());
    bits_a3[i] = nm->mkSkolem("a3", nm->booleanType());
    inputs.insert(bits_a1[i]);
    inputs.insert(bits_a2[i]);
    inputs.insert(bits_a3[i]);
  }

  std::vector<Node> res_bits = theory::bv::add3OptimalGadget(bits_a1,
							     bits_a2,
							     bits_a3,
							     eb.getCnfStream());

  for (unsigned i = 0; i < res_bits.size(); ++i) {
    eb.getCnfStream()->ensureLiteral(res_bits[i]);
    CVC4::prop::SatLiteral res_lit = eb.getCnfStream()->getLiteral(res_bits[i]);
    out << "c " << res_lit << " : res" << i << std::endl;
    inputs.insert(res_bits[i]);
  }

  out << "c i " ;
  for (unsigned i = 0; i < res_bits.size(); ++i) {
    out << eb.getCnfStream()->getLiteral(bits_a1[i]) <<" "
	<< eb.getCnfStream()->getLiteral(bits_a2[i]) <<" "
	<< eb.getCnfStream()->getLiteral(bits_a3[i]) <<" "
	<< eb.getCnfStream()->getLiteral(res_bits[i]) <<" ";
  }
  out << "0" << std::endl;
  
  eb.printCnfMapping(out, inputs, true);
  eb.printProblemClauses(out);
}


void equivalenceCheckerTerm(TBitblaster<Node>::TermBBStrategy e1, std::string name1, 
			    TBitblaster<Node>::TermBBStrategy e2, std::string name2,
			    Kind k, unsigned bitwidth, unsigned num_children = 2) {

  context::Context ctx;

  EncodingBitblaster eb(&ctx, name1+"_vs_"+name2);

  eb.setTermBBStrategy(k, e1);
  std::vector<Node> children1;
  for (unsigned i = 0; i < num_children; ++i) {
    children1.push_back(utils::mkVar("x1", bitwidth));
  }
  Node res1 = utils::mkVar("res1", bitwidth);
  Node op_ch1 = utils::mkNode(k, children1);
  Node eq1 = utils::mkNode(kind::EQUAL, res1, op_ch1);
  eb.assertFact(eq1);
  
  eb.setTermBBStrategy(k, e2);
  std::vector<Node> children2;
  for (unsigned i = 0; i < num_children; ++i) {
    children2.push_back(utils::mkVar("x2", bitwidth));
  }
  Node res2 = utils::mkVar("res2", bitwidth);
  Node op_ch2 = utils::mkNode(k, children2);
  Node eq2 = utils::mkNode(kind::EQUAL, res2, op_ch2);
  eb.assertFact(eq2);

  for(unsigned i = 0; i < num_children; ++i) {
    eb.assertFact(utils::mkNode(kind::EQUAL, children1[i], children2[i]));
  }
  eb.assertFact(utils::mkNode(kind::NOT, utils::mkNode(kind::EQUAL, res1, res2)));

  bool res = eb.solve();
  if (res) {
    std::cout << "NOT EQUIVALENT " << name1 << "  " << name2 << std::endl;
    std::cout << "Model from "<< name1 <<":"<< std::endl;
    for (unsigned i = 0; i < num_children; ++i) {
      std::cout <<"  "<< children1[i] <<": "
                << eb.getModelFromSatSolver(children1[i], false) << std::endl;
    }
    std::cout <<"  "<< res1 <<": " << eb.getModelFromSatSolver(res1, false) << std::endl;
    std::cout << "Model from "<< name2 <<":"<< std::endl;
    for (unsigned i = 0; i < num_children; ++i) {
      std::cout <<"  "<< children2[i] <<": "
                << eb.getModelFromSatSolver(children2[i], false) << std::endl;
    }
    std::cout <<"  "<< res2 <<": " << eb.getModelFromSatSolver(res2, false) << std::endl;
  } else {
    std::cout << "EQUIVALENT bw"<<bitwidth<< " " << name1 << "  " << name2 << std::endl;
  }
}

void equivalenceCheckerAtom(TBitblaster<Node>::AtomBBStrategy e1, std::string name1, 
			    TBitblaster<Node>::AtomBBStrategy e2, std::string name2,
			    Kind k, unsigned bitwidth) {

  context::Context ctx;

  EncodingBitblaster eb(&ctx, name1+"_vs_"+name2);
  NodeManager* nm = NodeManager::currentNM();
  
  eb.setAtomBBStrategy(k, e1);
  Node a1 = utils::mkVar(bitwidth);
  Node b1 = utils::mkVar(bitwidth);
  Node a1_op_b1 = utils::mkNode(k, a1, b1);
  Node c1 = nm->mkSkolem("c", nm->booleanType());
  Node eq1 = utils::mkNode(kind::IFF, c1, a1_op_b1);
  eb.assertFact(eq1);
  
  eb.setAtomBBStrategy(k, e2);
  Node a2 = utils::mkVar(bitwidth);
  Node b2 = utils::mkVar(bitwidth);
  Node a2_op_b2 = utils::mkNode(k, a2, b2);
  Node c2 = nm->mkSkolem("c", nm->booleanType());
  Node eq2 = utils::mkNode(kind::IFF, c2, a2_op_b2);
  eb.assertFact(eq2);

  eb.assertFact(utils::mkNode(kind::EQUAL, a1, a2));
  eb.assertFact(utils::mkNode(kind::EQUAL, b1, b2));
  eb.assertFact(utils::mkNode(kind::NOT, utils::mkNode(kind::IFF, c1, c2)));

  bool res = eb.solve();
  if (res) {
    std::cout << "NOT EQUIVALENT " << name1 << "  " << name2 << std::endl;
    std::cout << a1 <<": " << eb.getModelFromSatSolver(a1, false) << std::endl;
    std::cout << a2 <<": " << eb.getModelFromSatSolver(a2, false) << std::endl;
    std::cout << b1 <<": " << eb.getModelFromSatSolver(b1, false) << std::endl;
    std::cout << b2 <<": " << eb.getModelFromSatSolver(b2, false) << std::endl;
    std::cout << c1 <<": " << eb.getModelFromSatSolver(c1, false) << std::endl;
    std::cout << c2 <<": " << eb.getModelFromSatSolver(c2, false) << std::endl;
  } else {
    std::cout << "EQUIVALENT bw"<<bitwidth<< " " << name1 << "  " << name2 << std::endl;
  }
}

void generateReferenceEncodingsSAT15() {

  printAtomEncoding(kind::BITVECTOR_ULT, DefaultUltBB<Node>, "cvc-ult", 6);
  // printAtomEncoding(kind::BITVECTOR_ULE, DefaultUleBB<Node>, "cvc-ule", 6);
  // printAtomEncoding(kind::BITVECTOR_SLT, DefaultSltBB<Node>, "cvc-slt", 6);
  // printAtomEncoding(kind::BITVECTOR_SLE, DefaultSleBB<Node>, "cvc-sle", 6);
  
  printTermEncoding(kind::BITVECTOR_PLUS, DefaultPlusBB<Node>, "cvc-plus", 3);
  printTermEncoding(kind::BITVECTOR_PLUS, DefaultPlusBB<Node>, "cvc-plus", 4);

  printTermEncoding(kind::BITVECTOR_MULT, DefaultMultBB<Node>, "cvc-mult2-2n", 2, false, false);
  printTermEncoding(kind::BITVECTOR_MULT, DefaultMultBB<Node>, "cvc-mult2-2n", 2, true, false);
  printTermEncoding(kind::BITVECTOR_MULT, DefaultMultBB<Node>, "cvc-mult4", 4, false);

  printAtomEncoding(kind::BITVECTOR_ULT, OptimalUltBB<Node>, "cvc-ult-opt", 6);
  // printAtomEncoding(kind::BITVECTOR_ULE, DefaultUleBB<Node>, "cvc-ule", 6);
  // printAtomEncoding(kind::BITVECTOR_SLT, DefaultSltBB<Node>, "cvc-slt", 6);
  // printAtomEncoding(kind::BITVECTOR_SLE, DefaultSleBB<Node>, "cvc-sle", 6);
  
  printTermEncoding(kind::BITVECTOR_PLUS, OptimalPlusBB<Node>, "cvc-plus-opt", 3);
  printTermEncoding(kind::BITVECTOR_PLUS, OptimalPlusBB<Node>, "cvc-plus-opt", 4);
  
  {
    ofstream outfile;
    outfile.open ("cvc-full-adder.cnf");
    makeFullAdder(outfile);
    outfile.close();
  }

  {
    ofstream outfile;
    outfile.open ("cvc-ult-gadget.cnf");
    makeLTNewGadget(outfile);
    outfile.close();
  }

  {
    ofstream outfile;
    outfile.open ("cvc-slt-gadget.cnf");
    makeSignedGadget(outfile);
    outfile.close();
  }

  {
    ofstream outfile;
    outfile.open ("cvc-add3-carry2-gadget.cnf");
    makeAdd3DoubleCarryGadget(outfile);
    outfile.close();
  }

  {
    ofstream outfile;
    outfile.open ("cvc-add3-opt-bw3.cnf");
    makeAdd3Optimal(3, outfile);
    outfile.close();
  }
  
}

void generateReferenceEncodings(unsigned k, Options& opts) {
  Assert (k >= 2);
  // to test generating optimal encodings (and optimality of current designs)
  for (unsigned i = 2; i <= k; ++i) {
     printAtomEncoding(kind::BITVECTOR_ULT, DefaultUltBB<Node>, "cvc-ult", i);
     printAtomEncoding(kind::BITVECTOR_ULE, DefaultUleBB<Node>, "cvc-ule", i);
     printAtomEncoding(kind::BITVECTOR_SLT, DefaultSltBB<Node>, "cvc-slt", i);
     printAtomEncoding(kind::BITVECTOR_SLE, DefaultSleBB<Node>, "cvc-sle", i);
     printTermEncoding(kind::BITVECTOR_PLUS, DefaultPlusBB<Node>, "cvc-plus", i);

    // printAtomEncoding(kind::BITVECTOR_ULT, OptimalUltBB<Node>, "optimal-ult", i);
    // printAtomEncoding(kind::BITVECTOR_ULE, OptimalUleBB<Node>, "optimal-ule", i);
    // printAtomEncoding(kind::BITVECTOR_SLT, OptimalSltBB<Node>, "optimal-slt", i);
    // printAtomEncoding(kind::BITVECTOR_SLE, OptimalSleBB<Node>, "optimal-sle", i);
    // printTermEncoding(kind::BITVECTOR_PLUS, OptimalPlusBB<Node>, "optimal-plus", i);

    // opts[options::bvBlock2Mult] = true;
    
    printTermEncoding(kind::BITVECTOR_MULT, MultBlock2BB<Node>, "optimal-mult-bl2", i);
    printTermEncoding(kind::BITVECTOR_MULT, MultBlock2BB<Node>, "optimal-mult-bl2", i, true);
    printTermEncoding(kind::BITVECTOR_MULT, MultBlock2BB<Node>, "optimal-mult-bl2", i, false, false);
    printTermEncoding(kind::BITVECTOR_MULT, MultBlock2BB<Node>, "optimal-mult-bl2", i, true, false);

    // opts[options::bvBlock2Mult] = false;
    // opts[options::bvBlock2MultOpt] = true;
    
    // printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "optimal-mult-bl2", i);
    // printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "optimal-mult-bl2", i, true);
    // printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "optimal-mult-bl2", i, false, false);
    // printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "optimal-mult-bl2", i, true, false);

  }
}



void checkZooMultipliers(Options& opts) {
  unsigned width = opts[options::encodingBitwidth];
  std::vector<FullAdderEncoding> fullAdderEncodings;
  fullAdderEncodings.push_back(TSEITIN_NAIVE_AB_CIRCUIT);
  fullAdderEncodings.push_back(TSEITIN_NAIVE_AC_CIRCUIT);
  fullAdderEncodings.push_back(TSEITIN_NAIVE_BC_CIRCUIT);
  fullAdderEncodings.push_back(TSEITIN_SHARED_AB_CIRCUIT);
  fullAdderEncodings.push_back(TSEITIN_SHARED_AC_CIRCUIT);
  fullAdderEncodings.push_back(TSEITIN_SHARED_BC_CIRCUIT);
  fullAdderEncodings.push_back(DANIEL_COMPACT_CARRY);
  fullAdderEncodings.push_back(MINISAT_SUM_AND_CARRY);
  fullAdderEncodings.push_back(MINISAT_COMPLETE);
  fullAdderEncodings.push_back(MARTIN_OPTIMAL);

  std::vector<Add2Encoding::Style> add2Styles;
  add2Styles.push_back(Add2Encoding::RIPPLE_CARRY);   
  // add2Styles.push_back(CARRY_LOOKAHEAD);
  // add2Styles.push_back(CARRY_SELECT); 
  std::vector<Add3Encoding::Style> add3Styles;
  add3Styles.push_back(Add3Encoding::OPTIMAL_ADD3);
  add3Styles.push_back(Add3Encoding::THREE_TO_TWO_THEN_ADD);

  std::vector<AccumulateEncoding::Style> accStyles;
  accStyles.push_back(AccumulateEncoding::LINEAR_FORWARDS);
  accStyles.push_back(AccumulateEncoding::LINEAR_BACKWARDS);
  accStyles.push_back(AccumulateEncoding::TREE_REDUCTION);
  accStyles.push_back(AccumulateEncoding::ADD3_LINEAR_FORWARDS);
  accStyles.push_back(AccumulateEncoding::ADD3_LINEAR_BACKWARDS);
  accStyles.push_back(AccumulateEncoding::ADD3_TREE_REDUCTION);

  std::vector<PartialProductEncoding> partialProductEncodings;
  partialProductEncodings.push_back(CONVENTIONAL);
  partialProductEncodings.push_back(BLOCK2_BY_ADDITION);
  partialProductEncodings.push_back(BLOCK3_BY_ADDITION);
  partialProductEncodings.push_back(BLOCK4_BY_ADDITION);
  // partialProductEncodings.push_back(BLOCK5_BY_ADDITION);
  // partialProductEncodings.push_back(BLOCK2_BY_CONSTANT_MULTIPLICATION);
  // partialProductEncodings.push_back(BLOCK3_BY_CONSTANT_MULTIPLICATION);
  // partialProductEncodings.push_back(BLOCK4_BY_CONSTANT_MULTIPLICATION);
  // partialProductEncodings.push_back(BLOCK5_BY_CONSTANT_MULTIPLICATION);
  // partialProductEncodings.push_back(OPTIMAL_2_BY_2);
  // partialProductEncodings.push_back(OPTIMAL_3_BY_3);
  // partialProductEncodings.push_back(OPTIMAL_4_BY_4);
  // partialProductEncodings.push_back(OPTIMAL_5_BY_);

  std::vector<ReductionEncoding> reductionStyles;
  reductionStyles.push_back(WORD_LEVEL);
  reductionStyles.push_back(WALLACE_TREE);
  // reductionStyle.push_back(DADDA_TREE);
  // reductionStyle.push_back(UNARY_TO_BINARY_REDUCTION);`
  // reductionStyle.push_back(CARRY_SAVE_LINEAR_REDUCTION);
  // reductionStyle.push_back(CARRY_SAVE_TREE_REDUCTION);
  for (unsigned fa = 0; fa < fullAdderEncodings.size(); ++fa) {
    for (unsigned add2 = 0; add2 < add2Styles.size(); ++add2) {
      for (unsigned add3 = 0; add3 < add3Styles.size(); ++add3) {
	for (unsigned acc = 0; acc < accStyles.size(); ++acc) {
	  for (unsigned pp = 0; pp < partialProductEncodings.size(); ++pp) {
	    for (unsigned red = 0; red< reductionStyles.size(); ++red) {
	     
	      FullAdderEncoding fullAdderEncoding = fullAdderEncodings[fa];
	      Add2Encoding::Style add2Style = add2Styles[add2];
	      size_t carrySelectMin = -1;
	      size_t carrySelectSplit = -1;

	      Add2Encoding add2Enc(fullAdderEncoding,
				   add2Style,
				   carrySelectMin,
				   carrySelectSplit);

	      Add3Encoding::Style add3Style = add3Styles[add3];
	      Add3Encoding add3Enc(add3Style,
				   fullAdderEncoding,
				   add2Enc);
  
	      AccumulateEncoding::Style accStyle = accStyles[acc];

	      AccumulateEncoding accEncoding(add2Enc, add3Enc, accStyle);

	      RecursiveMultiplicationEncoding recursionStyle = DEFAULT_REC;
	      PartialProductEncoding partialProductEncoding = partialProductEncodings[pp];
	      ReductionEncoding reductionStyle = reductionStyles[red];

	      std::cout << "checkZooMultipliers for " << fullAdderEncoding << " "
			<< "  add2Style " << add2Style <<" " << std::endl
			<< "  add3Style " << add3Style <<" " << std::endl
			<< "  accStyle " << accStyle << " " << std::endl
			<< "  partialProductEncoding " << partialProductEncoding << " " << std::endl
			<< "  reductionStyle " << reductionStyle << std::endl;
	     
	      MultiplyEncoding multStyle(recursionStyle,
					 partialProductEncoding,
					 reductionStyle,
					 accEncoding);

	      MultiplyEncoding::setCurrent(multStyle);
	      equivalenceCheckerTerm(ZooMultBB<Node>, "zoo-add-mult",
				     DefaultMultBB<Node>, "default-mult",
				     kind::BITVECTOR_MULT, width);

	    }
	  }
	}
      }
    }
  }
}

void CVC4::runEncodingExperiment(Options& opts) {
  ExprManager em;
  SmtEngine smt(&em);
  smt::SmtScope scope(&smt);
  std::cout << "Running encoding experiments " << std::endl; 

  unsigned num_fixed = opts[options::encodingNumFixed];
  unsigned width = opts[options::encodingBitwidth];

  
  /**** Generating CNF encoding files for operations ****/

  generateReferenceEncodingsSAT15();
  // generateReferenceEncodings(width, opts);



  // printMult4x4x8(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>);

  // EncodingComparator ec_plus(3, kind::BITVECTOR_MULT, true,
  // 			     DefaultMultBB<Node>, "default-mult",
  // 			     OptimalAddMultBB<Node>, "optimal-add-mult");

  // sampleAssignments(num_fixed, 3*3, &ec_plus, true);
  // ec_plus.printResults(std::cout);

  /********* Equivalence Check Comparison ****************/
  
  // equivalenceCheckerAtom(OptimalUltBB<Node>, "optimal-ult",
  // 			 DefaultUltBB<Node>, "default-ult",
  // 			 kind::BITVECTOR_ULT, width);

  // equivalenceCheckerAtom(OptimalUleBB<Node>, "optimal-ule",
  // 			 DefaultUleBB<Node>, "default-ule",
  // 			 kind::BITVECTOR_ULE, width);

  // equivalenceCheckerAtom(OptimalSleBB<Node>, "optimal-sle",
  // 			 DefaultSleBB<Node>, "default-sle",
  // 			 kind::BITVECTOR_SLE, width);
  
  // equivalenceCheckerAtom(OptimalSltBB<Node>, "optimal-slt",
  // 			 DefaultSltBB<Node>, "default-slt",
  // 			 kind::BITVECTOR_SLT, width);


  /********* Equivalence Check Plus ****************/

  // equivalenceCheckerTerm(OptimalPlusBB<Node>, "optimal-add",
  // 			 DefaultPlusBB<Node>, "default-add",
  // 			 kind::BITVECTOR_PLUS, width);

  // equivalenceCheckerTerm(Add3PlusBB<Node>, "add3-plus",
  // 			 DefaultPlusBB<Node>, "default-plus",
  // 			 kind::BITVECTOR_PLUS, width, 3);

  
  /********* Equivalence Check Mult ****************/


  // checkZooMultipliers(opts); 
  


  // equivalenceCheckerTerm(OptimalAddMultBB<Node>, "optimal-add-mult",
  // 			 DefaultMultBB<Node>, "default-mult",
  // 			 kind::BITVECTOR_MULT, width);

  // equivalenceCheckerTerm(Mult3BottomBB<Node>, "optimal-mult4bot",
  //  			 DefaultMultBB<Node>, "default-mult",
  //  			 kind::BITVECTOR_MULT, width);

  // equivalenceCheckerTerm(Mult4BottomBB<Node>, "optimal-mult4bot",
  //  			 DefaultMultBB<Node>, "default-mult",
  //  			 kind::BITVECTOR_MULT, width);

  // equivalenceCheckerTerm(DebugMultBB<Node>, "debug-mult",
  // 			 DefaultMultBB<Node>, "default-mult",
  // 			 kind::BITVECTOR_MULT, width);

  // equivalenceCheckerTerm(MultBlock2BB<Node>, "optimal-mult-block2",
  // 			 DefaultMultBB<Node>, "default-mult",
  // 			 kind::BITVECTOR_MULT, width);

  // equivalenceCheckerTerm(Mult3BB<Node>, "optimal-mult3",
  // 			 DefaultMultBB<Node>, "default-mult",
  // 			 kind::BITVECTOR_MULT, width);
  
  // equivalenceCheckerTerm(Mult4BB<Node>, "optimal-mult4",
  // 			 DefaultMultBB<Node>, "default-mult",
  // 			 kind::BITVECTOR_MULT, width);


  // makeLTGadget();
  //testUltGadget();
  // makeLTGenGadget();
  // makeSignedGadget();
  // BruteForceTermOptChecker opt(width, kind::BITVECTOR_MULT,
  // 			          DefaultMultBB<Node>, "default-mult",
  // 			          OptimalAddMultBB<Node>, "optimal-add-mult");

  // sampleAssignments(9, 3*3, &opt, false);
  // opt.printResults();
  
  // EncodingComparator ec_plus(width, kind::BITVECTOR_PLUS, false,
  // 			     DefaultPlusBB<Node>, "default-plus",
  // 			     OptimalPlusBB<Node>, "optimal-plus");

  // sampleAssignments(num_fixed, width*3, &ec_plus, true);
  // ec_plus.printResults(std::cout);

  // EncodingComparator ec1(width, kind::BITVECTOR_MULT, false,
  // 			DefaultMultBB<Node>, "default-mult1",
  // 			OptimalAddMultBB<Node>, "optimal-add-mult");
  
  // sampleAssignments(num_fixed, width*3, &ec1, true);
  // ec1.printResults(std::cout);

  // EncodingComparator ec2(width, kind::BITVECTOR_MULT, false,
  // 			DefaultMultBB<Node>, "default-mult2",
  // 			MultBlock2BB<Node>, "mult-block2");
  
  // sampleAssignments(num_fixed, width*3, &ec2, true);
  // ec2.printResults(std::cout);

  // EncodingComparator ec3(width, kind::BITVECTOR_MULT, false,
  // 			DefaultMultBB<Node>, "default-mult3",
  // 			Mult3BottomBB<Node>, "mult-bot3");
  
  // sampleAssignments(num_fixed, width*3, &ec3, true);
  // ec3.printResults(std::cout);

  // EncodingComparator ec4(width, kind::BITVECTOR_MULT, false,
  // 			 MultBlock2BB<Node>, "mult-block2`",
  // 			 Mult3BottomBB<Node>, "mult-bot3`");
  
  // sampleAssignments(num_fixed, width*3, &ec4, true);
  // ec4.printResults(std::cout);

  
  // EncodingComparator ec_mult(width, kind::BITVECTOR_MULT, false,
  // 			     DefaultMultBB<Node>, "default-mult",
  // 			     OptimalAddMultBB<Node>, "optimal-add-mult");

  // sampleAssignments(num_fixed, width*3, &ec_mult, true);
  // ec_mult.printResults(std::cout);

  
  // EncodingContradiction ec_default(width, kind::BITVECTOR_PLUS, DefaultPlusBB<Node>, "default-plus");
  // EncodingContradiction ec_optimal(width, kind::BITVECTOR_PLUS, OptimalPlusBB<Node>, "optimal-plus");

  // sampleAssignments(num_fixed, width*3, &ec_default, true);
  // sampleAssignments(num_fixed, width*3, &ec_optimal, true);
  // ec_default.print(std::cout);
  // ec_optimal.print(std::cout);
}
