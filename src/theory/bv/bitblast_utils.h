/*********************                                                        */
/*! \file bitblast_utils.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Various utility functions for bit-blasting.
 **
 ** Various utility functions for bit-blasting.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLAST__UTILS_H
#define __CVC4__BITBLAST__UTILS_H


#include <ostream>
#include "expr/node.h"
#include "prop/cnf_stream.h"

#ifdef CVC4_USE_ABC
#include "base/main/main.h"
#include "base/abc/abc.h"


extern "C" {
#include "sat/cnf/cnf.h"
}
#endif

namespace CVC4 {

namespace theory {
namespace bv {

template <class T> class TBitblaster;

template <class T> 
std::string toString (const std::vector<T>& bits);

template <> inline
std::string toString<Node>(const std::vector<Node>& bits) {
  std::ostringstream os;
  for (int i = bits.size() - 1; i >= 0; --i) {
    TNode bit = bits[i];
    if (bit.getKind() == kind::CONST_BOOLEAN) {
      os << (bit.getConst<bool>() ? "1" : "0");
    } else {
      os << bit<< " ";
    }
  }
  os <<"\n";
  return os.str();
} 

template <class T> T mkBitVar() {Unreachable(); return T();}
template <class T> T mkTrue();  
template <class T> T mkFalse(); 
template <class T> T mkNot(T a);
template <class T> T mkOr(T a, T b);
template <class T> T mkOr(const std::vector<T>& a);
template <class T> T mkAnd(T a, T b);
template <class T> T mkAnd(const std::vector<T>& a);
template <class T> T mkXor(T a, T b);
template <class T> T mkIff(T a, T b);
template <class T> T mkIte(T cond, T a, T b);

template <> inline
Node mkBitVar<Node>() {
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkSkolem("bit", nm->booleanType(), "bit-blast bool variable"); 
}
 
template <> inline
Node mkTrue<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(true);
}

template <> inline
Node mkFalse<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(false);
}

template <> inline
Node mkNot<Node>(Node a) {
  return NodeManager::currentNM()->mkNode(kind::NOT, a);
}

template <> inline
Node mkOr<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b);
}

template <> inline
Node mkOr<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::OR, children); 
}


template <> inline
Node mkAnd<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::AND, a, b);
}

template <> inline
Node mkAnd<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::AND, children); 
}


template <> inline
Node mkXor<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::XOR, a, b);
}

template <> inline
Node mkIff<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::IFF, a, b);
}

template <> inline
Node mkIte<Node>(Node cond, Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::ITE, cond, a, b);
}

/*
 Various helper functions that get called by the bitblasting procedures
 */

template <class T>
void inline extractBits(const std::vector<T>& b, std::vector<T>& dest, unsigned lo, unsigned hi) {
  Assert ( lo < b.size() && hi < b.size() && lo <= hi);
  for (unsigned i = lo; i <= hi; ++i) {
    dest.push_back(b[i]); 
  }
}


template <class T>
void inline negateBits(const std::vector<T>& bits, std::vector<T>& negated_bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(mkNot(bits[i])); 
  }
}

template <class T>
bool inline isZero(const std::vector<T>& bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    if(bits[i] != mkFalse<T>()) {
      return false; 
    }
  }
  return true; 
}
 
template <class T>
void inline rshift(std::vector<T>& bits, unsigned amount) {
  for (unsigned i = 0; i < bits.size() - amount; ++i) {
    bits[i] = bits[i+amount]; 
  }
  for(unsigned i = bits.size() - amount; i < bits.size(); ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline lshift(std::vector<T>& bits, unsigned amount) {
  for (int i = (int)bits.size() - 1; i >= (int)amount ; --i) {
    bits[i] = bits[i-amount]; 
  }
  for(unsigned i = 0; i < amount; ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline zeroExtendBits(const std::vector<T>& a,
			   std::vector<T>& dest,
			   unsigned amount) {
  for (unsigned i = 0; i < a.size() ; ++i) {
    dest.push_back(a[i]); 
  }
  for (unsigned i = 0; i < amount; ++i) {
    dest.push_back(mkFalse<T>());
  }
}

template <class T>
void inline zeroExtendBits(std::vector<T>& a,
			   unsigned amount) {
  for (unsigned i = 0; i < amount; ++i) {
    a.push_back(mkFalse<T>());
  }
}
 
 
template <class T>
void inline makeZero(std::vector<T>& bits, unsigned width) {
  Assert(bits.size() == 0); 
  for(unsigned i = 0; i < width; ++i) {
    bits.push_back(mkFalse<T>()); 
  }
}

template <class T>
std::pair<T,T> inline fullAdder(const T a, const T b, const T cin) {
  T cout = mkOr(mkAnd(a, b),
		mkAnd(mkXor(a, b),
		      cin));;
  T sum = mkXor(mkXor(a, b), cin);
  return std::make_pair(sum, cout);
}
 

 
/****** Helper functions that return vectors ****/
// compiler should in theory optimize this 
 
template <class T>
std::vector<T> inline makeNot(const std::vector<T>& bits) {
  std::vector<T> negated_bits;
  for(unsigned i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(mkNot(bits[i])); 
  }
  return negated_bits;
}

template <class T>
std::vector<T> inline makeIte(const T& cond,
			      const std::vector<T>& then_bits,
			      const std::vector<T>& else_bits) {
  std::vector<T> res;
  Assert (then_bits.size() == else_bits.size()); 
  for(unsigned i = 0; i < then_bits.size(); ++i) {
    res.push_back(mkIte(cond, then_bits[i], else_bits[i])); 
  }
  return res;
}

template <class T>
std::vector<T> inline makeLShift(const std::vector<T>& bits,
				 unsigned amount) {
  std::vector<T> res;
  for(unsigned i = 0; i < amount; ++i) {
    res.push_back(mkFalse<T>()); 
  }
  for (unsigned i = 0; i < bits.size() - amount; ++i) {
    res.push_back(bits[i]); 
  }
  return res;
}
 

template <class T>
std::vector<T> inline makeZero(unsigned width) {
  std::vector<T> bits;
  Assert(bits.size() == 0); 
  for(unsigned i = 0; i < width; ++i) {
    bits.push_back(mkFalse<T>()); 
  }
  return bits;
}

template <class T>
std::vector<T> inline makeZeroExtend(const std::vector<T>& a,
				     unsigned amount) {
  std::vector<T> dest; 
  for (unsigned i = 0; i < a.size() ; ++i) {
    dest.push_back(a[i]); 
  }
  for (unsigned i = 0; i < amount; ++i) {
    dest.push_back(mkFalse<T>());
  }
  return dest;
}
 
template <class T>
std::vector<T> inline makeOr(const std::vector<T>& a,
			     const std::vector<T>& b) {
  std::vector<T> res;
  Assert(res.size() == 0 && a.size() == b.size()); 
  for(unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkOr<T>(a[i], b[i])); 
  }
  return res; 
}

template <class T>
std::vector<T> inline makeAndBit(const T& a,
				 const std::vector<T>& b) {
  std::vector<T> res;
  Assert(res.size() == 0); 
  for(unsigned i = 0; i < b.size(); ++i) {
    res.push_back(mkAnd<T>(a, b[i])); 
  }
  return res;
}
 
 

 
/** 
 * Constructs a simple ripple carry adder
 * 
 * @param a first term to be added
 * @param b second term to be added
 * @param res the result
 * @param carry the carry-in bit 
 * 
 * @return the carry-out
 */
template <class T>
T inline rippleCarryAdder(const std::vector<T>&a, const std::vector<T>& b,
			  std::vector<T>& res, T cin) {
  Assert(a.size() == b.size() && res.size() == 0);

  T sum;
  T carry = cin;
  std::pair<T, T> fa_res;
  for (unsigned i = 0 ; i < a.size(); ++i) {
    fa_res = fullAdder(a[i], b[i], carry);
    sum = fa_res.first;
    carry = fa_res.second;
    res.push_back(sum); 
  }

  return carry;
}

 
template <class T>
inline void shiftAddMultiplier(const std::vector<T>&a, const std::vector<T>&b, std::vector<T>& res) {
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkAnd(b[0], a[i])); 
  }
  
  for(unsigned k = 1; k < res.size(); ++k) {
    T carry_in = mkFalse<T>();
    std::pair<T, T> fa_res;
    for(unsigned j = 0; j < res.size() -k; ++j) {
      T aj = mkAnd(a[j], b[k]);
      fa_res = fullAdder(res[j+k], aj, carry_in);
      res[j+k] = fa_res.first;
      carry_in = fa_res.second;
    }
  }
}
 

template <class T>
T inline uLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());

  T res = mkAnd(mkNot(a[0]), b[0]);
  
  if(orEqual) {
    res = mkOr(res, mkIff(a[0], b[0])); 
  }
  
  for (unsigned i = 1; i < a.size(); ++i) {
    // a < b iff ( a[i] <-> b[i] AND a[i-1:0] < b[i-1:0]) OR (~a[i] AND b[i]) 
    res = mkOr(mkAnd(mkIff(a[i], b[i]), res),
               mkAnd(mkNot(a[i]), b[i])); 
  }
  return res;
}
 
template <class T>
T inline sLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());
  if (a.size() == 1) {
    if(orEqual) {
      return  mkOr(mkIff(a[0], b[0]),
                   mkAnd(a[0], mkNot(b[0]))); 
    }

    return mkAnd(a[0], mkNot(b[0]));
  }
  unsigned n = a.size() - 1; 
  std::vector<T> a1, b1;
  extractBits(a, a1, 0, n-1);
  extractBits(b, b1, 0, n-1);
  
  // unsigned comparison of the first n-1 bits
  T ures = uLessThanBB(a1, b1, orEqual);
  T res = mkOr(// a b have the same sign
               mkAnd(mkIff(a[n], b[n]),
                     ures),
               // a is negative and b positive
               mkAnd(a[n],
                     mkNot(b[n])));
  return res;
}

template<class T>
std::vector<T> multByConst(const std::vector<T>& a,
                           unsigned K,
                           CVC4::prop::CnfStream* cnf) {
  Assert (1 << a.size() > K);
  BitVector val(a.size(), K);

  std::vector<T> val_bits(a.size());
  for (int i = 0; i < a.size(); ++i) {
    if (val.isBitSet(i)) {
      val_bits[i] = mkTrue<T>();
    } else {
      val_bits[i] = mkFalse<T>();
    }
  }
  std::vector<T> res;
  shiftAddMultiplier(a, val_bits, res);
  return res;
}


 
}
}
}
 

#endif
