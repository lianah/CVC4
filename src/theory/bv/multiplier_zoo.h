/*********************                                                        */
/*! \file multiplier_zoo.h
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

#ifndef __CVC4__MULTIPLIER__ZOO_H
#define __CVC4__MULTIPLIER__ZOO_H


#include <ostream>
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "theory/bv/bitblast_utils.h"
#include "theory/bv/generated_encodings.h"

namespace CVC4 {

namespace theory {
namespace bv {

/****
  Martin Code Sketch
 ****/


typedef enum _fullAdderEncoding {
  /** Operation based **/
  TSEITIN_NAIVE_AB_CIRCUIT,    // Original CBMC
  TSEITIN_NAIVE_AC_CIRCUIT,
  TSEITIN_NAIVE_BC_CIRCUIT,
  TSEITIN_SHARED_AB_CIRCUIT,
  TSEITIN_SHARED_AC_CIRCUIT,
  TSEITIN_SHARED_BC_CIRCUIT,
  // No AIG support for now
  /* AIG_NAIVE_AB_CIRCUIT,         // Probably the worst... */
  /* AIG_NAIVE_AC_CIRCUIT, */
  /* AIG_NAIVE_BC_CIRCUIT, */
  /* AIG_SHARED_AB_CIRCUIT,        // CVC4 */
  /* AIG_SHARED_AC_CIRCUIT, */
  /* AIG_SHARED_BC_CIRCUIT, */
  
  /** Mixed **/
  DANIEL_COMPACT_CARRY,      // CBMC old default
  
  /** Clause based **/
  MINISAT_SUM_AND_CARRY,
  MINISAT_COMPLETE,          // With the 6 additional clauses
  MARTIN_OPTIMAL             // Current CBMC
} FullAdderEncoding;

template <class T>
T makeCarry(const FullAdderEncoding &fullAdderStyle,
	    const T& a, const T& b, const T& c,
	    CVC4::prop::CnfStream* cnf) {
  if (fullAdderStyle == DANIEL_COMPACT_CARRY) {
    T x = mkBitVar<T>();

    T nx = mkNot<T>(x);
    T na = mkNot<T>(a);
    T nb = mkNot<T>(b);
    T nc = mkNot<T>(c);

    NodeManager* nm = NodeManager::currentNM();
    
    cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, nx),
			  false, false, RULE_INVALID, TNode::null());
    cnf->convertAndAssert(nm->mkNode(kind::OR, a, nb, c, nx),
			  false, false, RULE_INVALID, TNode::null());
    cnf->convertAndAssert(nm->mkNode(kind::OR, a, nb, nc, x),
			  false, false, RULE_INVALID, TNode::null());
    cnf->convertAndAssert(nm->mkNode(kind::OR, na, b, c, nx),
			  false, false, RULE_INVALID, TNode::null());
    cnf->convertAndAssert(nm->mkNode(kind::OR, na, b, nc, x),
			  false, false, RULE_INVALID, TNode::null());
    cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, x),
			  false, false, RULE_INVALID, TNode::null());
    return x;
  }
  
  return mkOr(mkOr(mkAnd(a,b), mkAnd(a,c)), mkAnd(b, c));
}



template <class T>
std::pair<T, T> inline fullAdder(const FullAdderEncoding &fullAdderStyle,
				 const T &a,
				 const T &b,
				 const T &c,
				 prop::CnfStream* cnf) {
  T sum, carry;
  
  switch(fullAdderStyle) {
  case TSEITIN_NAIVE_AB_CIRCUIT:
  case DANIEL_COMPACT_CARRY:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(a, b), c);
    return std::make_pair<T, T>(sum, carry);
  case TSEITIN_NAIVE_AC_CIRCUIT:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(a, c), b);
    return std::make_pair<T, T>(sum, carry);
  case TSEITIN_NAIVE_BC_CIRCUIT:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(b, c), a);
    return std::make_pair<T, T>(sum, carry);
  case TSEITIN_SHARED_AB_CIRCUIT: {
    T cross = mkXor(a, b);
    carry = mkOr(mkAnd(a,b),mkAnd(cross, c));
    sum = mkXor(cross, c);
    return std::make_pair<T, T>(sum, carry);
  }
  case TSEITIN_SHARED_AC_CIRCUIT: {
    T cross = mkXor(a, c);
    carry = mkOr(mkAnd(a,c),mkAnd(cross, b));
    sum = mkXor(cross, b);
    return std::make_pair<T, T>(sum, carry);
  }
  case TSEITIN_SHARED_BC_CIRCUIT: {
    T cross = mkXor(b, c);
    carry = mkOr(mkAnd(b,c),mkAnd(cross, a));
    sum = mkXor(cross, a);
    return std::make_pair<T, T>(sum, carry);
  }
  case MINISAT_SUM_AND_CARRY:
  case MINISAT_COMPLETE: {
      sum = mkBitVar<T>();
      carry = mkBitVar<T>();
      T na = mkNot(a);
      T nb = mkNot(b);
      T nc = mkNot(c);
      T ncarry = mkNot(carry);
      T nsum = mkNot(sum);
      
      NodeManager* nm = NodeManager::currentNM();
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, c, nsum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, nc, sum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, carry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, ncarry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, b, nc, nsum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, b, c, sum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, na, nc, carry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, c, ncarry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, nb, nc, nsum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, nc, sum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, nb, nc, carry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, b, c, ncarry),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, c, nsum),
			    false, false, RULE_INVALID, TNode::null());
      cnf->convertAndAssert(nm->mkNode(kind::OR, a, nb, c, sum),
			    false, false, RULE_INVALID, TNode::null());
      
      if (fullAdderStyle == MINISAT_COMPLETE) {
	cnf->convertAndAssert(nm->mkNode(kind::OR, ncarry, nsum, a),
			      false, false, RULE_INVALID, TNode::null());
	cnf->convertAndAssert(nm->mkNode(kind::OR, ncarry, nsum, b),
			      false, false, RULE_INVALID, TNode::null());
	cnf->convertAndAssert(nm->mkNode(kind::OR, ncarry, nsum, c),
			      false, false, RULE_INVALID, TNode::null());
	cnf->convertAndAssert(nm->mkNode(kind::OR, carry, sum, na),
			      false, false, RULE_INVALID, TNode::null());
	cnf->convertAndAssert(nm->mkNode(kind::OR, carry, sum, nb),
			      false, false, RULE_INVALID, TNode::null());
	cnf->convertAndAssert(nm->mkNode(kind::OR, carry, sum, nc),
			      false, false, RULE_INVALID, TNode::null());
      }
      return std::make_pair<T, T>(sum, carry);
    }
  case MARTIN_OPTIMAL: {
    return optimalFullAdder(a, b, c, cnf);
    }
  default:
    Unreachable("Unknown fullAdder style");    
  }
  
}

typedef enum _halfAdderEncoding {
  // How many others are there...
  DEFAULT
  // \todo optimal half_adder
} HalfAdderEncoding;

template <class T>
T inline halfAdder(const HalfAdderEncoding &halfAdderStyle,
		   const T &a,
		   const T &b) {
  Assert (halfAdderStyle == DEFAULT);
  return std::make_pair<T, T>(mkXor(a, b), mkAnd(a, b));
}


struct Add2Encoding {
  FullAdderEncoding fullAdderStyle;
  typedef enum _Style {
    RIPPLE_CARRY,         // A common default
    CARRY_LOOKAHEAD,
    CARRY_SELECT
  } Style;
  Style style;
  size_t carrySelectMinimum;
  size_t carrySelectSplit;

  Add2Encoding(FullAdderEncoding fAS,
	       Add2Encoding::Style sty,
	       size_t csMin = -1,
	       size_t csSplit = -1)
  : fullAdderStyle(fAS)
  , style(sty)
  , carrySelectMinimum(csMin)
  , carrySelectSplit(csSplit)
  {}
};


template <class T>
std::vector<T> inline add2(const Add2Encoding &add2Style,
			   const std::vector<T> &a,
			   const std::vector<T> &b,
			   const T &cin,
			   prop::CnfStream* cnf) {
  Assert(a.size() == b.size());
  std::vector<T> result(a.size() + 1);

  if (a.size() > add2Style.carrySelectMinimum) {
    // carry select basically duplicates steps in the adder
    // one assuming the carry is 0 and one it is 1 and then muxes between the two 
    Unimplemented("Carry select unimplemented");
  } else {
    switch (add2Style.style) {
    case Add2Encoding::RIPPLE_CARRY :
      {
	T carry = cin;
	std::pair<T, T> tmp;
	for (int i = 0; i < a.size(); ++i) {
	  tmp = fullAdder(add2Style.fullAdderStyle, a[i], b[i], carry, cnf);
	  result[i] =  tmp.first;
	  carry = tmp.second;
	}
	result[a.size()] = carry;
      }
      break;

    case Add2Encoding::CARRY_LOOKAHEAD :
    default :
      Unimplemented("Add2 style not implemented");
    }
  }

  Assert(result.size() == a.size() + 1);
  return result;
}

template <class T>
std::vector<T> inline sub2(const Add2Encoding &add2Style,
			   const std::vector<T> &a,
			   const std::vector<T> &b,
			   prop::CnfStream* cnf) {
  Assert(a.size() == b.size());
  std::vector<T> not_b = makeNot(b);
  return add2(add2Style, a, not_b, mkTrue<T>(), cnf); 
} 
 
struct Add3Encoding {
  typedef enum _style{
    OPTIMAL_ADD3, 
    THREE_TO_TWO_THEN_ADD
  } Style;
  Style style;
  FullAdderEncoding fullAdderStyle;
  Add2Encoding add2Style;
  Add3Encoding(const Add3Encoding::Style sty,
	       const FullAdderEncoding& fAS,
	       const Add2Encoding& add2Sty)
  : style(sty)
  , fullAdderStyle(fAS)
  , add2Style(add2Sty)
  {}
};
 
template <class T>
std::vector<T> inline add3 (const Add3Encoding &add3Style,
			    const std::vector<T> &a,
			    const std::vector<T> &b,
			    const std::vector<T> &c,
			    const T &cin,
			    prop::CnfStream* cnf) {
  Assert(a.size() == b.size());
  Assert(a.size() == c.size());
  std::vector<T> result;

  switch (add3Style.style) {
  case Add3Encoding::THREE_TO_TWO_THEN_ADD :
    {
      std::vector<T> sum(a.size() + 1);
      std::vector<T> carry(a.size() + 1);

      carry[0] = cin;

      std::pair<T, T> tmp;
      for (int i = 0; i < a.size(); ++i) {
	tmp = fullAdder(add3Style.fullAdderStyle,
			a[i],
			b[i],
			c[i],
			cnf);
	sum[i] = tmp.first;
	carry[i + 1] = tmp.second;
      }

      sum[a.size()] = mkFalse<T>();

      // \todo We can add in a second carry here...
      result = add2(add3Style.add2Style, sum, carry, mkFalse<T>(), cnf);

    }
    break;
  default :
    Unimplemented("Add3 style not implemented");
  }

  Assert(result.size() == a.size() + 2);
  return result;
}


struct AccumulateEncoding {
  Add2Encoding add2Style;
  Add3Encoding add3Style;

  typedef enum _style {
    LINEAR_FORWARDS,    // Most solvers
    LINEAR_BACKWARDS,
    TREE_REDUCTION,

    ADD3_LINEAR_FORWARDS,
    ADD3_LINEAR_BACKWARDS,
    ADD3_TREE_REDUCTION
  } Style;
  Style style;
  AccumulateEncoding(const Add2Encoding& add2,
		     const Add3Encoding& add3,
		     AccumulateEncoding::Style sty)
  : add2Style(add2)
  , add3Style(add3)
  , style(sty)
  {}
};

template <class T> std::vector<T> inline accumulate (const AccumulateEncoding &accumulateStyle,
						     const std::vector<std::vector<T> > &set,
						     prop::CnfStream* cnf) {
  size_t inputCount = set.size();
  size_t inputLength = set[0].size();

  assert(inputCount != 0);
  for (unsigned i = 0; i < inputCount; ++i) {
    assert(set[i].size() == inputLength);
  }

  if (inputCount == 1) {
    return set[0];
  }

  std::vector<T> sum;

  switch (accumulateStyle.style) {
  case AccumulateEncoding::LINEAR_FORWARDS: {
    sum = set[0];
    
    for (int i = 1; i < inputCount; ++i) {
      // \todo We can sneak in lots of carrys in accumulation...
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 makeZeroExtend(set[i], sum.size() - set[i].size()),
		 mkFalse<T>(),
		 cnf);
    }
    break;  
  }

  case AccumulateEncoding::LINEAR_BACKWARDS: {
    sum = set[inputCount - 1];
    
    for (int i = inputCount - 2; i >= 0; --i) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 makeZeroExtend(set[i], sum.size() - set[i].size()),
		 mkFalse<T>(),
		 cnf);
    }
    break;
  }
  case AccumulateEncoding::TREE_REDUCTION: {
    std::vector<std::vector<T> > input = set;
    std::vector<std::vector<T> > output;

    while (input.size() >= 2) {
      for (int i = 0; i + 1< input.size(); i += 2) {
	output.push_back(add2(accumulateStyle.add2Style,
			      input[i],
			      input[i + 1],
			      mkFalse<T>(),
			      cnf));
      }
      if ((input.size() & 1) == 1) {
	output.push_back(makeZeroExtend(input[input.size() - 1], 1));
      }

      input = output;
      output.clear();
    }

    sum = input[0];
    break;
  }
  case AccumulateEncoding::ADD3_LINEAR_FORWARDS: {
    sum = set[0];

    for (int i = 1; i < inputCount; i += 2) {
      sum = add3(accumulateStyle.add3Style,
		 sum,
		 makeZeroExtend(set[i], sum.size() - set[i].size()),
		 makeZeroExtend(set[i + 1], sum.size() - set[i + 1].size()),
		 mkFalse<T>(),
		 cnf);
    }
    if ((inputCount & 1) == 0) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 makeZeroExtend(set[inputCount - 1], sum.size() - set[inputCount - 1].size()),
		 mkFalse<T>(),
		 cnf);
    }
    break;
  }
  case AccumulateEncoding::ADD3_LINEAR_BACKWARDS: {
    sum = set[inputCount - 1];
    
    for (int i = inputCount - 2; i >= 1; i -= 2) {
      sum = add3(accumulateStyle.add3Style,
		 sum,
		 makeZeroExtend(set[i], sum.size() - set[i].size()),
		 makeZeroExtend(set[i - 1], sum.size() - set[i - 1].size()),
		 mkFalse<T>(), cnf);
    }
    if ((inputCount & 1) == 0) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 makeZeroExtend(set[0], sum.size() - set[0].size()),
		 mkFalse<T>(), cnf);
    }
    break;
  }

  case AccumulateEncoding::ADD3_TREE_REDUCTION: {
    std::vector<std::vector<T> > input = set;
    std::vector<std::vector<T> > output;

    while (input.size() >= 3) {
      int i;
      for (i = 0; i + 2 < input.size(); i+=3) {
	output.push_back(add3(accumulateStyle.add3Style,
			      input[i],
			      input[i + 1],
			      input[i + 2],
			      mkFalse<T>(), cnf));
      }
      while (i < input.size()) {
	output.push_back(makeZeroExtend(input[i], 1));
	++i;
      }

      input = output;
      output.clear();
    }

    if (input.size() == 2) {
      sum = add2(accumulateStyle.add2Style,
		 input[0],
		 input[1],
		 mkFalse<T>(), cnf);
    } else {
      sum = input[0];
    }

    break;
  }

 default:
    Unimplemented("Accumulate style not implemented");
  }

  // Trim to the correct length
  size_t lengthIncrement = 0;
  while ((1 << lengthIncrement) < inputCount) {
    ++lengthIncrement;
  }

  sum.resize(inputLength + lengthIncrement);
  return sum;
}

typedef enum _recursiveMultiplicationEncoding {
  DEFAULT_REC,
  KARATSUBA
} RecursiveMultiplicationEncoding;

typedef enum _partialProductEncoding {
  CONVENTIONAL,
  BLOCK2_BY_ADDITION,
  BLOCK3_BY_ADDITION,
  BLOCK4_BY_ADDITION,
  BLOCK5_BY_ADDITION,
  BLOCK2_BY_CONSTANT_MULTIPLICATION,
  BLOCK3_BY_CONSTANT_MULTIPLICATION,
  BLOCK4_BY_CONSTANT_MULTIPLICATION,
  BLOCK5_BY_CONSTANT_MULTIPLICATION,
  OPTIMAL_2_BY_2,
  OPTIMAL_3_BY_3,
  OPTIMAL_4_BY_4,
  OPTIMAL_5_BY_5,
} PartialProductEncoding;


typedef enum _reductionEncoding {
  /** Word level reductions **/
  WORD_LEVEL,
  
  /** Bit level reductions **/
  WALLACE_TREE,               // Boolector
  DADDA_TREE,
  
  /** Carry-save reductions **/
  // \todo these

  UNARY_TO_BINARY_REDUCTION,   // Not sure about how best to use this
  CARRY_SAVE_LINEAR_REDUCTION, // Needs more parameters
  CARRY_SAVE_TREE_REDUCTION    // Needs more parameters

} ReductionEncoding;

struct MultiplyEncoding {
  RecursiveMultiplicationEncoding recursionStyle;
  PartialProductEncoding partialProductStyle;
  ReductionEncoding reductionStyle;
  AccumulateEncoding accumulateStyle;

  size_t recursiveMinimum;
  
  bool isWordLevelReduction (void) const {
    return this->reductionStyle == WORD_LEVEL;
  }

  bool isBitLevelReduction (void) const {
    return this->reductionStyle == WALLACE_TREE ||
      this->reductionStyle == DADDA_TREE;
  }

  MultiplyEncoding(const RecursiveMultiplicationEncoding& recSty,
		   const PartialProductEncoding& ppSty,
		   const ReductionEncoding& reSty,
		   const AccumulateEncoding accSty,
		   size_t recMin = -1)
  : recursionStyle(recSty)
  , partialProductStyle(ppSty)
  , reductionStyle(reSty)
  , accumulateStyle(accSty)
  , recursiveMinimum(recMin)
  {}
};


template <class T>
std::vector<T> inline multiply (const MultiplyEncoding &multiplyStyle,
				const std::vector<T> &a,
				const std::vector<T> &b,
				prop::CnfStream* cnf) {
  Assert(a.size() == b.size());

  std::vector<T> product;

  if (a.size() > multiplyStyle.recursiveMinimum) {

    size_t splitLength = a.size() / 2;  // Rounding down...
    std::vector<T> ah;
    extractBits(a, ah, splitLength + 1, a.size() - 1);
    std::vector<T> al;
    extractBits(a, al, 0, splitLength);

    std::vector<T> bh;
    extractBits(b, bh, splitLength + 1, b.size());
    std::vector<T> bl;
    extractBits(b, bl, 0, splitLength);

    switch (multiplyStyle.recursionStyle) {
    case DEFAULT : {
      std::vector<T> hh(multiply(multiplyStyle, ah, bh, cnf));
      std::vector<T> hl(multiply(multiplyStyle, ah, bl, cnf));
      std::vector<T> lh(multiply(multiplyStyle, al, bh, cnf));
      std::vector<T> ll(multiply(multiplyStyle, al, bl, cnf));

      zeroExtendBits(hh, a.size());
      zeroExtendBits(hl, a.size());
      zeroExtendBits(lh, a.size());
      zeroExtendBits(ll, a.size()); 

      // \todo : check for off-by-one errors when width is odd

      
      lshift(hh, splitLength * 2);
      
      std::vector<T> hhll = makeOr(hh, ll);
      lshift(hl, splitLength);
      lshift(lh, splitLength);
	
      product = add3(multiplyStyle.accumulateStyle.add3Style,
		     hhll,
		     hl,
		     lh,
		     mkFalse<T>(), cnf);

      break;
    }
    case KARATSUBA :
    default :
      Unimplemented("Recursion style unimplemented");
    }
  }



  if (multiplyStyle.isWordLevelReduction() ||
      multiplyStyle.isBitLevelReduction()) {

    // Generate the grid
    std::vector< std::vector<T> > grid(a.size());
    size_t blockSize;
    size_t blockEntryWidth;

    switch (multiplyStyle.partialProductStyle) {
    case CONVENTIONAL :
      blockSize = 1;
      for (int i = 0; i < b.size(); ++i) {
	grid[i] = makeAndBit(b[i], a);
      }
      break;

    case BLOCK2_BY_ADDITION : blockSize = 2; blockEntryWidth = a.size() + 1;
    case BLOCK3_BY_ADDITION : blockSize = 3; blockEntryWidth = a.size() + 2;
    case BLOCK4_BY_ADDITION : blockSize = 4; blockEntryWidth = a.size() + 3; 
    case BLOCK5_BY_ADDITION : blockSize = 5; blockEntryWidth = a.size() + 4; {
	// Build blocks
	// each block[i] represents the result of multiplying the constant i by a (IDIOT!!)
	std::vector< std::vector<T> > block(1 << blockSize);
	block[0] = makeZero<T>(blockEntryWidth);
	block[1] = a;
	block[2] = makeLShift(makeZeroExtend(a, 1), 1);
	block[3] = add2(multiplyStyle.accumulateStyle.add2Style,
			makeZeroExtend(block[1], 1),
			block[2],
			mkFalse<T>(), cnf);
	if (blockSize == 2) goto trim;

	block[4] = makeLShift(makeZeroExtend(a, 2), 2);
	block[5] = add2(multiplyStyle.accumulateStyle.add2Style,
			makeZeroExtend(block[1], 2), 
			block[4],
			mkFalse<T>(), cnf);
	block[6] = makeLShift(makeZeroExtend(block[3], 1), 1);
	block[8] = makeLShift(makeZeroExtend(a, 3), 3);
	block[7] = sub2(multiplyStyle.accumulateStyle.add2Style,
			block[8],
			block[1], cnf);

	if (blockSize == 3) goto trim;

	Unimplemented("... and so on ...");

      trim :
	// Set block width
	for (int i = 0; i < block.size(); ++i) {
	  block[i].resize(blockEntryWidth); // LSH: why do you need this?
	}

	// LSH: this does not work. You should get 4 bits from each block
	// and they can overflow in the next block
	// Select to build grid
	if (multiplyStyle.partialProductStyle == BLOCK2_BY_ADDITION) {
	  for (int i = 0; i < b.size(); i += 2) {
	    // \todo This is not optimal!
	    grid[i / 2] = makeIte(b[i + 1],
				  makeIte(b[i], block[3], block[2]),
				  makeIte(b[i], block[1], block[0]));
	  }
	  // LSH TODO!!
	  Unimplemented("Fix up for when b.size() is odd");

	} else {
	  Unimplemented("other selects work similarly");
	}

	break;
      }
    case BLOCK2_BY_CONSTANT_MULTIPLICATION : blockSize = 2; blockEntryWidth = a.size() + 1;
    case BLOCK3_BY_CONSTANT_MULTIPLICATION : blockSize = 3; blockEntryWidth = a.size() + 2;
    case BLOCK4_BY_CONSTANT_MULTIPLICATION : blockSize = 4; blockEntryWidth = a.size() + 2;
    case BLOCK5_BY_CONSTANT_MULTIPLICATION : blockSize = 5; blockEntryWidth = a.size() + 3;

      Unimplemented("Need the multiply by constant function.");
      break;

    case OPTIMAL_2_BY_2 :
    case OPTIMAL_3_BY_3 :
    case OPTIMAL_4_BY_4 :
    case OPTIMAL_5_BY_5 :
      // It is not immediately obvious how to flatten these back into a grid
    default :
      Unimplemented("Unimplemented partial product style");
    }


    // Now reduce...

    if (multiplyStyle.isWordLevelReduction()) {
      Assert(multiplyStyle.reductionStyle == WORD_LEVEL);

      for (int i = 0; i < grid.size(); ++i) {
	std::vector<T> extended_grid = makeZeroExtend(grid[i], a.size()*2 - grid[i].size());
	grid[i].swap(extended_grid);
	lshift(grid[i], i * blockSize);
      }

      // LSH why do we need a trim?
      return accumulate(multiplyStyle.accumulateStyle, grid, cnf);

    } else {
      Assert(multiplyStyle.isBitLevelReduction());

      std::vector < std::vector<T> > antiDiagonals(a.size() * 2);

      // Load anti-diagonals correctly
      for (int i = 0; i < grid.size(); ++i) {
	for (int j = 0; j < grid[i].size(); ++j) {
	  antiDiagonals[i * blockSize + j].push_back(grid[i][j]);
	}
      }

      // Reduce
      size_t maximumInDiagonal = 0;
      do {

	// One reduction round
	for (int i = antiDiagonals.size() - 1 ; i > 0; --i) {
	  if (antiDiagonals[i].size() >= 3) { // Or maybe 2 ...

	    std::vector<T> tmp = antiDiagonals[i];
	    antiDiagonals[i].clear();

	    for (int j = 0; j < tmp.size(); j += 3) {
	      // Should this be add2Style.fullAdderStyle?  Does it matter?
	      std::pair<T, T> result(fullAdder(multiplyStyle.accumulateStyle.add3Style.fullAdderStyle,
					      tmp[j],
					      tmp[j+1],
					      tmp[j+2],
					      cnf));
	      antiDiagonals[i].push_back(result.first);
	      antiDiagonals[i+1].push_back(result.second);
				    
	    }
	    Unimplemented("Half adder if the remainder is two");


	    maximumInDiagonal = (maximumInDiagonal < antiDiagonals[i+1].size()) ?
	      antiDiagonals[i+1].size() : maximumInDiagonal;
	  }

	  maximumInDiagonal = (maximumInDiagonal < antiDiagonals[i].size()) ?
	    antiDiagonals[i].size() : maximumInDiagonal;
	}

      } while (maximumInDiagonal > 3);  // Or maybe 2 ...

      Unimplemented("The final add2 or add3");

    }

  } else {
    Unimplemented("Carry-save not implemented just yet");

  }
  Unreachable();
}

 
}
}
}
 

#endif
