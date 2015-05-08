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
#include "theory/bv/bitblast_mode.h"
#include "theory/bv/generated_encodings.h"

namespace CVC4 {

namespace theory {
namespace bv {

/****
  Martin Code Sketch
 ****/


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
  Unreachable();
}

template <>
std::pair<Node, Node> inline fullAdder(const FullAdderEncoding &fullAdderStyle,
				 const Node &a,
				 const Node &b,
				 const Node &c,
				 prop::CnfStream* cnf) {
  Node sum, carry;
  
  switch(fullAdderStyle) {
  case TSEITIN_NAIVE_AB_CIRCUIT:
  case DANIEL_COMPACT_CARRY:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(a, b), c);
    return std::make_pair<Node, Node>(sum, carry);
  case TSEITIN_NAIVE_AC_CIRCUIT:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(a, c), b);
    return std::make_pair<Node, Node>(sum, carry);
  case TSEITIN_NAIVE_BC_CIRCUIT:
    carry = makeCarry(fullAdderStyle, a, b, c, cnf);
    sum = mkXor(mkXor(b, c), a);
    return std::make_pair<Node, Node>(sum, carry);
  case TSEITIN_SHARED_AB_CIRCUIT: {
    Node cross = mkXor(a, b);
    carry = mkOr(mkAnd(a,b),mkAnd(cross, c));
    sum = mkXor(cross, c);
    return std::make_pair<Node, Node>(sum, carry);
  }
  case TSEITIN_SHARED_AC_CIRCUIT: {
    Node cross = mkXor(a, c);
    carry = mkOr(mkAnd(a,c),mkAnd(cross, b));
    sum = mkXor(cross, b);
    return std::make_pair<Node, Node>(sum, carry);
  }
  case TSEITIN_SHARED_BC_CIRCUIT: {
    Node cross = mkXor(b, c);
    carry = mkOr(mkAnd(b,c),mkAnd(cross, a));
    sum = mkXor(cross, a);
    return std::make_pair<Node, Node>(sum, carry);
  }
  case MINISAT_SUM_AND_CARRY:
  case MINISAT_COMPLETE: {
      sum = mkBitVar<Node>();
      carry = mkBitVar<Node>();
      Node na = mkNot(a);
      Node nb = mkNot(b);
      Node nc = mkNot(c);
      Node ncarry = mkNot(carry);
      Node nsum = mkNot(sum);
      
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
      return std::make_pair<Node, Node>(sum, carry);
    }
  case OPTIMAL: {
    return optimalFullAdder(a, b, c, cnf);
    }
  default:
    Unreachable("Unknown fullAdder style");    
  }
  
}

 
template <class T>
std::pair<T,T> inline halfAdder(const HalfAdderEncoding &halfAdderStyle,
		   const T &a,
		   const T &b) {
  Assert (halfAdderStyle == DEFAULT);
  return std::make_pair<T, T>(mkXor(a, b), mkAnd(a, b));
}


 
template <class T>
std::vector<T> inline add2(const Add2Encoding &add2Style,
			   const std::vector<T> &a,
			   const std::vector<T> &b,
			   const T &cin,
			   prop::CnfStream* cnf) {
  Assert(a.size() == b.size());
  std::vector<T> result(a.size());

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
	// result[a.size()] = carry;
      }
      break;

    case Add2Encoding::CARRY_LOOKAHEAD :
    default :
      Unimplemented("Add2 style not implemented");
    }
  }

  Assert(result.size() == a.size());
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
      std::vector<T> sum(a.size());
      std::vector<T> carry(a.size()+1);

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

      // sum[a.size()] = mkFalse<T>();
      // T interm_carry = carry.back();
      carry.pop_back();
      result = add2(add3Style.add2Style, sum, carry, mkFalse<T>(), cnf);
      break;
    }

  case Add3Encoding::OPTIMAL_ADD3: {
    result = add3OptimalGadget(a, b, c, cnf);
    break;
  }
  default :
    Unimplemented("Add3 style not implemented");
  }

  Assert(result.size() == a.size());
  return result;
}


 
template <class T> std::vector<T> inline accumulate(const AccumulateEncoding &accumulateStyle,
						    const std::vector<std::vector<T> > &grid,
						    prop::CnfStream* cnf) {
  size_t inputCount = grid.size();
  size_t inputLength = grid[0].size();

  Assert(inputCount != 0);
  for (unsigned i = 0; i < inputCount; ++i) {
    Assert(grid[i].size() == inputLength);
  }

  if (inputCount == 1) {
    return grid[0];
  }

  std::vector<T> sum;

  switch (accumulateStyle.style) {
  case AccumulateEncoding::LINEAR_FORWARDS: {
    sum = grid[0];
    
    for (int i = 1; i < inputCount; ++i) {
      // \todo We can sneak in lots of carrys in accumulation...
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 grid[i],
		 mkFalse<T>(),
		 cnf);
      // discard carry from add2
      // sum.resize(inputLength);
    }
    break;  
  }

  case AccumulateEncoding::LINEAR_BACKWARDS: {
    sum = grid[inputCount - 1];
    
    for (int i = inputCount - 2; i >= 0; --i) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 grid[i],
		 mkFalse<T>(),
		 cnf);
    }
    break;
  }
  case AccumulateEncoding::TREE_REDUCTION: {
    std::vector<std::vector<T> > input = grid;
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
	output.push_back(input[input.size() - 1]);
      }

      input = output;
      output.clear();
    }

    sum = input[0];
    break;
  }
  case AccumulateEncoding::ADD3_LINEAR_FORWARDS: {
    sum = grid[0];

    for (int i = 1; i < inputCount - 1; i += 2) {
      sum = add3(accumulateStyle.add3Style,
		 sum,
		 grid[i], 
		 grid[i + 1],
		 mkFalse<T>(),
		 cnf);
    }
    if ((inputCount & 1) == 0) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 grid[inputCount - 1],
		 mkFalse<T>(),
		 cnf);
    }
    break;
  }
  case AccumulateEncoding::ADD3_LINEAR_BACKWARDS: {
    sum = grid[inputCount - 1];
    
    for (int i = inputCount - 2; i >= 1; i -= 2) {
      sum = add3(accumulateStyle.add3Style,
		 sum,
		 grid[i],
		 grid[i - 1],
		 mkFalse<T>(), cnf);
    }
    if ((inputCount & 1) == 0) {
      sum = add2(accumulateStyle.add2Style,
		 sum,
		 grid[0],
		 mkFalse<T>(), cnf);
    }
    break;
  }

  case AccumulateEncoding::ADD3_TREE_REDUCTION: {
    std::vector<std::vector<T> > input = grid;
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
	output.push_back(input[i]);
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
  /* size_t lengthIncrement = 0; */
  /* while ((1 << lengthIncrement) < inputCount) { */
  /*   ++lengthIncrement; */
  /* } */

  /* sum.resize(inputLength + lengthIncrement); */
  return sum;
}


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
    std::vector< std::vector<T> > grid;
    size_t blockSize;
    size_t blockEntryWidth;

    switch (multiplyStyle.partialProductStyle) {
    case CONVENTIONAL :
      blockSize = 1;
      for (int i = 0; i < b.size(); ++i) {
	grid.push_back(makeAndBit(b[i], a));
      }
      break;

    case BLOCK2_BY_ADDITION : 
    case BLOCK3_BY_ADDITION : 
    case BLOCK4_BY_ADDITION : 
    case BLOCK5_BY_ADDITION :  {
      if (multiplyStyle.partialProductStyle == BLOCK2_BY_ADDITION)
        blockSize = 2;
      if (multiplyStyle.partialProductStyle == BLOCK3_BY_ADDITION)
        blockSize = 3;
      if (multiplyStyle.partialProductStyle == BLOCK4_BY_ADDITION)
        blockSize = 4;
      if (multiplyStyle.partialProductStyle == BLOCK5_BY_ADDITION)
        blockSize = 5;
      
      // Build blocks
      // each block[i] represents the result of multiplying the constant i by a (IDIOT!!)
      Assert (a.size() >= 2);
      blockEntryWidth = a.size();
      std::vector< std::vector<T> > block(1 << blockSize);
      block[0] = makeZero<T>(blockEntryWidth);
      block[1] = a;
      block[2] = makeLShift(a, 1);
      block[3] = add2(multiplyStyle.accumulateStyle.add2Style,
                      block[1],
                      block[2],
                      mkFalse<T>(), cnf);

      if (blockSize == 2) goto trim1;
      Assert (a.size() >= 3);      

      block[4] = makeLShift(a, 2);
      block[5] = add2(multiplyStyle.accumulateStyle.add2Style,
                      block[1], 
                      block[4],
                      mkFalse<T>(), cnf);
      block[6] = makeLShift(block[3], 1);
      block[7] = sub2(multiplyStyle.accumulateStyle.add2Style,
                      makeLShift(a, 3), // 8 * a
                      block[1], cnf);

      if (blockSize == 3) goto trim1;
      Assert (a.size() >= 4);
      // TODO: maybe better combinations
      block[8] = makeLShift(a, 3);

      block[9] = add2(multiplyStyle.accumulateStyle.add2Style,
                      a, 
                      block[8],
                      mkFalse<T>(), cnf);
      block[10] = add2(multiplyStyle.accumulateStyle.add2Style,
                      block[2], 
                      block[8],
                      mkFalse<T>(), cnf);
      block[11] = add2(multiplyStyle.accumulateStyle.add2Style,
		       block[3],
		       block[8],
		       mkFalse<T>(), cnf);
      
   
      block[12] = makeLShift(block[3], 2);
      block[13] = add2(multiplyStyle.accumulateStyle.add2Style,
		       block[8],
		       block[5],
		       mkFalse<T>(), cnf);
      block[14] = sub2(multiplyStyle.accumulateStyle.add2Style,
		       makeLShift(a, 4),
		       block[2], cnf);
      block[15] = sub2(multiplyStyle.accumulateStyle.add2Style,
		       makeLShift(a, 4),
		       block[1], cnf);

      if (blockSize == 4) goto trim1; 
      Assert (a.size() >= 5);
      Unimplemented("No 5 blocking yet");
      
      trim1 :
      // Select to build grid
      if (multiplyStyle.partialProductStyle == BLOCK2_BY_ADDITION) {
        for (int i = 0; i <= b.size() -2; i += 2) {
          // \todo This is not optimal!
          grid.push_back(makeIte(b[i + 1],
                                 makeIte(b[i], block[3], block[2]),
                                 makeIte(b[i], block[1], block[0])));
        }
        
      } else if (multiplyStyle.partialProductStyle == BLOCK3_BY_ADDITION) {
        for (int i = 0; i <= b.size() -3; i += 3) {
          grid.push_back(makeIte(b[i+2],
                                 (makeIte(b[i + 1],
                                         makeIte(b[i], block[7], block[6]),
                                         makeIte(b[i], block[5], block[4]))),
                                 makeIte(b[i + 1],
                                         makeIte(b[i], block[3], block[2]),
                                         makeIte(b[i], block[1], block[0]))));
        }
      } else if (multiplyStyle.partialProductStyle == BLOCK4_BY_ADDITION) {
        for (int i = 0; i <= b.size() -4; i += 4) {
          grid.push_back(makeIte(b[i+3],
				 makeIte(b[i+2],
					 (makeIte(b[i + 1],
						  makeIte(b[i], block[15], block[14]),
						  makeIte(b[i], block[13], block[12]))),
					 makeIte(b[i + 1],
						 makeIte(b[i], block[11], block[10]),
						 makeIte(b[i], block[9], block[8]))),				 
				 makeIte(b[i+2],
					 (makeIte(b[i + 1],
						  makeIte(b[i], block[7], block[6]),
						  makeIte(b[i], block[5], block[4]))),
					 makeIte(b[i + 1],
						 makeIte(b[i], block[3], block[2]),
						 makeIte(b[i], block[1], block[0])))));
	}
      } else if (multiplyStyle.partialProductStyle == BLOCK5_BY_ADDITION) {
	Unimplemented(); 
        /* for (int i = 0; i <= b.size() -5; i += 5) { */
        /*   grid.push_back(makeIte(b[i+4], */
	/* 			 makeIte(b[i+3], */
	/* 				 makeIte(b[i+2], */
	/* 					 (makeIte(b[i + 1], */
	/* 						  makeIte(b[i], block[31], block[30]), */
	/* 						  makeIte(b[i], block[29], block[28]))), */
	/* 					 makeIte(b[i + 1], */
	/* 						 makeIte(b[i], block[27], block[26]), */
	/* 						 makeIte(b[i], block[25], block[24]))),				  */
	/* 				 makeIte(b[i+2], */
	/* 					 (makeIte(b[i + 1], */
	/* 						  makeIte(b[i], block[23], block[22]), */
	/* 						  makeIte(b[i], block[21], block[20]))), */
	/* 					 makeIte(b[i + 1], */
	/* 						 makeIte(b[i], block[19], block[18]), */
	/* 						 makeIte(b[i], block[17], block[16])))), */
	/* 			 makeIte(b[i+3], */
	/* 				 makeIte(b[i+2], */
	/* 					 (makeIte(b[i + 1], */
	/* 						  makeIte(b[i], block[15], block[14]), */
	/* 						  makeIte(b[i], block[13], block[12]))), */
	/* 					 makeIte(b[i + 1], */
	/* 						 makeIte(b[i], block[11], block[10]), */
	/* 						 makeIte(b[i], block[9], block[8]))),				  */
	/* 				 makeIte(b[i+2], */
	/* 					 (makeIte(b[i + 1], */
	/* 						  makeIte(b[i], block[7], block[6]), */
	/* 						  makeIte(b[i], block[5], block[4]))), */
	/* 					 makeIte(b[i + 1], */
	/* 						 makeIte(b[i], block[3], block[2]), */
	/* 						 makeIte(b[i], block[1], block[0])))))); */
	/* } */
      } else {
        Unimplemented("other selects work similarly");
      }
      
      break;
    }
    case BLOCK2_BY_CONSTANT_MULTIPLICATION : 
    case BLOCK3_BY_CONSTANT_MULTIPLICATION : 
    case BLOCK4_BY_CONSTANT_MULTIPLICATION : 
    case BLOCK5_BY_CONSTANT_MULTIPLICATION : {
      if (multiplyStyle.partialProductStyle == BLOCK2_BY_CONSTANT_MULTIPLICATION)
        blockSize = 2;
      if (multiplyStyle.partialProductStyle == BLOCK3_BY_CONSTANT_MULTIPLICATION)
        blockSize = 3;
      if (multiplyStyle.partialProductStyle == BLOCK4_BY_CONSTANT_MULTIPLICATION)
        blockSize = 4;
      if (multiplyStyle.partialProductStyle == BLOCK5_BY_CONSTANT_MULTIPLICATION)
        blockSize = 5;

      // FIXME add leftovers to optimalMultConst
      // Assert (a.size() % blockSize == 0);
      // Build blocks
      // each block[i] represents the result of multiplying the constant i by a (IDIOT!!)
      Assert (a.size() >= 2);
      blockEntryWidth = a.size();
      std::vector< std::vector<T> > block(1 << blockSize);
      block[0] = makeZero<T>(blockEntryWidth);
      block[1] = a;
      block[2] = makeLShift(a, 1);
      block[3] = optimalMultConst3(a, cnf);

      if (blockSize == 2) goto trim2;
      Assert (a.size() >= 3);      

      block[4] = makeLShift(a, 2);
      block[5] = optimalMultConst5(a, cnf);
      block[6] = makeLShift(block[3], 1);
      block[7] = optimalMultConst7(a, cnf);

      if (blockSize == 3) goto trim2;
      Unimplemented("Need the multiply by constant function.");

      trim2 :
      // Select to build grid
      if (multiplyStyle.partialProductStyle == BLOCK2_BY_CONSTANT_MULTIPLICATION) {
        for (int i = 0; i <= b.size() -2; i += 2) {
          // \todo This is not optimal!
          grid.push_back(makeIte(b[i + 1],
                                 makeIte(b[i], block[3], block[2]),
                                 makeIte(b[i], block[1], block[0])));
        }
        
      } else if (multiplyStyle.partialProductStyle == BLOCK3_BY_CONSTANT_MULTIPLICATION) {
        for (int i = 0; i <= b.size() -3; i += 3) {
          grid.push_back(makeIte(b[i+2],
                                 (makeIte(b[i + 1],
                                         makeIte(b[i], block[7], block[6]),
                                         makeIte(b[i], block[5], block[4]))),
                                 makeIte(b[i + 1],
                                         makeIte(b[i], block[3], block[2]),
                                         makeIte(b[i], block[1], block[0]))));
        }
      } else {
	Unimplemented("No > 3 block yet");
      }
      
      break;
    }
      
    case OPTIMAL_2_BY_2 :
    case OPTIMAL_3_BY_3 :
    case OPTIMAL_4_BY_4 :
    case OPTIMAL_5_BY_5 :
      // It is not immediately obvious how to flatten these back into a grid
    default :
      Unimplemented("Unimplemented partial product style");
    }


    // if the width is not divisible by blockSize add more rows
    unsigned rem_rows =  b.size() % blockSize;
    for (int i = rem_rows ; i > 0; --i) {
      grid.push_back(makeAndBit(b[b.size() - i], a));
    }
    
    // Now reduce...
    if (multiplyStyle.isWordLevelReduction()) {
      Assert(multiplyStyle.reductionStyle == WORD_LEVEL);

      for (int i = 0; i < grid.size() - rem_rows ; ++i) {
	lshift(grid[i], i * blockSize);
      }
      // if the width is not divisible by blockSize shift remaining rows accordingly
      for (int i =  rem_rows; i > 0 ; --i) {
        lshift(grid[grid.size() - i], b.size() - i);
      }


      // LSH try not to assert unnecessary clauses
      std::vector<T> res = accumulate(multiplyStyle.accumulateStyle, grid, cnf);
      Assert (res.size() == a.size());
      //      res.resize(a.size());
      return res;

    } else {
      Assert(multiplyStyle.isBitLevelReduction());

      std::vector < std::vector<T> > antiDiagonals(a.size());

      for (int k = 0; k < a.size()/ blockSize + 1; ++k) {
      	// each element on of the block is on its own diagonal
      	// (taking into account width not divisible by block-size)
      	for (int i = 0; i < blockSize && (k*blockSize + i < a.size()); ++i) {
      	  int num_diagonal = k*blockSize + i;
      	  // std::cout << "Diagonal " << num_diagonal << std::endl;
      	  // number of elements we are adding in the diagonal is k
      	  for (int j = 0; j <= k; ++j) {
      	    // std::cout << "  el " << j <<" " << (k-j)*blockSize + i << std::endl;
      	    antiDiagonals[num_diagonal].push_back(grid[j][(k-j)*blockSize + i]);
      	  }
      	}
      }

      
      // std::cout << "Adding remainder " << std::endl;
      int rem_rows = b.size() % blockSize - 1; // the first one is added in above loop
      int rows_offset = grid.size() - rem_rows;
      for (int i = 0; i < rem_rows; ++i) {
      	int num_diagonal = b.size() - rem_rows + i;
      	// std::cout << "Diagonal " << num_diagonal << std::endl;
      	for (int j = 0; j <= i; ++j) {
      	  int row = rows_offset + j;
      	  // std::cout << "  el " << row <<" " << j+i << std::endl;
      	  antiDiagonals[num_diagonal].push_back(grid[row][i-j]);
      	}
      }
      
      
      // Reduce
      size_t maximumInDiagonal = 0;
      do {

        maximumInDiagonal = 0;
	// One reduction round
	for (int i = 0; i < antiDiagonals.size(); ++i) {
	  if (antiDiagonals[i].size() >= 2) { // Or maybe 2 ...

	    std::vector<T> tmp;
            tmp.swap(antiDiagonals[i]);
	    antiDiagonals[i].clear();

	    for (int j = 0; j < tmp.size()-2; j += 3) {
	      // Should this be add2Style.fullAdderStyle?  Does it matter?
	      std::pair<T, T> result(fullAdder(multiplyStyle.accumulateStyle.add3Style.fullAdderStyle,
					      tmp[j],
					      tmp[j+1],
					      tmp[j+2],
					      cnf));
	      antiDiagonals[i].push_back(result.first);
              if (i < antiDiagonals.size() - 1) {
                antiDiagonals[i+1].push_back(result.second);
              }
	    }
            if (tmp.size() % 3 == 1) {
              antiDiagonals[i].push_back(tmp.back());
            } else if (tmp.size() % 3 == 2) {
	      std::pair<T, T> result(halfAdder(DEFAULT,
                                               tmp[tmp.size() - 2],
                                               tmp[tmp.size() - 1]));
	      antiDiagonals[i].push_back(result.first);
              if (i < antiDiagonals.size() - 1) {
                antiDiagonals[i+1].push_back(result.second);
              }
            }
	  }

	  maximumInDiagonal = (maximumInDiagonal < antiDiagonals[i].size()) ?
	    antiDiagonals[i].size() : maximumInDiagonal;
	}
      } while (maximumInDiagonal > 2);  // Or maybe 2 ...

      std::vector<T> final_result;
      for (int i = 0; i < antiDiagonals.size(); ++i) {
        if (antiDiagonals[i].size() == 1) {
          final_result.push_back(antiDiagonals[i][0]);
        } else if (antiDiagonals[i].size() == 2) {
          std::pair<T, T> result = halfAdder(DEFAULT,
                                             antiDiagonals[i][0],
                                             antiDiagonals[i][1]);
          final_result.push_back(result.first);
          if (i < antiDiagonals.size() - 1) {
            antiDiagonals[i+1].push_back(result.second);
          }
        } else {
          Assert (antiDiagonals[i].size() == 3);
          std::pair<T, T> result(fullAdder(multiplyStyle.accumulateStyle.add3Style.fullAdderStyle,
                                           antiDiagonals[i][0],
                                           antiDiagonals[i][1],
                                           antiDiagonals[i][2],
                                           cnf));
          final_result.push_back(result.first);
          if (i < antiDiagonals.size() - 1) {
            antiDiagonals[i+1].push_back(result.second);
          }
        }
      }
      return final_result;
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
