/*********************                                                        */
/*! \file bitblast_mode.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitblasting modes for bit-vector solver.
 **
 ** Bitblasting modes for bit-vector solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BITBLAST_MODE_H
#define __CVC4__THEORY__BV__BITBLAST_MODE_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace bv {

/** Enumeration of bit-blasting modes */
enum BitblastMode {

  /**
   * Lazy bit-blasting that separates boolean reasoning
   * from term reasoning.
   */
  BITBLAST_MODE_LAZY,

  /**
   * Bit-blast eagerly to the bit-vector SAT solver.
   */
  BITBLAST_MODE_EAGER
};/* enum BitblastMode */

/** Enumeration of bit-vector equality slicer mode */
enum BvSlicerMode {

  /**
   * Force the slicer on. 
   */
  BITVECTOR_SLICER_ON, 

  /**
   * Slicer off. 
   */
  BITVECTOR_SLICER_OFF, 

  /**
   * Auto enable slicer if problem has only equalities.
   */
  BITVECTOR_SLICER_AUTO

};/* enum BvSlicerMode */

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

typedef enum _halfAdderEncoding {
  // How many others are there...
  DEFAULT
  // \todo optimal half_adder
} HalfAdderEncoding;

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

 MultiplyEncoding()
  : recursionStyle(DEFAULT_REC)
  , partialProductStyle(CONVENTIONAL)
  , reductionStyle(WORD_LEVEL)
  , accumulateStyle(AccumulateEncoding(Add2Encoding(TSEITIN_NAIVE_AB_CIRCUIT,
						    Add2Encoding::RIPPLE_CARRY),
				       Add3Encoding(Add3Encoding::THREE_TO_TWO_THEN_ADD,
						    TSEITIN_NAIVE_AB_CIRCUIT,
						    Add2Encoding(TSEITIN_NAIVE_AB_CIRCUIT,
								 Add2Encoding::RIPPLE_CARRY)),
				       AccumulateEncoding::LINEAR_FORWARDS))
  , recursiveMinimum(-1)
  {}

  
  static MultiplyEncoding s_current;
  static MultiplyEncoding current() { return s_current; }
  static void setCurrent(const MultiplyEncoding& enc) { s_current = enc; }
};

std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::PartialProductEncoding e);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::ReductionEncoding e);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::FullAdderEncoding fa);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::HalfAdderEncoding e);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::Add2Encoding::Style e);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::Add3Encoding::Style e);
std::ostream& operator<<(std::ostream& out, CVC4::theory::bv::AccumulateEncoding::Style e);
 

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::bv::BitblastMode mode) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out, theory::bv::BvSlicerMode mode) CVC4_PUBLIC;

 
 
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__BITBLAST_MODE_H */
