/*********************                                                        */
/*! \file multiplier_zoo.cpp
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

#include "theory/bv/multiplier_zoo.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

using namespace std;
using namespace CVC4::theory::bv::utils;

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, FullAdderEncoding fa) {
   switch(fa) {
   case TSEITIN_NAIVE_AB_CIRCUIT: out << ""; break;
   case TSEITIN_NAIVE_AC_CIRCUIT: out << "TSEITIN_NAIVE_AC_CIRCUIT"; break;
   case TSEITIN_NAIVE_BC_CIRCUIT: out << "TSEITIN_NAIVE_BC_CIRCUIT"; break;
   case TSEITIN_SHARED_AB_CIRCUIT: out << "TSEITIN_SHARED_AB_CIRCUIT"; break;
   case TSEITIN_SHARED_AC_CIRCUIT: out << "TSEITIN_SHARED_AC_CIRCUIT"; break;
   case TSEITIN_SHARED_BC_CIRCUIT: out << "TSEITIN_SHARED_BC_CIRCUIT"; break;
   case DANIEL_COMPACT_CARRY: out << "DANIEL_COMPACT_CARRY"; break;
   case MINISAT_SUM_AND_CARRY: out << "MINISAT_SUM_AND_CARRY"; break;
   case MINISAT_COMPLETE: out << "MINISAT_COMPLETE"; break;
   case MARTIN_OPTIMAL: out << "MARTIN_OPTIMA"; break;
   default:
     Unreachable();
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, HalfAdderEncoding e) {
   switch(e) {
   case DEFAULT: out << "DEFAULT"; break;
   default:
     Unreachable();
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, Add2Encoding::Style e) {
   switch(e) {
   case Add2Encoding::RIPPLE_CARRY: out << "Add2Encoding::RIPPLE_CARRY"; break;
   case Add2Encoding::CARRY_LOOKAHEAD: out << "Add2Encoding::CARRY_LOOKAHEAD"; break; 
   case Add2Encoding::CARRY_SELECT: out <<"Add2Encoding::CARRY_SELECT"; break;
   default:
     Unreachable();
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, Add3Encoding::Style e) {
   switch(e) {
   case Add3Encoding::OPTIMAL_ADD3: out << "Add3Encoding::OPTIMAL_ADD3"; break;
   case Add3Encoding::THREE_TO_TWO_THEN_ADD: out <<"Add3Encoding::THREE_TO_TWO_THEN_ADD"; break;
   default: Unreachable(); 
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, AccumulateEncoding::Style e) {
   switch(e) {
   case AccumulateEncoding::LINEAR_FORWARDS: out << "AccumulateEncoding::LINEAR_FORWARDS"; break;
   case AccumulateEncoding::LINEAR_BACKWARDS: out << "AccumulateEncoding::LINEAR_BACKWARDS"; break;
   case AccumulateEncoding::TREE_REDUCTION: out << "AccumulateEncoding::TREE_REDUCTION"; break;
   case AccumulateEncoding::ADD3_LINEAR_FORWARDS: out << "AccumulateEncoding::ADD3_LINEAR_BACKWARDS"; break;
   case AccumulateEncoding::ADD3_LINEAR_BACKWARDS: out << "AccumulateEncoding::ADD3_LINEAR_FORWARDS"; break;
   case AccumulateEncoding::ADD3_TREE_REDUCTION: out << "AccumulateEncoding::ADD3_TREE_REDUCTION"; break;
   default: Unreachable(); 
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, PartialProductEncoding e) {
   switch(e) {
   case CONVENTIONAL: out << "CONVENTIONAL"; break;
   case BLOCK2_BY_ADDITION: out << "BLOCK2_BY_ADDITION"; break;
   case BLOCK3_BY_ADDITION: out << "BLOCK3_BY_ADDITION"; break;
   case BLOCK4_BY_ADDITION: out << "BLOCK4_BY_ADDITION"; break;
   case BLOCK5_BY_ADDITION: out << "BLOCK5_BY_ADDITION"; break;
   case BLOCK2_BY_CONSTANT_MULTIPLICATION: out << "BLOCK2_BY_CONSTANT_MULTIPLICATION"; break;
   case BLOCK3_BY_CONSTANT_MULTIPLICATION: out << "BLOCK3_BY_CONSTANT_MULTIPLICATION"; break;
   case BLOCK4_BY_CONSTANT_MULTIPLICATION: out << "BLOCK4_BY_CONSTANT_MULTIPLICATION"; break;
   case BLOCK5_BY_CONSTANT_MULTIPLICATION: out << "BLOCK5_BY_CONSTANT_MULTIPLICATION"; break;
   case OPTIMAL_2_BY_2: out << "OPTIMAL_2_BY_2"; break;
   case OPTIMAL_3_BY_3: out << "OPTIMAL_3_BY_3"; break;
   case OPTIMAL_4_BY_4: out << "OPTIMAL_4_BY_4"; break;
   case OPTIMAL_5_BY_5: out << "OPTIMAL_5_BY_5"; break;
   default: Unreachable(); 
   }
   return out;
 }

 std::ostream& CVC4::theory::bv::operator<<(std::ostream& out, ReductionEncoding e) {
   switch(e) {
   case WORD_LEVEL: out << "WORD_LEVEL"; break;
   case WALLACE_TREE: out << "WALLACE_TREE"; break;
   case DADDA_TREE: out << "DADDA_TREE"; break;
   case UNARY_TO_BINARY_REDUCTION: out << "UNARY_TO_BINARY_REDUCTION"; break;
   case CARRY_SAVE_LINEAR_REDUCTION: out << "CARRY_SAVE_LINEAR_REDUCTION"; break;
   case CARRY_SAVE_TREE_REDUCTION: out << "CARRY_SAVE_TREE_REDUCTION"; break;
   default: Unreachable(); 
   }
   return out;
 }
