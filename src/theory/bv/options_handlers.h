/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for TheoryBV options
 **
 ** Custom handlers and predicates for TheoryBV options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__BV__OPTIONS_HANDLERS_H

#include "theory/bv/bitblast_mode.h"
#include "main/options.h"

namespace CVC4 {
namespace theory {
namespace bv {

inline void abcEnabledBuild(std::string option, bool value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

inline void abcEnabledBuild(std::string option, std::string value, SmtEngine* smt) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

static const std::string bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning betwen the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
";

inline BitblastMode stringToBitblastMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "lazy") {
    if (!options::bitvectorPropagate.wasSetByUser()) {
      options::bitvectorPropagate.set(true);
    }
    if (!options::bitvectorEqualitySolver.wasSetByUser()) {
      options::bitvectorEqualitySolver.set(true);
    }
    if (!options::bitvectorEqualitySlicer.wasSetByUser()) {
      if (options::incrementalSolving() ||
          options::produceModels()) {
        options::bitvectorEqualitySlicer.set(BITVECTOR_SLICER_OFF);
      } else {
        options::bitvectorEqualitySlicer.set(BITVECTOR_SLICER_AUTO);
      }
    }
    
    if (!options::bitvectorInequalitySolver.wasSetByUser()) {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser()) {
      options::bitvectorAlgebraicSolver.set(true);
    }
    return BITBLAST_MODE_LAZY;
  } else if(optarg == "eager") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Eager bit-blasting does not currently support incremental mode. \n\
                                         Try --bitblast=lazy"));
    }
    
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true); 
    }
    return BITBLAST_MODE_EAGER;
  } else if(optarg == "help") {
    puts(bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bitblast: `") +
                          optarg + "'.  Try --bitblast=help.");
  }
}

 inline CVC4::theory::bv::FullAdderEncoding stringToFullAdder(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "tseitin-naive-ab") {
    return CVC4::theory::bv::TSEITIN_NAIVE_AB_CIRCUIT;
  } else if(optarg == "tseitin-naive-ac") {
    return CVC4::theory::bv::TSEITIN_NAIVE_AC_CIRCUIT;
  } else if(optarg == "tseitin-naive-bc") {
    return CVC4::theory::bv::TSEITIN_NAIVE_BC_CIRCUIT;
  } else if(optarg == "tseitin-shared-ab") {
    return CVC4::theory::bv::TSEITIN_SHARED_AB_CIRCUIT;
  } else if(optarg == "tseitin-shared-ac") {
    return CVC4::theory::bv::TSEITIN_SHARED_AC_CIRCUIT;
  } else if(optarg == "tseitin-shared-bc") {
    return CVC4::theory::bv::TSEITIN_SHARED_BC_CIRCUIT;
  } else if(optarg == "compact-carry") {
    return CVC4::theory::bv::DANIEL_COMPACT_CARRY;
  } else if(optarg == "sum-and-carry") {
    return CVC4::theory::bv::MINISAT_SUM_AND_CARRY;
  } else if(optarg == "minisat-complete") {
    return CVC4::theory::bv::MINISAT_COMPLETE;
  } else if(optarg == "optimal") {
    return CVC4::theory::bv::MARTIN_OPTIMAL;
  } else {
    throw OptionException(std::string("unknown option for --full-adder: `") +
                          optarg );
  }
}

inline CVC4::theory::bv::Add3Encoding::Style stringToAdd3Style(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if (optarg == "optimal") {
    return CVC4::theory::bv::Add3Encoding::OPTIMAL_ADD3;
  } else if (optarg == "add2then") {
    return CVC4::theory::bv::Add3Encoding::THREE_TO_TWO_THEN_ADD;
  } else {
    throw OptionException(std::string("unknown option for --add3style: `") +
                          optarg );
  }
}

inline CVC4::theory::bv::AccumulateEncoding::Style stringToAccumulateStyle(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if (optarg == "linear-fwd") {
    return CVC4::theory::bv::AccumulateEncoding::LINEAR_FORWARDS;
  } else if (optarg == "linear-back") {
    return CVC4::theory::bv::AccumulateEncoding::LINEAR_BACKWARDS;
  } else if (optarg == "tree") {
    return CVC4::theory::bv::AccumulateEncoding::TREE_REDUCTION;
  } else if (optarg == "add3-linear-fwd") {
    return CVC4::theory::bv::AccumulateEncoding::ADD3_LINEAR_FORWARDS;
  } else if (optarg == "add3-linear-back") {
    return CVC4::theory::bv::AccumulateEncoding::ADD3_LINEAR_BACKWARDS;
  } else if (optarg == "add3-tree") {
    return CVC4::theory::bv::AccumulateEncoding::ADD3_TREE_REDUCTION;
  } else {
    throw OptionException(std::string("unknown option for --accumulate: `") +
                          optarg );
  }
}

inline CVC4::theory::bv::PartialProductEncoding stringToPartialProduct(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if (optarg == "conventional") {
    return CVC4::theory::bv::CONVENTIONAL;
  } else if (optarg == "block2") {
    return CVC4::theory::bv::BLOCK2_BY_ADDITION;
  } else if (optarg == "block3") {
    return CVC4::theory::bv::BLOCK3_BY_ADDITION;
  } else if (optarg == "block4") {
    return CVC4::theory::bv::BLOCK4_BY_ADDITION;
  } else if (optarg == "block5") {
    return CVC4::theory::bv::BLOCK5_BY_ADDITION;
  } else if (optarg == "block2const") {
    return CVC4::theory::bv::BLOCK2_BY_CONSTANT_MULTIPLICATION;
  } else if (optarg == "block3const") {
    return CVC4::theory::bv::BLOCK3_BY_CONSTANT_MULTIPLICATION;
  } else if (optarg == "block4const") {
    return CVC4::theory::bv::BLOCK4_BY_CONSTANT_MULTIPLICATION;
  } else if (optarg == "block5const") {
    return CVC4::theory::bv::BLOCK5_BY_CONSTANT_MULTIPLICATION;
  } else {
    throw OptionException(std::string("unknown option for --partial-prod: `") +
                          optarg );
  }
}

inline CVC4::theory::bv::ReductionEncoding stringToReduction(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if (optarg == "wallace") {
    return CVC4::theory::bv::WALLACE_TREE;
  } else if (optarg == "word") {
    return CVC4::theory::bv::WORD_LEVEL; 
  } else {
    throw OptionException(std::string("unknown option for --reduction: `") +
                          optarg );
  }
}

 
static const std::string bvSlicerModeHelp = "\
Bit-vector equality slicer modes supported by the --bv-eq-slicer option:\n\
\n\
auto (default)\n\
+ Turn slicer on if input has only equalities over core symbols\n\
\n\
on\n\
+ Turn slicer on\n\
\n\
off\n\
+ Turn slicer off\n\
";

inline BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {

  if(optarg == "auto") {
    return BITVECTOR_SLICER_AUTO;
  } else if(optarg == "on") {
    return BITVECTOR_SLICER_ON;
  } else if(optarg == "off") {
    return BITVECTOR_SLICER_OFF; 
  } else if(optarg == "help") {
    puts(bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-eq-slicer: `") +
                          optarg + "'.  Try --bv-eq-slicer=help.");
  }
}

inline void setBitblastAig(std::string option, bool arg, SmtEngine* smt) throw(OptionException) {
  if(arg) {
    if(options::bitblastMode.wasSetByUser()) {
      if(options::bitblastMode() != BITBLAST_MODE_EAGER) {
        throw OptionException("bitblast-aig must be used with eager bitblaster");
      }
    } else {
      options::bitblastMode.set(stringToBitblastMode("", "eager", smt));
    }
    if(!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;drw");
    }
  }
}

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__OPTIONS_HANDLERS_H */
