/*********************                                                        */
/*! \file abstract_value.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of abstract values
 **
 ** Representation of abstract values.
 **/

#include "cvc4_public.h"

#pragma once

#include <iosfwd>

#include "util/integer.h"

namespace CVC4 {

class CVC4_PUBLIC AbstractValue {
  const Integer d_index;

public:

  AbstractValue(Integer index) throw(IllegalArgumentException);

  ~AbstractValue() throw() {}

  const Integer& getIndex() const throw() {
    return d_index;
  }

  bool operator==(const AbstractValue& val) const throw() {
    return d_index == val.d_index;
  }
  bool operator!=(const AbstractValue& val) const throw() {
    return !(*this == val);
  }

  bool operator<(const AbstractValue& val) const throw() {
    return d_index < val.d_index;
  }
  bool operator<=(const AbstractValue& val) const throw() {
    return d_index <= val.d_index;
  }
  bool operator>(const AbstractValue& val) const throw() {
    return !(*this <= val);
  }
  bool operator>=(const AbstractValue& val) const throw() {
    return !(*this < val);
  }

};/* class AbstractValue */

std::ostream& operator<<(std::ostream& out, const AbstractValue& val) CVC4_PUBLIC;

/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC AbstractValueHashFunction {
  inline size_t operator()(const AbstractValue& val) const {
    return IntegerHashFunction()(val.getIndex());
  }
};/* struct AbstractValueHashFunction */

}/* CVC4 namespace */
