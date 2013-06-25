#include "theory/idl/idl_model.h"

using namespace CVC4;
using namespace theory;
using namespace idl;

IDLModel::IDLModel(context::Context* context)
: d_model(context)
, d_reason(context)
{}

Integer IDLModel::getValue(TNode var) const {
  model_value_map::const_iterator find = d_model.find(var);
  if (find != d_model.end()) {
    return (*find).second;
  } else {
    return 0;
  }
}

void IDLModel::setValue(TNode var, Integer value, IDLReason reason) {
  Assert(!reason.constraint.isNull());
  d_model[var] = value;
  d_reason[var] = reason;
}

void IDLModel::getReasonCycle(TNode var, std::vector<TNode>& reasons) {
  TNode current = var;
  do {
    Debug("theory::idl::model") << "processing: " << var << std::endl;
    Assert(d_reason.find(current) != d_reason.end());
    IDLReason reason = d_reason[current];
    Debug("theory::idl::model") << "adding reason: " << reason.constraint << std::endl;
    reasons.push_back(reason.constraint);
    current = reason.x;
  } while (current != var);
}

void IDLModel::toStream(std::ostream& out) const {
  model_value_map::const_iterator it = d_model.begin();
  model_value_map::const_iterator it_end = d_model.end();
  out << "Model[" << std::endl;
  for (; it != it_end; ++ it) {
    out << (*it).first << " -> " << (*it).second << std::endl;
  }
  out << "]";
}