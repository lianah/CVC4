/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
** \verbatim
** Original author: Liana Hadarean 
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2013  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Algebraic solver.
**
** Algebraic solver.
**/

#include "theory/bv/options.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv_utils.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::prop;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool hasExpensiveBVOperators(TNode fact);

SubstitutionEx::SubstitutionEx()
  : d_substitutions()
  , d_cache()
  , d_cacheInvalid(true)
{}

void SubstitutionEx::addSubstitution(TNode from, TNode to, TNode reason) {
  Debug("bv-substitution") << "SubstitutionEx::addSubstitution: "<< from <<" => "<< to <<"\n";
  Debug("bv-substitution") << " reason "<<reason << "\n";
  
  d_cacheInvalid = true;
  Assert (from != to);
  Assert (d_substitutions.find(from) == d_substitutions.end());
  d_substitutions[from] = SubstitutionElement(to, reason);
}

Node SubstitutionEx::apply(TNode node) {
  Debug("bv-substitution") << "SubstitutionEx::apply("<< node <<")\n";
  if (d_cacheInvalid) {
    d_cache.clear();
    d_cacheInvalid = false;
  }

  SubstitutionsCache::iterator it = d_cache.find(node);

  if (it != d_cache.end()) {
    Node res = it->second.to;
    Debug("bv-substitution") << "   =>"<< res <<"\n";
    return res;
  }

  Node result = internalApply(node);
  Debug("bv-substitution") << "   =>"<< result <<"\n";
  return result;
}

Node SubstitutionEx::internalApply(TNode node) {
  if (d_substitutions.empty())
    return node;

  vector<SubstitutionStackElement> stack;
  stack.push_back(SubstitutionStackElement(node));

  while (!stack.empty()) {
    SubstitutionStackElement head = stack.back();
    stack.pop_back();
    
    TNode current = head.node;

    if (hasCache(current)) {
      continue;
    }

    // check if it has substitution
    Substitutions::const_iterator it = d_substitutions.find(current);
    if (it != d_substitutions.end()) {
      vector<Node> reasons;
      TNode to = it->second.to;
      reasons.push_back(it->second.reason);
      // check if the thing we subsituted to has substitutions
      TNode res = internalApply(to);
      // update reasons
      reasons.push_back(getReason(to));
      Node reason = utils::mkAnd(reasons);
      storeCache(current, res, reason);
      continue;
    }

    // if no children then just continue
    if(current.getNumChildren() == 0) {
      storeCache(current, current, utils::mkTrue());
      continue;
    }
    
    // children already processed 
    if (head.childrenAdded) {
      NodeBuilder<> nb(current.getKind());
      std::vector<Node> reasons;
      
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        TNode op = current.getOperator();
        Assert (hasCache(op));
        nb << getCache(op);
        reasons.push_back(getReason(op));
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        Assert (hasCache(current[i]));
        nb << getCache(current[i]);
        reasons.push_back(getReason(current[i]));
      }
      Node result = nb;
      // if the node is new apply substitutions to it
      Node subst_result = result;
      if (result != current) {
        subst_result = result!= current? internalApply(result) : result;
        reasons.push_back(getReason(result));
      }
      Node reason = utils::mkAnd(reasons);
      storeCache(current, subst_result, reason);
      continue;
    } else {
      // add children to stack
      stack.push_back(SubstitutionStackElement(current, true));
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        stack.push_back(SubstitutionStackElement(current.getOperator()));
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        stack.push_back(SubstitutionStackElement(current[i]));
      }
    }
  }

  Assert(hasCache(node));
  return getCache(node);
}

Node SubstitutionEx::explain(TNode node) const {
  if(!hasCache(node))
    return utils::mkTrue();
  
  Debug("bv-substitution") << "SubstitutionEx::explain("<< node <<")\n";
  Node res = getReason(node);
  Debug("bv-substitution") << "  with "<< res <<"\n";
  return res;
}

Node SubstitutionEx::getReason(TNode node) const {
  Assert(hasCache(node));
  SubstitutionsCache::const_iterator it = d_cache.find(node);
  return it->second.reason;
}

bool SubstitutionEx::hasCache(TNode node) const {
  return d_cache.find(node) != d_cache.end();
}

Node SubstitutionEx::getCache(TNode node) const {
  Assert (hasCache(node));
  return d_cache.find(node)->second.to;
}

void SubstitutionEx::storeCache(TNode from, TNode to, Node reason) {
  //  Debug("bv-substitution") << "SubstitutionEx::storeCache(" << from <<", " << to <<", "<< reason<<")\n"; 
  Assert (!hasCache(from));
  d_cache[from] = SubstitutionElement(to, reason);
}

AlgebraicSolver::AlgebraicSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv)
  , d_quickSolver(new BVQuickCheck("alg"))
  , d_isComplete(c, false)
  , d_isDifficult(c, false)
  , d_budget(options::bvAlgebraicBudget())
  , d_explanations()
  , d_ctx(new context::Context())
  , d_quickXplain(options::bitvectorQuickXplain() ? new QuickXPlain("alg", d_quickSolver) : NULL)
  , d_statistics()
{}

AlgebraicSolver::~AlgebraicSolver() {
  delete d_quickXplain;
  delete d_quickSolver;
  delete d_ctx;
}

bool AlgebraicSolver::check(Theory::Effort e) {
  Assert(!options::bitvectorEagerBitblast());

  if (!Theory::fullEffort(e))
    return true;

  if (!useHeuristic())
    return true;
  
  ++(d_numCalls);
  
  TimerStat::CodeTimer algebraicTimer(d_statistics.d_solveTime);
  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check (" << e << ")\n";
  ++(d_statistics.d_numCallstoCheck);

  d_explanations.clear();
  d_ids.clear(); 
  d_inputAssertions.clear(); 

  std::vector<WorklistElement> worklist;

  uint64_t original_bb_cost = 0;

  NodeSet seen_assertions;
  // Processing assertions from scratch
  for (AssertionQueue::const_iterator it = assertionsBegin(); it != assertionsEnd(); ++it) {
    Debug("bv-subtheory-algebraic") << "   " << *it << "\n";
    TNode assertion = *it;
    unsigned id = worklist.size();
    d_ids[assertion] = id; 
    worklist.push_back(WorklistElement(assertion, id));
    d_inputAssertions.insert(assertion); 
    storeExplanation(assertion);

    uint64_t assertion_size = d_quickSolver->computeAtomWeight(assertion, seen_assertions);
    Assert (original_bb_cost <= original_bb_cost + assertion_size);
    original_bb_cost+= assertion_size; 
  }

  for (unsigned i = 0; i < worklist.size(); ++i) {
    d_ids[worklist[i].node] = worklist[i].id;
  }
  
  Debug("bv-subtheory-algebraic") << "Assertions " << worklist.size() <<" : \n";

  Assert (d_explanations.size() == worklist.size()); 
  

  SubstitutionEx subst;

  // first round of substitutions
  processAssertions(worklist, subst); 

  if (!d_isDifficult.get()) {
    // skolemize all possible extracts
    ExtractSkolemizer skolemizer(d_ctx);
    skolemizer.skolemize(worklist);
    // second round of substitutions
    processAssertions(worklist, subst); 
  }


  // if(Debug.isOn("bv-algebraic-dbg")) {
  //   Debug("bv-algebraic-dbg") << "Post processAssertions2 \n";
  //   for (unsigned i = 0; i < worklist.size(); ++i) {
  //     TNode fact = worklist[i].node;
  //     unsigned id = worklist[i].id;
  //     TNode explanation = d_explanations[id];
  //     Debug("bv-algebraic-dbg") <<fact << " id= " << id <<"\n";
  //     Debug("bv-algebraic-dbg") <<"    expl: " << Rewriter::rewrite(explanation) <<"\n"; 
  //   }
  // }

  
  NodeSet subst_seen;
  uint64_t subst_bb_cost = 0;

  unsigned r = 0;
  unsigned w = 0;

  for (; r < worklist.size(); ++r) {

    TNode fact = worklist[r].node;
    unsigned id = worklist[r].id;
    
    if (Dump.isOn("bv-algebraic")) {
      Node expl = d_explanations[id];
      Node query = utils::mkNot(utils::mkNode(kind::IMPLIES, expl, fact));
      Dump("bv-algebraic") << EchoCommand("ThoeryBV::AlgebraicSolver::substitution explanation"); 
      Dump("bv-algebraic") << PushCommand(); 
      Dump("bv-algebraic") << AssertCommand(query.toExpr());
      Dump("bv-algebraic") << CheckSatCommand();
      Dump("bv-algebraic") << PopCommand(); 
    }

    if (fact.isConst() &&
        fact.getConst<bool>() == true) {
      continue;
    }

    if (fact.isConst() &&
        fact.getConst<bool>() == false) {
      // we have a conflict
      Node conflict = Rewriter::rewrite(d_explanations[id]);
      d_bv->setConflict(conflict);
      d_isComplete.set(true);
      Debug("bv-subtheory-algebraic") << " UNSAT: assertion simplfies to false with conflict: "<< conflict << "\n";
       
      if (Dump.isOn("bv-algebraic")) {
        Dump("bv-algebraic") << EchoCommand("TheoryBV::AlgebraicSolver::conflict"); 
        Dump("bv-algebraic") << PushCommand(); 
        Dump("bv-algebraic") << AssertCommand(conflict.toExpr());
        Dump("bv-algebraic") << CheckSatCommand();
        Dump("bv-algebraic") << PopCommand(); 
      }

      
      ++(d_statistics.d_numSimplifiesToFalse);
      ++(d_numSolved);
      return false;
    }

    subst_bb_cost+= d_quickSolver->computeAtomWeight(fact, subst_seen);
    worklist[w] = WorklistElement(fact, id);
    Node expl = Rewriter::rewrite(d_explanations[id]);
    storeExplanation(id, expl);
    d_ids[fact] = id;
    ++w;
  }

  worklist.resize(w);

  
  if(Debug.isOn("bv-subtheory-algebraic")) {
    Debug("bv-subtheory-algebraic") << "Assertions post-substitutions " << worklist.size() << ":\n";
    for (unsigned i = 0; i < worklist.size(); ++i) {
      Debug("bv-subtheory-algebraic") << "   " << worklist[i].node << "\n";
    }
  }

  
  double ratio = ((double)subst_bb_cost)/original_bb_cost;

  if (ratio > 0.5 ||
      !d_isDifficult.get()) {
    // give up if problem not reduced enough
    d_isComplete = false;
    return true;
  }
  
  // all facts solved to true
  if (worklist.empty()) {
    Debug("bv-subtheory-algebraic") << " SAT: everything simplifies to true.\n";
    ++(d_statistics.d_numSimplifiesToTrue);
    ++(d_numSolved);
    return true;
  }

  d_quickSolver->reset();

  d_quickSolver->push();
  std::vector<Node> facts;
  for (unsigned i = 0; i < worklist.size(); ++i) {
    facts.push_back(worklist[i].node); 
  }
  bool ok = quickCheck(facts, subst);

  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check done " << ok << ".\n";
  return ok;
}

bool AlgebraicSolver::quickCheck(std::vector<Node>& facts, SubstitutionEx& subst) {
  SatValue res = d_quickSolver->checkSat(facts, d_budget);

  if (res == SAT_VALUE_UNKNOWN) {
    d_isComplete.set(false);
    Debug("bv-subtheory-algebraic") << " Unknown.\n";
    ++(d_statistics.d_numUnknown);
    return true;
  }
  
  if (res == SAT_VALUE_TRUE) {
    Debug("bv-subtheory-algebraic") << " Sat.\n";
    ++(d_statistics.d_numSat);
    ++(d_numSolved);
    d_isComplete.set(true);
    return true;
  }

  Assert (res == SAT_VALUE_FALSE);
  Assert (d_quickSolver->inConflict());  

  Debug("bv-subtheory-algebraic") << " Unsat.\n";
  ++(d_numSolved);
  ++(d_statistics.d_numUnsat);

  
  Node conflict = d_quickSolver->getConflict();
  Debug("bv-subtheory-algebraic") << " Conflict: " << conflict << "\n";

  // singleton conflict
  if (conflict.getKind() != kind::AND) {
    Assert (d_ids.find(conflict) != d_ids.end());
    unsigned id = d_ids[conflict]; 
    Assert (id < d_explanations.size()); 
    Node theory_confl = d_explanations[id];
    d_bv->setConflict(theory_confl);
    return false;
  }

  Assert (conflict.getKind() == kind::AND);
  if (options::bitvectorQuickXplain()) {
    d_quickSolver->popToZero();
    Debug("bv-quick-xplain") << "AlgebraicSolver::quickCheck original conflict size " << conflict.getNumChildren() << "\n";
    conflict = d_quickXplain->minimizeConflict(conflict);
    Debug("bv-quick-xplain") << "AlgebraicSolver::quickCheck minimized conflict size " << conflict.getNumChildren() << "\n";
  }
  
  vector<TNode> theory_confl;
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode c = conflict[i];

    Assert (d_ids.find(c) != d_ids.end()); 
    unsigned c_id = d_ids[c];
    Assert (c_id < d_explanations.size());
    TNode c_expl = d_explanations[c_id];
    theory_confl.push_back(c_expl);
  }
  
  Node confl = Rewriter::rewrite(utils::mkAnd(theory_confl));

  Debug("bv-subtheory-algebraic") << " Out Conflict: " << confl << "\n";
  setConflict(confl);
  return false;
}

void AlgebraicSolver::setConflict(TNode conflict) {
  Node final_conflict = conflict;
  if (options::bitvectorQuickXplain() &&
      conflict.getKind() == kind::AND &&
      conflict.getNumChildren() > 4) {
    final_conflict = d_quickXplain->minimizeConflict(conflict);
  }
  d_bv->setConflict(final_conflict);
}

bool AlgebraicSolver::solve(TNode fact, TNode reason, SubstitutionEx& subst) {
  if (fact.getKind() != kind::EQUAL) return false;

  TNode left = fact[0];
  TNode right = fact[1];

  
  if (left.isVar() && !right.hasSubterm(left)) {
    subst.addSubstitution(left, right, reason);
    return true;
  }
  if (right.isVar() && !left.hasSubterm(right)) {
    subst.addSubstitution(right, left, reason);
    return true;
  }

  // xor simplification
  if (right.getKind() == kind::BITVECTOR_XOR &&
      left.getKind() == kind::BITVECTOR_XOR) {
    TNode var = left[0];
    if (!var.getMetaKind() == kind::metakind::VARIABLE)
      return false; 

    // simplify xor with same variable on both sides
    if (right.hasSubterm(var)) {
      std::vector<Node> right_children;
      for (unsigned i = 0; i < right.getNumChildren(); ++i) {
        if (right[i] != var)
          right_children.push_back(right[i]); 
      }
      Assert (right_children.size());
      Node new_right = right_children.size() > 1 ? utils::mkNode(kind::BITVECTOR_XOR, right_children)
                                                 : right_children[0];
      std::vector<Node> left_children;
      for (unsigned i = 1; i < left.getNumChildren(); ++i) {
        left_children.push_back(left[i]);
      }
      Node new_left = left_children.size() > 1 ? utils::mkNode(kind::BITVECTOR_XOR, left_children)
                                               : left_children[0];
      Node new_fact = utils::mkNode(kind::EQUAL, new_left, new_right);
      subst.addSubstitution(fact, new_fact, reason);
      return true;
    }
    
    NodeBuilder<> nb(kind::BITVECTOR_XOR);
    for (unsigned i = 1; i < left.getNumChildren(); ++i) {
      nb << left[i];
    }
    Node inverse = left.getNumChildren() == 2? (Node)left[1] : (Node)nb;
    Node new_right = utils::mkNode(kind::BITVECTOR_XOR, right, inverse);
    subst.addSubstitution(var, new_right, reason);

    if (Dump.isOn("bv-algebraic")) {
      Node query = utils::mkNot(utils::mkNode(kind::IFF, fact, utils::mkNode(kind::EQUAL, var, new_right)));
      Dump("bv-algebraic") << EchoCommand("ThoeryBV::AlgebraicSolver::substitution explanation"); 
      Dump("bv-algebraic") << PushCommand(); 
      Dump("bv-algebraic") << AssertCommand(query.toExpr());
      Dump("bv-algebraic") << CheckSatCommand();
      Dump("bv-algebraic") << PopCommand(); 
    }

    
    return true;
  }

  // (a xor t = a) <=> (t = 0)
  if (left.getKind() == kind::BITVECTOR_XOR &&
      right.getMetaKind() == kind::metakind::VARIABLE &&
      left.hasSubterm(right)) {
    TNode var = right;
    Node new_left = utils::mkNode(kind::BITVECTOR_XOR, var, left);
    Node zero = utils::mkConst(utils::getSize(var), 0u);
    Node new_fact = utils::mkNode(kind::EQUAL, zero, new_left);
    subst.addSubstitution(fact, new_fact, reason);
    return true; 
  }
  
  if (right.getKind() == kind::BITVECTOR_XOR &&
      left.getMetaKind() == kind::metakind::VARIABLE &&
      right.hasSubterm(left)) {
    TNode var = left;
    Node new_right = utils::mkNode(kind::BITVECTOR_XOR, var, right);
    Node zero = utils::mkConst(utils::getSize(var), 0u);
    Node new_fact = utils::mkNode(kind::EQUAL, zero, new_right);
    subst.addSubstitution(fact, new_fact, reason);
    return true; 
  }

  // (a xor b = 0) <=> (a = b)
  if (left.getKind() == kind::BITVECTOR_XOR &&
      left.getNumChildren() == 2 &&
      right.getKind() == kind::CONST_BITVECTOR &&
      right.getConst<BitVector>() == BitVector(utils::getSize(left), 0u)) {
    Node new_fact = utils::mkNode(kind::EQUAL, left[0], left[1]);
    subst.addSubstitution(fact, new_fact, reason);
    return true; 
  }
  

  return false;
} 

bool AlgebraicSolver::isSubstitutableIn(TNode node, TNode in) {
  if (node.getMetaKind() == kind::metakind::VARIABLE &&
      !in.hasSubterm(node))
    return true;
  return false; 
}

void AlgebraicSolver::processAssertions(std::vector<WorklistElement>& worklist, SubstitutionEx& subst) {
  bool changed = true;
  while(changed) {
    changed = false;
    for (unsigned i = 0; i < worklist.size(); ++i) {
      // apply current substitutions
      Node current = subst.apply(worklist[i].node);
      unsigned current_id = worklist[i].id;
      Node subst_expl = subst.explain(worklist[i].node);
      worklist[i] = WorklistElement(Rewriter::rewrite(current), current_id);
      // explanation for this assertion
      Node old_expl = d_explanations[current_id];
      Node new_expl = subst_expl == utils::mkTrue() ? old_expl
        : utils::mkAnd(subst_expl, old_expl);
      storeExplanation(current_id, new_expl);
      
      // use the new substitution to solve
      if(solve(worklist[i].node, new_expl, subst)) {
        changed = true;
      }
    }

    // check for concat slicings
    for (unsigned i = 0; i < worklist.size(); ++i) {
      TNode fact = worklist[i].node;
      unsigned current_id = worklist[i].id;
      
      if (fact.getKind() != kind::EQUAL)
        continue;

      TNode left = fact[0];
      TNode right = fact[1];
      if (left.getKind() != kind::BITVECTOR_CONCAT ||
          right.getKind() != kind::BITVECTOR_CONCAT ||
          left.getNumChildren() != right.getNumChildren())
        continue;

      bool can_slice = true;
      for (unsigned j = 0; j < left.getNumChildren(); ++j) {
        if (utils::getSize(left[j]) != utils::getSize(right[j]))
          can_slice = false;
      }
      
      if (!can_slice)
        continue; 
      
      for (unsigned j = 0; j < left.getNumChildren(); ++j) {
        Node eq_j = utils::mkNode(kind::EQUAL, left[j], right[j]);
        unsigned id = d_explanations.size();
        TNode expl = d_explanations[current_id];
        storeExplanation(expl);
        worklist.push_back(WorklistElement(eq_j, id));
        d_ids[eq_j] = id; 
      }
      worklist[i] = WorklistElement(utils::mkTrue(), worklist[i].id);
      changed = true;
    }
    Assert (d_explanations.size() == worklist.size()); 
  }
}

void AlgebraicSolver::storeExplanation(unsigned id, TNode explanation) {
  Assert (checkExplanation(explanation)); 
  d_explanations[id] = explanation;
}

void AlgebraicSolver::storeExplanation(TNode explanation) {
  Assert (checkExplanation(explanation));
  d_explanations.push_back(explanation); 
}

bool AlgebraicSolver::checkExplanation(TNode explanation) {
  explanation = Rewriter::rewrite(explanation);
  if (explanation.getKind() != kind::AND) {
    return d_inputAssertions.find(explanation) != d_inputAssertions.end();
  }
  for (unsigned i = 0; i < explanation.getNumChildren(); ++i) {
    if (d_inputAssertions.find(explanation[i]) == d_inputAssertions.end()) {
      return false;
    }
  }
  return true; 
}


bool AlgebraicSolver::isComplete() {
  return d_isComplete.get(); 
}

bool AlgebraicSolver::useHeuristic() {
  if (d_numCalls == 0)
    return true;
  
  double success_rate = d_numSolved/d_numCalls;
  d_statistics.d_useHeuristic.setData(success_rate);
  return success_rate > 0.8;
}


void AlgebraicSolver::assertFact(TNode fact) {
  d_assertionQueue.push_back(fact);
  if (!d_isDifficult.get()) {
    d_isDifficult.set(hasExpensiveBVOperators(fact));
  }
}


AlgebraicSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::AlgebraicSolver::NumCallsToCheck", 0)
  , d_numSimplifiesToTrue("theory::bv::AlgebraicSolver::NumSimplifiesToTrue", 0)
  , d_numSimplifiesToFalse("theory::bv::AlgebraicSolver::NumSimplifiesToFalse", 0)
  , d_numUnsat("theory::bv::AlgebraicSolver::NumUnsat", 0)
  , d_numSat("theory::bv::AlgebraicSolver::NumSat", 0)
  , d_numUnknown("theory::bv::AlgebraicSolver::NumUnknown", 0)
  , d_solveTime("theory::bv::AlgebraicSolver::SolveTime")
  , d_useHeuristic("theory::bv::AlgebraicSolver::UseHeuristic", 0.2)
{
  StatisticsRegistry::registerStat(&d_numCallstoCheck);
  StatisticsRegistry::registerStat(&d_numSimplifiesToTrue);
  StatisticsRegistry::registerStat(&d_numSimplifiesToFalse);
  StatisticsRegistry::registerStat(&d_numUnsat);
  StatisticsRegistry::registerStat(&d_numSat);
  StatisticsRegistry::registerStat(&d_numUnknown);
  StatisticsRegistry::registerStat(&d_solveTime);
  StatisticsRegistry::registerStat(&d_useHeuristic);
}

AlgebraicSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numCallstoCheck);
  StatisticsRegistry::unregisterStat(&d_numSimplifiesToTrue);
  StatisticsRegistry::unregisterStat(&d_numSimplifiesToFalse);
  StatisticsRegistry::unregisterStat(&d_numUnsat);
  StatisticsRegistry::unregisterStat(&d_numSat);
  StatisticsRegistry::unregisterStat(&d_numUnknown);
  StatisticsRegistry::unregisterStat(&d_solveTime);
  StatisticsRegistry::unregisterStat(&d_useHeuristic);
}

bool hasExpensiveBVOperatorsRec(TNode fact, TNodeSet& seen) {
  if (fact.getKind() == kind::BITVECTOR_MULT ||
      fact.getKind() == kind::BITVECTOR_UDIV_TOTAL ||
      fact.getKind() == kind::BITVECTOR_UREM_TOTAL) {
    return true;
  }

  if (seen.find(fact) != seen.end())
    return false;
  
  if (fact.getNumChildren() == 0)
    return false;
  
  for (unsigned i = 0; i < fact.getNumChildren(); ++i) {
    bool difficult = hasExpensiveBVOperatorsRec(fact[i], seen);
    if (difficult)
      return true;
  }
  seen.insert(fact);
  return false;
}

bool hasExpensiveBVOperators(TNode fact) {
  TNodeSet seen;
  return hasExpensiveBVOperatorsRec(fact, seen);
}

void ExtractSkolemizer::skolemize(std::vector<WorklistElement>& facts) {
  TNodeSet seen;
  for (unsigned i = 0; i < facts.size(); ++i) {
    TNode current = facts[i].node;
    collectExtracts(current, seen); 
  }

  for (VarExtractMap::iterator it = d_varToExtract.begin(); it != d_varToExtract.end(); ++it) {
    ExtractList& el = it->second;
    TNode var = it->first; 
    if (el.overlap)
      continue;

    std::vector<unsigned> indices;
    for (unsigned i = 0; i < el.extracts.size(); ++i) {
      unsigned high = el.extracts[i].high;
      unsigned low = el.extracts[i].low;
      indices.push_back(high);
      indices.push_back(low);
    }
    std::sort(indices.begin(), indices.end());

    Assert (indices.size() % 2 == 0); 
    
    std::vector<Node> decomp;
    if (indices[0] != 0) {
      Node first = utils::mkExtract(var, indices[0] -1, 0);
      decomp.push_back(first); 
    }
    
    for (unsigned i = 0; i < indices.size() - 1; i+=2) {
      unsigned low = indices[i];
      unsigned high = indices[i+1];
      TNode extract1 = utils::mkExtract(var, high, low);
      decomp.push_back(extract1); 
      if (i + 2 < indices.size() &&
          high + 1 < indices[i+2]) {
        TNode extract2 = utils::mkExtract(var, indices[i+2] - 1, high+1);
        decomp.push_back(extract2); 
      }
    }
    
    if (indices.back() != utils::getSize(var) - 1) {
      Node last = utils::mkExtract(var, utils::getSize(var) - 1, indices.back()+1);
      decomp.push_back(last); 
    }

    NodeBuilder<> concat_nb(kind::BITVECTOR_CONCAT);
    for (int i = decomp.size() - 1; i >= 0; --i) {
      Node skolem = mkSkolem(decomp[i]);
      storeSkolem(decomp[i], skolem);
      concat_nb << skolem;
    }

    Node skolemized_var = concat_nb;
    
    Assert (utils::getSize(skolemized_var) == utils::getSize(var));
    storeSkolem(var, skolemized_var);
  }

  for (unsigned i = 0; i < facts.size(); ++i) {
    facts[i] = WorklistElement(skolemize(facts[i].node), facts[i].id);
  }
}

Node ExtractSkolemizer::mkSkolem(Node node) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getMetaKind() == kind::metakind::VARIABLE);
  Assert (!d_skolemSubst.hasSubstitution(node));
  return utils::mkVar(utils::getSize(node)); 
}

void ExtractSkolemizer::unSkolemize(std::vector<WorklistElement>& facts) {
  for (unsigned i = 0; i < facts.size(); ++i) {
    facts[i] = WorklistElement(unSkolemize(facts[i].node), facts[i].id);
  }
}

void ExtractSkolemizer::storeSkolem(TNode node, TNode skolem) {
  d_skolemSubst.addSubstitution(node, skolem);
  d_skolemSubstRev.addSubstitution(skolem, node);
}

Node ExtractSkolemizer::unSkolemize(TNode node) {
  return d_skolemSubstRev.apply(node); 
}

Node ExtractSkolemizer::skolemize(TNode node) {
  return d_skolemSubst.apply(node); 
}


void ExtractSkolemizer::ExtractList::addExtract(Extract& e) {
  if (overlap)
    return;

  for (unsigned i = 0; i < extracts.size(); ++i) {
    unsigned l = extracts[i].low;
    unsigned h = extracts[i].high;
    Assert (l <= h && e.low <= e.high);
    if (l == e.low && h == e.high)
      continue;
    
    if (h < e.low)
      continue;
    if (e.high < l)
      continue;
    overlap = true;
    return;
  }
  extracts.push_back(e);
}

void ExtractSkolemizer::storeExtract(TNode var, unsigned high, unsigned low) {
  Assert (var.getMetaKind() == kind::metakind::VARIABLE);
  if (d_varToExtract.find(var) == d_varToExtract.end()) {
    d_varToExtract[var] = ExtractList();
  }
  VarExtractMap::iterator it = d_varToExtract.find(var);
  ExtractList& el = it->second;
  if (el.overlap)
    return;

  Extract e(high, low);
  el.addExtract(e);
}
  
void ExtractSkolemizer::collectExtracts(TNode node, TNodeSet& seen) {
  if (seen.find(node) != seen.end()) {
    return;
  }
  
  if (node.getKind() == kind::BITVECTOR_EXTRACT &&
      node[0].getMetaKind() == kind::metakind::VARIABLE) {
    unsigned high = utils::getExtractHigh(node);
    unsigned low = utils::getExtractLow(node);
    TNode var = node[0];
    storeExtract(var, high, low);
    seen.insert(node);
    return;
  }

  if (node.getNumChildren() == 0)
    return;

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectExtracts(node[i], seen);
  }
  seen.insert(node); 
}

ExtractSkolemizer::ExtractSkolemizer(context::Context* c)
  : d_varToExtract()
  , d_skolemSubst(c)
  , d_skolemSubstRev(c)
{}
