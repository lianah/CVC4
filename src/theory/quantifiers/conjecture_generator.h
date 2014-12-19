/*********************                                                        */
/*! \file conjecture_generator.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief conjecture generator class
 **/

#include "cvc4_public.h"

#ifndef CONJECTURE_GENERATOR_H
#define CONJECTURE_GENERATOR_H

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermArgTrie;

//algorithm for computing candidate subgoals

class ConjectureGenerator;

// operator independent index of arguments for an EQC
class OpArgIndex
{
public:
  std::map< TNode, OpArgIndex > d_child;
  std::vector< TNode > d_ops;
  std::vector< TNode > d_op_terms;
  void addTerm( ConjectureGenerator * s, TNode n, unsigned index = 0 );
  Node getGroundTerm( ConjectureGenerator * s, std::vector< TNode >& args );
  void getGroundTerms( ConjectureGenerator * s, std::vector< TNode >& terms );
};

class PatternTypIndex
{
public:
  std::vector< TNode > d_terms;
  std::map< TypeNode, std::map< unsigned, PatternTypIndex > > d_children;
  void clear() {
    d_terms.clear();
    d_children.clear();
  }
};

class SubstitutionIndex
{
public:
  //current variable, or ground EQC if d_children.empty()
  TNode d_var;
  std::map< TNode, SubstitutionIndex > d_children;
  //add substitution
  void addSubstitution( TNode eqc, std::vector< TNode >& vars, std::vector< TNode >& terms, unsigned i = 0 );
  //notify substitutions
  bool notifySubstitutions( ConjectureGenerator * s, std::map< TNode, TNode >& subs, TNode rhs, unsigned numVars, unsigned i = 0 );
};

class TermGenerator
{
public:
  TermGenerator(){}
  TypeNode d_typ;
  unsigned d_id;
  //1 : consider as unique variable
  //2 : consider equal to another variable
  //5 : consider a function application
  unsigned d_status;
  int d_status_num;
  //for function applications: the number of children you have built
  int d_status_child_num;
  //children (pointers to TermGenerators)
  std::vector< unsigned > d_children;
  //possible eqc for this term
  //std::vector< TNode > d_eqc;

  //match status
  unsigned d_match_status;
  int d_match_status_child_num;
  //match mode
  //1 : different variables must have different matches
  //2 : variables must map to ground terms
  //3 : both 1 and 2
  unsigned d_match_mode;
  //children
  std::vector< std::map< TNode, TermArgTrie >::iterator > d_match_children;
  std::vector< std::map< TNode, TermArgTrie >::iterator > d_match_children_end;

  void reset( ConjectureGenerator * s, TypeNode tn );
  bool getNextTerm( ConjectureGenerator * s, unsigned depth );
  void resetMatching( ConjectureGenerator * s, TNode eqc, unsigned mode );
  bool getNextMatch( ConjectureGenerator * s, TNode eqc, std::map< TypeNode, std::map< unsigned, TNode > >& subs, std::map< TNode, bool >& rev_subs );

  unsigned getDepth( ConjectureGenerator * s );
  unsigned getGeneralizationDepth( ConjectureGenerator * s );
  Node getTerm( ConjectureGenerator * s );

  void debugPrint( ConjectureGenerator * s, const char * c, const char * cd );
};


class TheoremIndex
{
private:
  void addTheorem( std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs );
  void addTheoremNode( TNode curr, std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs );
  void getEquivalentTerms( std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                           std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                           std::vector< Node >& terms );
  void getEquivalentTermsNode( Node curr, std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                               std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                               std::vector< Node >& terms );
public:
  TNode d_var;
  std::map< TNode, TheoremIndex > d_children;
  std::vector< Node > d_terms;

  void addTheorem( TNode lhs, TNode rhs ) {
    std::vector< TNode > v;
    std::vector< unsigned > a;
    addTheoremNode( lhs, v, a, rhs );
  }
  void getEquivalentTerms( TNode n, std::vector< Node >& terms ) {
    std::vector< TNode > nv;
    std::vector< unsigned > na;
    std::map< TNode, TNode > smap;
    std::vector< TNode > vars;
    std::vector< TNode > subs;
    getEquivalentTermsNode( n, nv, na, smap, vars, subs, terms );
  }
  void clear(){
    d_var = Node::null();
    d_children.clear();
    d_terms.clear();
  }
  void debugPrint( const char * c, unsigned ind = 0 );
};



class ConjectureGenerator : public QuantifiersModule
{
  friend class OpArgIndex;
  friend class PatGen;
  friend class PatternGenEqc;
  friend class PatternGen;
  friend class SubsEqcIndex;
  friend class TermGenerator;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
//this class maintains a congruence closure for *universal* facts
private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    ConjectureGenerator& d_sg;
  public:
    NotifyClass(ConjectureGenerator& sg): d_sg(sg) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) { return true; }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) { return true; }
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) { return true; }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) { }
    void eqNotifyNewClass(TNode t) { d_sg.eqNotifyNewClass(t); }
    void eqNotifyPreMerge(TNode t1, TNode t2) { d_sg.eqNotifyPreMerge(t1, t2); }
    void eqNotifyPostMerge(TNode t1, TNode t2) { d_sg.eqNotifyPostMerge(t1, t2); }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {d_sg.eqNotifyDisequal(t1, t2, reason); }
  };/* class ConjectureGenerator::NotifyClass */
  /** The notify class */
  NotifyClass d_notify;
  class EqcInfo{
  public:
    EqcInfo( context::Context* c );
    //representative
    context::CDO< Node > d_rep;
  };
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );
  /** (universal) equaltity engine */
  eq::EqualityEngine d_uequalityEngine;
  /** pending adds */
  std::vector< Node > d_upendingAdds;
  /** relevant terms */
  std::map< Node, bool > d_urelevant_terms;
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** add pending universal terms, merge equivalence classes */
  void doPendingAddUniversalTerms();
  /** are universal equal */
  bool areUniversalEqual( TNode n1, TNode n2 );
  /** are universal disequal */
  bool areUniversalDisequal( TNode n1, TNode n2 );
  /** get universal representative */
  TNode getUniversalRepresentative( TNode n, bool add = false );
  /** set relevant */
  void setUniversalRelevant( TNode n );
  /** ordering for universal terms */
  bool isUniversalLessThan( TNode rt1, TNode rt2 );
  
  /** the nodes we have reported as canonical representative */
  std::vector< TNode > d_ue_canon;
  /** is reported canon */
  bool isReportedCanon( TNode n );
  /** mark that term has been reported as canonical rep */
  void markReportedCanon( TNode n );
  
private:  //information regarding the conjectures
  /** list of all conjectures */
  std::vector< Node > d_conjectures;
  /** list of all waiting conjectures */
  std::vector< Node > d_waiting_conjectures;
  /** map of equality conjectures */
  std::map< Node, std::vector< Node > > d_eq_conjectures;
  /** currently existing conjectures in equality engine */
  BoolMap d_ee_conjectures;
  /** conjecture index */
  TheoremIndex d_thm_index;
  /** the relevant equivalence classes based on the conjectures */
  std::vector< TNode > d_relevant_eqc[2];
private:  //information regarding the signature we are enumerating conjectures for
  //all functions
  std::vector< TNode > d_funcs;
  //functions per type
  std::map< TypeNode, std::vector< TNode > > d_typ_funcs;
  //function to kind map
  std::map< TNode, Kind > d_func_kind;
  //type of each argument of the function
  std::map< TNode, std::vector< TypeNode > > d_func_args;
  //free variables
  std::map< TypeNode, std::vector< Node > > d_free_var;
  //map from free variable to FV#
  std::map< TNode, unsigned > d_free_var_num;
  // get canonical free variable #i of type tn
  Node getFreeVar( TypeNode tn, unsigned i );
  // get maximum free variable numbers
  void getMaxFreeVarNum( TNode n, std::map< TypeNode, unsigned >& mvn );
  // get canonical term, return null if it contains a term apart from handled signature
  Node getCanonicalTerm( TNode n, std::map< TypeNode, unsigned >& var_count, std::map< TNode, TNode >& subs );
private:  //information regarding the terms
  //relevant patterns (the LHS's)
  std::map< TypeNode, std::vector< Node > > d_rel_patterns;
  //total number of unique variables
  std::map< TNode, unsigned > d_rel_pattern_var_sum;
  //by types
  PatternTypIndex d_rel_pattern_typ_index;
  // substitution to ground EQC index
  std::map< TNode, SubstitutionIndex > d_rel_pattern_subs_index;
  //patterns (the RHS's)
  std::map< TypeNode, std::vector< Node > > d_patterns;
  //patterns to # variables per type
  std::map< TNode, std::map< TypeNode, unsigned > > d_pattern_var_id;
  // # duplicated variables
  std::map< TNode, unsigned > d_pattern_var_duplicate;
  // is normal pattern?  (variables allocated in canonical way left to right)
  std::map< TNode, bool > d_pattern_is_normal;
  // patterns to a count of # operators (variables and functions)
  std::map< TNode, std::map< TNode, unsigned > > d_pattern_fun_id;
  // term size
  std::map< TNode, unsigned > d_pattern_fun_sum;
  // collect functions
  unsigned collectFunctions( TNode opat, TNode pat, std::map< TNode, unsigned >& funcs,
                             std::map< TypeNode, unsigned >& mnvn, std::map< TypeNode, unsigned >& mxvn );
  // add pattern
  void registerPattern( Node pat, TypeNode tpat );
private: //for debugging
  unsigned d_rel_term_count;
  std::map< TNode, unsigned > d_em;
public:  //environment for term enumeration
  //the current number of enumerated variables per type
  std::map< TypeNode, unsigned > d_var_id;
  //the limit of number of variables per type to enumerate
  std::map< TypeNode, unsigned > d_var_limit;
  //the functions we can currently generate
  std::map< TypeNode, std::vector< TNode > > d_typ_tg_funcs;
  //the equivalence classes (if applicable) that match the currently generated term
  bool d_use_ccand_eqc;
  std::vector< std::vector< TNode > > d_ccand_eqc[2];
  //the term generation objects
  unsigned d_tg_id;
  std::map< unsigned, TermGenerator > d_tg_alloc;
  unsigned d_tg_gdepth;
  int d_tg_gdepth_limit;
  //std::vector< std::vector< unsigned > > d_var_eq_tg;
  //access functions
  unsigned getNumTgVars( TypeNode tn );
  bool allowVar( TypeNode tn );
  void addVar( TypeNode tn );
  void removeVar( TypeNode tn );
  unsigned getNumTgFuncs( TypeNode tn );
  TNode getTgFunc( TypeNode tn, unsigned i );
  bool considerCurrentTerm();
  bool considerTermCanon( unsigned tg_id );
  void changeContext( bool add );
public:  //for generalization lattice
  //id of maximal nodes
  std::map< TypeNode, std::vector< TNode > > d_gen_lat_maximal;
  //generalization lattice
  std::map< TNode, std::vector< TNode > > d_gen_lat_child;
  std::map< TNode, std::vector< TNode > > d_gen_lat_parent;
  //generalization depth
  std::map< TNode, int > d_gen_depth;
  //generalizations
  bool isGeneralization( TNode patg, TNode pat ) {
    std::map< TNode, TNode > subs;
    return isGeneralization( patg, pat, subs );
  }
  bool isGeneralization( TNode patg, TNode pat, std::map< TNode, TNode >& subs );
  void addGeneralizationsOf( TNode pat, std::map< TNode, bool >& patProc );
  
  //from generalization depth to relevant patterns
  std::map< TypeNode, std::map< unsigned, std::vector< TNode > > > d_rel_patterns_at_depth;
  
  
public:  //for property enumeration
  //conjectures to process at a particular depth
  std::map< unsigned, std::vector< unsigned > > d_cconj_at_depth;
  //RHS, LHS
  std::vector< TNode > d_cconj[2];
  // RHS paired
  std::map< TNode, std::vector< TNode > > d_cconj_rhs_paired;
  //add candidate conjecture
  void addCandidateConjecture( TNode lhs, TNode rhs, unsigned depth );
  //process candidate conjecture at depth
  void processCandidateConjecture( unsigned cid, unsigned depth );
  //whether it should be considered
  bool considerCandidateConjecture( TNode lhs, TNode rhs );
  //notified of a substitution
  bool notifySubstitution( TNode glhs, std::map< TNode, TNode >& subs, TNode rhs );
  //confirmation count
  unsigned d_subs_confirmCount;
  //individual witnesses (for range)
  std::vector< TNode > d_subs_confirmWitnessRange;
  //individual witnesses (for domain)
  std::map< TNode, std::vector< TNode > > d_subs_confirmWitnessDomain;
public:  //for ground equivalence classes
  eq::EqualityEngine * getEqualityEngine();
  bool areDisequal( TNode n1, TNode n2 );
  bool areEqual( TNode n1, TNode n2 );
  TNode getRepresentative( TNode n );
  TermDb * getTermDatabase();
private:  //information about ground equivalence classes
  TNode d_bool_eqc[2];
  std::map< TNode, Node > d_ground_eqc_map;
  std::vector< TNode > d_ground_terms;
  //operator independent term index
  std::map< TNode, OpArgIndex > d_op_arg_index;
  //is handled term
  bool isHandledTerm( TNode n );
  Node getGroundEqc( TNode r );
  bool isGroundEqc( TNode r );
  bool isGroundTerm( TNode n );
  // count of full effort checks
  unsigned d_fullEffortCount;
public:
  ConjectureGenerator( QuantifiersEngine * qe, context::Context* c );
  /* needs check */
  bool needsCheck( Theory::Effort e );
  /* reset at a round */
  void reset_round( Theory::Effort e );
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void registerQuantifier( Node q );
  void assertNode( Node n );
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "ConjectureGenerator"; }

//options
private:
  bool optReqDistinctVarPatterns();
  bool optFilterFalsification();
  bool optFilterConfirmation();
  bool optFilterConfirmationDomain();
  bool optFilterConfirmationOnlyGround();
  bool optFilterConfirmationNonCanonical();   //filter if all ground confirmations are non-canonical
  unsigned optFullCheckFrequency();
  unsigned optFullCheckConjectures();
};


}
}
}

#endif
