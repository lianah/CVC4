/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Proof manager
 **
 ** Proof manager
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__PROOF_H
#define __CVC4__PROOF__PROOF_H

#include "options/smt_options.h"


/* Do NOT use #ifdef CVC4_PROOF to check if proofs are enabled.
 * We cannot assume users will use -DCVC4_PROOFS if they have a proofs build.
 * The preferred way of checking that proofs are enabled is to use:
 * #if IS_PROOFS_BUILD
 * ...
 * #endif
 *
 * The macro IS_PROOFS_BUILD is defined in util/configuration_private.h
 *
 * This has the effect of forcing that location to have included this header
 * *before* performing this test. This includes C preprocessing expansion.
 * This forces the inclusion of "cvc4_private.h". This is intentional!
 *
 * See bug 688 for more details:
 * http://cvc4.cs.nyu.edu/bugs/show_bug.cgi?id=688
 *
 * If you want to check CVC4_PROOF, you should have a very good reason
 * and should list the exceptions here:
 * - Makefile.am
 * - proof/proofs.h
 * - util/configuration_private.h
 */

#ifdef CVC4_PROOF
#  define PROOF(x) if(options::proof() || options::unsatCores()) { x; }
#  define NULLPROOF(x) (options::proof() || options::unsatCores()) ? x : NULL
#  define PROOF_ON() (options::proof() || options::unsatCores())
#else /* CVC4_PROOF */
#  define PROOF(x)
#  define NULLPROOF(x) NULL
#  define PROOF_ON() false
#endif /* CVC4_PROOF */


#endif /* __CVC4__PROOF__PROOF_H */
