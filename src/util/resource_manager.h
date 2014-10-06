/*********************                                                        */
/*! \file resource_manager.h
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Manages and updates various resource and time limits. 
**
** Manages and updates various resource and time limits. 
**/

#include <cstddef>
#include "cvc4_private.h"
#include <sys/time.h>

#ifndef __CVC4__RESOURCE_MANAGER_H
#define __CVC4__RESOURCE_MANAGER_H


namespace CVC4 {
  class SmtEngine;
  namespace prop {
    class PropEngine;
  }
  /**
   * A helper class to keep track of a time budget and signal
   * the PropEngine when the budget expires.
   */
  class SmtTimer {

    unsigned long d_ms;
    timeval d_limit;

  public:

    /** Construct a SmtTimer attached to the given SmtEngine. */
    SmtTimer()
      : d_ms(0) {}

    /** Is the timer currently active? */
    bool on() const {
      return d_ms != 0;
    }

    /** Set a millisecond timer (0==off). */
    void set(unsigned long millis);
    
    /** Return the milliseconds elapsed since last set(). */
    unsigned long elapsed() const;

    bool expired() const;

  };/* class SmtTimer */


  class ResourceManager {
    friend class SmtEngine;

    SmtEngine* d_smtEngine;
    prop::PropEngine* d_propEngine;
    SmtTimer d_timer;

    /** A user-imposed cumulative time budget, in milliseconds.  0 = no limit. */
    unsigned long d_timeBudgetCumulative;
    /** A user-imposed per-call time budget, in milliseconds.  0 = no limit. */
    unsigned long d_timeBudgetPerCall;
    /** A user-imposed cumulative resource budget.  0 = no limit. */
    unsigned long d_resourceBudgetCumulative;
    /** A user-imposed per-call resource budget.  0 = no limit. */
    unsigned long d_resourceBudgetPerCall;

    /** The number of milliseconds used by this SmtEngine since its inception. */
    unsigned long d_cumulativeTimeUsed;
    /** The amount of resource used by this SmtEngine since its inception. */
    unsigned long d_cumulativeResourceUsed;

    /** The ammount of resource used by this SmtEngine during this call*/
    unsigned long d_thisCallResourceUsed;
    
    /** The ammount of resource budget for this call (min between per call budget
     * and left-over cummulative budget */
    unsigned long d_thisCallTimeBudget;
    unsigned long d_thisCallResourceBudget;
    
    // only the SmtEngine can update theses
    void setResourceLimit(unsigned long units, bool cumulative = false);
    void setTimeLimit(unsigned long millis, bool cumulative = false);

    bool d_on;

    ResourceManager(SmtEngine* smt)
      : d_smtEngine(smt)
      , d_propEngine(NULL)
      , d_timer()
      , d_timeBudgetCumulative()
      , d_timeBudgetPerCall()
      , d_resourceBudgetCumulative()
      , d_resourceBudgetPerCall()
      , d_cumulativeTimeUsed()
      , d_cumulativeResourceUsed()
      , d_thisCallResourceUsed()
      , d_thisCallTimeBudget()
      , d_thisCallResourceBudget()
      , d_on(false)
    {}

    /** 
     * Resets perCall limits to mark the start of a new call,
     * updates budget for current call and starts the timer
     */    
    void beginCall();
    /** 
     * Marks the end of a SmtEngine check call, stops the timer
     * updates cummulative time used.
     * 
     */
    void endCall();
    void setPropEngine(prop::PropEngine* prop);
  public:

    bool limitOn() const {return cummulativeLimitOn() || perCallLimitOn(); }
    bool cummulativeLimitOn() const;
    bool perCallLimitOn() const;
    
    bool outOfResources() const;
    bool outOfTime() const;
    bool out() const {return d_on && (outOfResources() || outOfTime()); }
    
    unsigned long getResourceUsage() const;
    unsigned long getTimeUsage() const;
    unsigned long getResourceRemaining() const;
    unsigned long getTimeRemaining() const;

    unsigned long getResourceBudgetForThisCall() { return d_thisCallResourceBudget; }
    void spendResource();
    void spendResource(unsigned long units);
  };
}/* CVC4 namespace */

#endif /* __CVC4__RESOURCE_MANAGER_H */
