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
#include <sys/time.h>

#include "cvc4_private.h"
#include "util/exception.h"
#include "util/unsafe_interrupt_exception.h"

#ifndef __CVC4__RESOURCE_MANAGER_H
#define __CVC4__RESOURCE_MANAGER_H


namespace CVC4 {
  /**
   * A helper class to keep track of a time budget and signal
   * the PropEngine when the budget expires.
   */
  class Timer {

    unsigned long d_ms;
    timeval d_wall_limit;
    clock_t d_cpu_start_time;
    clock_t d_cpu_limit;
    
    bool d_wall_time;

    /** Return the milliseconds elapsed since last set() cpu time. */
    unsigned long elapsedCPU() const;
    /** Return the milliseconds elapsed since last set() wall time. */
    unsigned long elapsedWall() const;

  public:

    /** Construct a Timer. */
    Timer()
      : d_ms(0)
      , d_cpu_start_time(0)
      , d_cpu_limit(0)
      , d_wall_time(true)
    {}

    /** Is the timer currently active? */
    bool on() const {
      return d_ms != 0;
    }

    /** Set a millisecond timer (0==off). */
    void set(unsigned long millis, bool wall_time = true);
    /** Return the milliseconds elapsed since last set() wall/cpu time
     depending on d_wall_time*/
    unsigned long elapsed() const;
    bool expired() const;

  };/* class Timer */


  class ResourceManager {

    Timer d_cumulativeTimer;
    Timer d_perCallTimer;
    
    /** A user-imposed cumulative time budget, in milliseconds.  0 = no limit. */
    unsigned long d_timeBudgetCumulative;
    /** A user-imposed per-call time budget, in milliseconds.  0 = no limit. */
    unsigned long d_timeBudgetPerCall;
    /** A user-imposed cumulative resource budget.  0 = no limit. */
    unsigned long d_resourceBudgetCumulative;
    /** A user-imposed per-call resource budget.  0 = no limit. */
    unsigned long d_resourceBudgetPerCall;

    /** The number of milliseconds used. */
    unsigned long d_cumulativeTimeUsed;
    /** The amount of resource used. */
    unsigned long d_cumulativeResourceUsed;

    /** The ammount of resource used during this call*/
    unsigned long d_thisCallResourceUsed;
    
    /** The ammount of resource budget for this call (min between per call budget
     * and left-over cummulative budget */
    unsigned long d_thisCallTimeBudget;
    unsigned long d_thisCallResourceBudget;
    

    bool d_isHardLimit;
    bool d_on;
    bool d_cpuTime;
    unsigned long d_spendResourceCalls;

    // Count indicating how often to check resource manager
    // in loops
    const static unsigned long s_resourceCount;
  public:

    ResourceManager();
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
    void spendResource(bool unsafe = true) throw(UnsafeInterruptException) ;

    void setHardLimit(bool value);
    void setResourceLimit(unsigned long units, bool cumulative = false);
    void setTimeLimit(unsigned long millis, bool cumulative = false);
    void useCPUTime(bool cpu); 

    void enable(bool on);
    /** 
     * Resets perCall limits to mark the start of a new call,
     * updates budget for current call and starts the timer
     */    
    void beginCall();
    /** 
     * Marks the end of a SmtEngine check call, stops the per
     * call timer, updates cummulative time used.
     * 
     */
    void endCall();
    static unsigned long getFrequencyCount() { return s_resourceCount; }
  };
}/* CVC4 namespace */

#endif /* __CVC4__RESOURCE_MANAGER_H */
