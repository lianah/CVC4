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

#include "util/resource_manager.h"
#include "util/output.h"
#include "smt/smt_engine_scope.h"
#include "smt/options.h" 
#include "theory/rewriter.h"

using namespace CVC4;
using namespace std;


/** Set a millisecond timer (0==off). */
void SmtTimer::set(unsigned long millis) {
  d_ms = millis;
  // keep track of when it was set, even if it's disabled (i.e. == 0)
  Trace("limit") << "SmtTimer::set(" << d_ms << ")" << std::endl;
  gettimeofday(&d_limit, NULL);
  Trace("limit") << "SmtTimer::set(): it's " << d_limit.tv_sec << "," << d_limit.tv_usec << std::endl;
  d_limit.tv_sec += millis / 1000;
  d_limit.tv_usec += (millis % 1000) * 1000;
  if(d_limit.tv_usec > 1000000) {
    ++d_limit.tv_sec;
    d_limit.tv_usec -= 1000000;
  }
  Trace("limit") << "SmtTimer::set(): limit is at " << d_limit.tv_sec << "," << d_limit.tv_usec << std::endl;
}

/** Return the milliseconds elapsed since last set(). */
unsigned long SmtTimer::elapsed() const {
  timeval tv;
  gettimeofday(&tv, NULL);
  Trace("limit") << "SmtTimer::elapsed(): it's now " << tv.tv_sec << "," << tv.tv_usec << std::endl;
  tv.tv_sec -= d_limit.tv_sec - d_ms / 1000;
  tv.tv_usec -= d_limit.tv_usec - (d_ms % 1000) * 1000;
  Trace("limit") << "SmtTimer::elapsed(): elapsed time is " << tv.tv_sec << "," << tv.tv_usec << std::endl;
  return tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

bool SmtTimer::expired() const {
  if(on()) {
    timeval tv;
    gettimeofday(&tv, NULL);
    Trace("limit") << "SmtTimer::expired(): current time is " << tv.tv_sec << "," << tv.tv_usec << std::endl;
    Trace("limit") << "SmtTimer::expired(): limit time is " << d_limit.tv_sec << "," << d_limit.tv_usec << std::endl;
    if(d_limit.tv_sec < tv.tv_sec ||
       (d_limit.tv_sec == tv.tv_sec && d_limit.tv_usec <= tv.tv_usec)) {
      Trace("limit") << "SmtTimer::expired(): OVER LIMIT!" << std::endl;
      return true;
    } else {
      Trace("limit") << "SmtTimer::expired(): within limit" << std::endl;
    }
  }
  return false;
}

ResourceManager::ResourceManager()
  : d_timer()
  // , d_timeBudgetCumulative(options::cumulativeMillisecondLimit())
  // , d_timeBudgetPerCall(options::perCallMillisecondLimit())
  // , d_resourceBudgetCumulative(options::cumulativeResourceLimit())
  // , d_resourceBudgetPerCall(options::perCallResourceLimit())
  , d_timeBudgetCumulative(0)
  , d_timeBudgetPerCall(0)
  , d_resourceBudgetCumulative(0)
  , d_resourceBudgetPerCall(0)

  , d_cumulativeTimeUsed(0)
  , d_cumulativeResourceUsed(0)
  , d_thisCallResourceUsed(0)
  , d_thisCallTimeBudget(0)
  , d_thisCallResourceBudget(0)
  , d_isHardLimit()
  , d_on(false)
  , d_spendResourceCalls(0)
{}


void ResourceManager::setResourceLimit(unsigned long units, bool cumulative) {
  d_on = true;
  if(cumulative) {
    Trace("limit") << "ResourceManager: setting cumulative resource limit to " << units << endl;
    d_resourceBudgetCumulative = (units == 0) ? 0 : (d_cumulativeResourceUsed + units);
  } else {
    Trace("limit") << "ResourceManager: setting per-call resource limit to " << units << endl;
    d_resourceBudgetPerCall = units;
  }
}

void ResourceManager::setTimeLimit(unsigned long millis, bool cumulative) {
  d_on = true;
  if(cumulative) {
    Trace("limit") << "ResourceManager: setting cumulative time limit to " << millis << " ms" << endl;
    d_timeBudgetCumulative = (millis == 0) ? 0 : (d_cumulativeTimeUsed + millis);
  } else {
    Trace("limit") << "ResourceManager: setting per-call time limit to " << millis << " ms" << endl;
    d_timeBudgetPerCall = millis;
  }
  d_timer.set(millis);
}

unsigned long ResourceManager::getResourceUsage() const {
  return d_cumulativeResourceUsed;
}

unsigned long ResourceManager::getTimeUsage() const {
  return d_cumulativeTimeUsed;
}

unsigned long ResourceManager::getResourceRemaining() const {
  if (d_thisCallResourceBudget <= d_thisCallResourceUsed)
    return 0;
  return d_thisCallResourceBudget - d_thisCallResourceUsed;
}

unsigned long ResourceManager::getTimeRemaining() const {
  unsigned long time_passed = d_timer.elapsed();
  if (time_passed >= d_thisCallTimeBudget)
    return 0;
  return d_thisCallTimeBudget - time_passed;
}

void ResourceManager::spendResource(bool unsafe) throw (UnsafeInterrupt) {
  ++d_spendResourceCalls;
  if (!d_on) return;
  
  ++d_cumulativeResourceUsed;
  ++d_thisCallResourceUsed;
  if(out()) {
    if (d_isHardLimit) {
      throw UnsafeInterrupt();
    }
    Trace("limit") << "ResourceManager::spendResource: interrupt!" << std::endl;
    smt::currentSmtEngine()->interrupt();
  }
}

void ResourceManager::beginCall() {
  d_thisCallResourceUsed = 0;

  if (cummulativeLimitOn()) {
    if (d_resourceBudgetCumulative) {
      d_thisCallResourceBudget = d_resourceBudgetCumulative <= d_cumulativeResourceUsed ? 0 :
                                 d_resourceBudgetCumulative - d_cumulativeResourceUsed;
    }

    if (d_timeBudgetCumulative) {
      d_thisCallTimeBudget = d_timeBudgetCumulative <= d_cumulativeTimeUsed? 0 :
                             d_timeBudgetCumulative - d_cumulativeTimeUsed;
      d_timer.set(d_thisCallTimeBudget);
    }
    // we are out of resources so we shouldn't update the
    // budget for this call to the per call budget
    if (d_thisCallTimeBudget == 0 ||
        d_thisCallResourceUsed == 0)
      return;
  }
  
  if (perCallLimitOn()) {
    // take min of what's left and per-call budget
    if (d_resourceBudgetPerCall) {
      d_thisCallResourceBudget = d_thisCallResourceBudget < d_resourceBudgetPerCall && d_thisCallResourceBudget != 0 ? d_thisCallResourceBudget : d_resourceBudgetPerCall;
    }
    
    if (d_timeBudgetPerCall) {
      d_thisCallTimeBudget = d_thisCallTimeBudget < d_timeBudgetPerCall && d_thisCallTimeBudget != 0 ? d_thisCallTimeBudget : d_timeBudgetPerCall;
    }
  }
}

void ResourceManager::endCall() {
  unsigned long usedInCall = d_timer.elapsed();
  d_cumulativeTimeUsed += usedInCall;
  //  d_cumulativeResourceUsed += d_propEngine->updateAndGetSatResource(0);
  // FIXME: what about other sat solver?
  d_timer.set(0);
}

bool ResourceManager::cummulativeLimitOn() const {
  return d_timeBudgetCumulative || d_resourceBudgetCumulative;
}

bool ResourceManager::perCallLimitOn() const {
  return d_timeBudgetPerCall || d_resourceBudgetPerCall;
}

bool ResourceManager::outOfResources() const {
  // resource limiting not enabled
  if (d_resourceBudgetPerCall == 0 &&
      d_resourceBudgetCumulative == 0)
    return false;
  
  return getResourceRemaining() == 0;
}

bool ResourceManager::outOfTime() const {
  if (d_timeBudgetPerCall == 0 &&
      d_timeBudgetCumulative == 0)
    return false;
  
  return d_timer.expired();
}
// void ResourceManager::setPropEngine(prop::PropEngine* prop) {
//   AlwaysAssert(d_propEngine == NULL);
//   d_propEngine = prop;
// }
