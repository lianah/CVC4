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

void Timer::set(unsigned long millis, bool wallTime) {
  d_ms = millis;
  Trace("limit") << "Timer::set(" << d_ms << ")" << std::endl;  
  // keep track of when it was set, even if it's disabled (i.e. == 0)
  d_wall_time = wallTime;
  if (d_wall_time) {
    // Wall time
    gettimeofday(&d_wall_limit, NULL);
    Trace("limit") << "Timer::set(): it's " << d_wall_limit.tv_sec << "," << d_wall_limit.tv_usec << std::endl;
    d_wall_limit.tv_sec += millis / 1000;
    d_wall_limit.tv_usec += (millis % 1000) * 1000;
    if(d_wall_limit.tv_usec > 1000000) {
      ++d_wall_limit.tv_sec;
      d_wall_limit.tv_usec -= 1000000;
    }
    Trace("limit") << "Timer::set(): limit is at " << d_wall_limit.tv_sec << "," << d_wall_limit.tv_usec << std::endl;
  } else {
    // CPU time
    d_cpu_start_time = ((double)clock())/(CLOCKS_PER_SEC *0.001);
    d_cpu_limit = d_cpu_start_time + d_ms;
  }
}

/** Return the milliseconds elapsed since last set(). */
unsigned long Timer::elapsedWall() const {
  Assert (d_wall_time);
  timeval tv;
  gettimeofday(&tv, NULL);
  Trace("limit") << "Timer::elapsedWallTime(): it's now " << tv.tv_sec << "," << tv.tv_usec << std::endl;
  tv.tv_sec -= d_wall_limit.tv_sec - d_ms / 1000;
  tv.tv_usec -= d_wall_limit.tv_usec - (d_ms % 1000) * 1000;
  Trace("limit") << "Timer::elapsedWallTime(): elapsed time is " << tv.tv_sec << "," << tv.tv_usec << std::endl;
  return tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

unsigned long Timer::elapsedCPU() const {
  Assert (!d_wall_time);
  clock_t elapsed = ((double)clock())/(CLOCKS_PER_SEC *0.001)- d_cpu_start_time;
  Trace("limit") << "Timer::elapsedCPUTime(): elapsed time is " << elapsed << " ms" <<std::endl;
  return elapsed; 
}

unsigned long Timer::elapsed() const {
  if (d_wall_time)
    return elapsedWall();
  return elapsedCPU();
}

bool Timer::expired() const {
  if (!on()) return false;

  if (d_wall_time) {
    timeval tv;
    gettimeofday(&tv, NULL);
    Debug("limit") << "Timer::expired(): current wall time is " << tv.tv_sec << "," << tv.tv_usec << std::endl;
    Debug("limit") << "Timer::expired(): limit wall time is " << d_wall_limit.tv_sec << "," << d_wall_limit.tv_usec << std::endl;
    if(d_wall_limit.tv_sec < tv.tv_sec ||
       (d_wall_limit.tv_sec == tv.tv_sec && d_wall_limit.tv_usec <= tv.tv_usec)) {
      Debug("limit") << "Timer::expired(): OVER LIMIT!" << std::endl;
      return true;
    }
    Debug("limit") << "Timer::expired(): within limit" << std::endl;
    return false;
  }

  // cpu time
  double current = ((double)clock())/(CLOCKS_PER_SEC*0.001);
  Debug("limit") << "Timer::expired(): current cpu time is " << current <<  std::endl;
  Debug("limit") << "Timer::expired(): limit cpu time is " << d_cpu_limit <<  std::endl;
  if (current >= d_cpu_limit) {
    Debug("limit") << "Timer::expired(): OVER LIMIT!" << current <<  std::endl;
    return true;
  }
  return false;
}

const unsigned long ResourceManager::s_resourceCount = 1000;

ResourceManager::ResourceManager()
  : d_cumulativeTimer()
  , d_perCallTimer()
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
  , d_cpuTime(false)
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
    d_cumulativeTimer.set(millis, !d_cpuTime);
  } else {
    Trace("limit") << "ResourceManager: setting per-call time limit to " << millis << " ms" << endl;
    d_timeBudgetPerCall = millis;
    // perCall timer will be set in beginCall
  }

}

unsigned long ResourceManager::getResourceUsage() const {
  return d_cumulativeResourceUsed;
}

unsigned long ResourceManager::getTimeUsage() const {
  if (d_timeBudgetCumulative) {
    return d_cumulativeTimer.elapsed();
  }
  return d_cumulativeTimeUsed;
}

unsigned long ResourceManager::getResourceRemaining() const {
  if (d_thisCallResourceBudget <= d_thisCallResourceUsed)
    return 0;
  return d_thisCallResourceBudget - d_thisCallResourceUsed;
}

unsigned long ResourceManager::getTimeRemaining() const {
  unsigned long time_passed = d_cumulativeTimer.elapsed();
  if (time_passed >= d_thisCallTimeBudget)
    return 0;
  return d_thisCallTimeBudget - time_passed;
}

void ResourceManager::spendResource(bool unsafe) throw (UnsafeInterruptException) {
  ++d_spendResourceCalls;
  if (!d_on) return;

  Debug("limit") << "ResourceManager::spendResource()" << std::endl;
  ++d_cumulativeResourceUsed;
  ++d_thisCallResourceUsed;
  if(out()) {
    Trace("limit") << "ResourceManager::spendResource: interrupt!" << std::endl;
	Trace("limit") << "                 on call " << d_spendResourceCalls << std::endl;
    if (outOfTime()) {
      Trace("limit") << "ResourceManager::spendResource: elapsed time" << d_cumulativeTimer.elapsed() << std::endl;
    }
    
    if (smt::smtEngineInScope()) {
      theory::Rewriter::clearCaches();
    }
    if (d_isHardLimit) {
      throw UnsafeInterruptException();
    }

    // interrupt it next time resources are checked
    if (smt::smtEngineInScope()) {
      smt::currentSmtEngine()->interrupt();
    }
  }
}

void ResourceManager::beginCall() {
  
  d_perCallTimer.set(d_timeBudgetPerCall, !d_cpuTime);
  d_thisCallResourceUsed = 0;
  if (!d_on) return;
  
  if (cummulativeLimitOn()) {
    if (d_resourceBudgetCumulative) {
      d_thisCallResourceBudget = d_resourceBudgetCumulative <= d_cumulativeResourceUsed ? 0 :
                                 d_resourceBudgetCumulative - d_cumulativeResourceUsed;
    }

    if (d_timeBudgetCumulative) {

      AlwaysAssert(d_cumulativeTimer.on());
      // timer was on since the option was set
      d_cumulativeTimeUsed = d_cumulativeTimer.elapsed();
      d_thisCallTimeBudget = d_timeBudgetCumulative <= d_cumulativeTimeUsed? 0 :
                             d_timeBudgetCumulative - d_cumulativeTimeUsed;
      d_cumulativeTimer.set(d_thisCallTimeBudget, d_cpuTime);
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
  unsigned long usedInCall = d_perCallTimer.elapsed();
  d_perCallTimer.set(0);
  d_cumulativeTimeUsed += usedInCall;
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
  
  return d_cumulativeTimer.expired() || d_perCallTimer.expired();
}

void ResourceManager::useCPUTime(bool cpu) {
  Trace("limit") << "ResourceManager::useCPUTime("<< cpu <<")\n"; 
  d_cpuTime = cpu;
}

void ResourceManager::setHardLimit(bool value) {
  Trace("limit") << "ResourceManager::setHardLimit("<< value <<")\n"; 
  d_isHardLimit = value;
}

void ResourceManager::enable(bool on) {
  Trace("limit") << "ResourceManager::enable("<< on <<")\n";
  d_on = on;
}