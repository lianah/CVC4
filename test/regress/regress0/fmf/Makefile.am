# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @abs_top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	array_card.smt2 \
	agree466.smt2 \
	ALG008-1.smt2 \
	german169.smt2 \
	QEpres-uf.855035.smt \
	agree467.smt2 \
	Arrow_Order-smtlib.778341.smt \
	german73.smt2 \
	PUZ001+1.smt2 \
	refcount24.cvc.smt2 \
	fmf-bound-int.smt2 \
	fc-simple.smt2 \
	fc-unsat-tot-2.smt2 \
	fc-unsat-pent.smt2 \
	fc-pigeonhole19.smt2 \
	Hoare-z3.931718.smt \
	bug0909.smt2 \
	lst-no-self-rev-exp.smt2 \
	fib-core.smt2 \
	fore19-exp2-core.smt2 \
	with-ind-104-core.smt2 \
	syn002-si-real-int.smt2 \
	krs-sat.smt2 \
	forall_unit_data2.smt2 \
	sc_bad_model_1221.smt2


EXTRA_DIST = $(TESTS)


#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
