# -*- Makefile -*-
# This Makefile assumes "make" has been previously run in the parent folder

COQBIN?=$(dir $(shell which coqtop))
COQC := $(COQBIN)coqc
PARAMLIBS := -I ../src
EXAMPLES := example.v ListQueue.v features.v wadler.v bug.v bug2.v bug3.v bug4.v bug5.v dummyFix.v exmNotParametric.v

all:: Parametricity.vo

examples:: $(EXAMPLES:.v=.vo)

ListQueue.vo: ListQueue.v Parametricity.vo
example.vo: example.v Parametricity.vo
features.vo: features.v Parametricity.vo
wadler.vo: wadler.v Parametricity.vo
bug.vo: bug.v Parametricity.vo
bug%.vo: bug%.v Parametricity.vo

# native eats too much memory, see eg https://gitlab.com/coq/coq/-/jobs/1144081161
%.vo: %.v
	$(COQC) $(PARAMLIBS) -native-compiler no $<

ide:: Parametricity.vo
	$(COQBIN)coqide -debug $(PARAMLIBS) $(EXAMPLES)

top:: Parametricity.vo
	$(COQBIN)coqtop $(PARAMLIBS)

clean::
	rm -f *.vo *.glob *.d
