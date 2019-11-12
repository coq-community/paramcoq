# -*- Makefile -*-
# This Makefile assumes "make" has been previously run in the parent folder

include ../Makefile.coq.conf
COQBIN?=$(dir $(shell which coqtop))
COQC := $(COQBIN)coqc
PARAMLIBS := $(addprefix -I ../,$(COQMF_SRC_SUBDIRS))
EXAMPLES := example.v ListQueue.v features.v wadler.v bug.v bug2.v bug3.v bug4.v bug5.v dummyFix.v exmNotParametric.v

all:: Parametricity.vo

examples:: $(EXAMPLES:.v=.vo)

ListQueue.vo: ListQueue.v Parametricity.vo 
example.vo: example.v Parametricity.vo 
features.vo: features.v Parametricity.vo 
wadler.vo: wadler.v Parametricity.vo 
bug.vo: bug.v Parametricity.vo 
bug%.vo: bug%.v Parametricity.vo

%.vo: %.v
	$(COQC) $(PARAMLIBS) $<

ide:: Parametricity.vo 
	$(COQBIN)coqide -debug $(PARAMLIBS) $(EXAMPLES)

top:: Parametricity.vo
	$(COQBIN)coqtop $(PARAMLIBS)

clean:: 
	rm -f *.vo *.glob *.d
