#COQBIN := ../../coq/bin/
COQC := $(COQBIN)coqc 
.PHONY: coq clean

all: Parametricity.vo 

examples:: example.vo ListQueue.vo features.vo wadler.vo bug.vo bug2.vo bug3.vo bug4.vo bug5.vo dummyFix.vo exmNotParametric.vo

%.vo: %.v
	$(COQC) -I ../src $<

ListQueue.vo: ListQueue.v Parametricity.vo 
example.vo: example.v Parametricity.vo 
Transport.vo: Transport.v Parametricity.vo 
bug.vo: bug.v Parametricity.vo 
group.vo: group.v Transport.vo Parametricity.vo 
features.vo: features.v Parametricity.vo 
wadler.vo: wadler.v Parametricity.vo 
bug%.vo: bug%.v Parametricity.v

ide:: Parametricity.vo 
	$(COQBIN)coqide -debug -I ../src *.v 

top:: Parametricity.vo
	$(COQBIN)coqtop -I ../src 

clean:: 
	rm -f *.vo *.glob *.d
