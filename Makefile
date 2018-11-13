# -*- Makefile -*-
.PHONY: coq clean

coq:: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Make.cfg
	coq_makefile -f Make.cfg -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean

distclean:
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.bak .coqdeps.d

install:
	$(MAKE) -f Makefile.coq install
