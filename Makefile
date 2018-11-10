# -*- Makefile -*-
.PHONY: coq clean

coq:: Makefile.coq
	$(MAKE) -f Makefile.coq

src/paramcoq_mod.ml: src/paramcoq.mlpack
	sed -e "s/\([^ ]\{1,\}\)/let _=Mltop.add_known_module\"\1\" /g" $< > $@
	echo "let _=Mltop.add_known_module\"paramcoq\"" >> $@

Makefile.coq: Make.cfg src/paramcoq_mod.ml
	coq_makefile -f Make.cfg -o Makefile.coq

distclean:
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.bak .depend src/paramcoq_mod.ml

install:
	$(MAKE) -f Makefile.coq install
