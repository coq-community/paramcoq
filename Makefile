# -*- Makefile -*-

COQPROJECT=Make.cfg.local
include Makefile.common

src.$(COQVV)/paramcoq_mod.ml: src.$(COQVV)/paramcoq.mlpack
	sed -e "s/\([^ ]\{1,\}\)/let _=Mltop.add_known_module\"\1\" /g" $< > $@
	echo "let _=Mltop.add_known_module\"paramcoq\"" >> $@

pre-makefile:: src.$(COQVV)/paramcoq_mod.ml

Make.cfg.local: Make.cfg
	sed -e "s/src.version/src.$(COQVV)/" $< > $@

this-distclean::
	rm -f Make.cfg.local src.*/paramcoq_mod.ml
