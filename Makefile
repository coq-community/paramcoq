# -*- Makefile -*-

COQPROJECT=Make.cfg.local
include Makefile.common

src.$(COQVV)/paramcoq_mod.ml: src.$(COQVV)/paramcoq.mlpack
	sed -e "s/\([^ ]\{1,\}\)/let _=Mltop.add_known_module\"\1\" /g" $< > $@
	echo "let _=Mltop.add_known_module\"paramcoq\"" >> $@

pre-makefile:: src.$(COQVV)/paramcoq_mod.ml

ifeq (, $(shell which coqpp))
 PPEXT=ml4
else
 # 8.9 doesn't supports the attribute coqpp syntax
 ifeq ($(COQVV),8.9)
   PPEXT=ml4
 else
   PPEXT=mlg
 endif
endif

Make.cfg.local: Make.cfg
	sed -e "s/src.version/src.$(COQVV)/;s/coqpp.ext/$(PPEXT)/" $< > $@

ifeq ($(COQVV),8.7)
this-config::
	sed -e "s/\(Parametricity Module Decimal.\)//" -i test-suite/Parametricity.v
endif

this-distclean::
	rm -f Make.cfg.local src.*/paramcoq_mod.ml
