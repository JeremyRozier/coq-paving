EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://www.chargueraud.org/softs/tlc/' TLC \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v)
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ))
VS_OTHER := $(VS)
else
VS := $(VS_IN_PROJ)
endif

all: html

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

zip: 
	cp Makefile Makefile_common
	cp Makefile_up Makefile
	zip ImpAlg.zip Makefile  README.md _CoqProject `tail -n +2 _CoqProject`
	cp Makefile_common Makefile

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html

irif: html zip
	cp html/* -r ../persoIrif/ITP/
	cp ImpAlg.zip ../persoIrif/ITP/
	rsync -arpvz ../persoIrif/ emiquey@www.irif.fr:public_html/ --exclude '.git'




$(COQMAKEFILE): $(COQ_PROJ) $(VS)
		coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: clean all force
