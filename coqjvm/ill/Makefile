# Includes the generated lexer and parser (as they can be built easily
# and the resulting files may have deps), but exclude the coq
# extracted code and ocaml that it relies upon.  NB: we need to add an
# explicit dep on coqextract.cmi though.
ML_SOURCE:=ill_absyn.ml BasicsImpl.ml ill_lexer.ml ill_parser.ml \
           CoqModules.ml Coqutil.ml TranslateTools.ml ILL_Translate.ml \
           ill_proofcheck.ml

ML_OBJ:=$(COQML_PREREQ:.ml=.cmo) coqextract.cmo $(ML_SOURCE:.ml=.cmo)
ML_OBJI:=$(ML_OBJ:.cmo=.cmi)

# You will also need to change mkcoqml if you change this
COQ_DIR_OPT:=-R . ILL

DEBUG:=-g

OCAMLC_OPTS:=-I ../../extlib-1.5/ -I ../../ocaml-jvml-bob/lib $(DEBUG)

.PHONY: all clean recclean

all: ill_proofcheck ILLSimplifier.vo

ill_proofcheck: common.cmo coqextract.cmo $(ML_OBJ)
	ocamlc.opt $(OCAMLC_OPTS) -o $@ unix.cma extLib.cma ocaml_jvml.cmo $^

# FIXME: need some dependencies here
common.cmo common.cmi:
	$(MAKE) -C ../common
	cp ../common/common.cmo ../common/common.cmi .

coqextract.cmo coqextract.cmi: common.cmo common.cmi
	./mkcoqml

CoqModules.cmo: coqextract.cmi
BasicsImpl.cmo: coqextract.cmi
Coqutil.cmo: coqextract.cmi
ILL_Translate.cmo: common.cmi

clean:
	rm -f $(ML_OBJ) $(ML_OBJI) \
	      coqextract.ml coqextract.mli ill_parser.ml ill_parser.mli \
	      ill_lexer.ml ill_proofcheck \
	      common.cmo common.cmi \
	      *.vo \
	      deps-coq deps-ml

recclean: clean
	$(MAKE) -C .. clean


%.cmo: %.ml
	ocamlc.opt $(OCAMLC_OPTS) -c $<

%.cmi: %.mli
	ocamlc.opt $(OCAMLC_OPTS) -c $<

%.ml %.mli: %.mly
	ocamlyacc $<

%.ml: %.mll
	ocamllex $<

# For external coq modules we switch to that directory and make it.
# Note that the order is important.

../%.vo: ../%.v
	$(MAKE) -C .. $*.vo

%.vo: %.v
	coqc -Q .. "" $(COQ_DIR_OPT) $*

deps-coq: *.v
	coqdep -Q .. "" $(COQ_DIR_OPT) $^ | sed -e 's/^ILLExtraction.vo/coqextract.cmo coqextract.cmi/' > $@

deps-ml: $(ML_SOURCE)
	ocamldep $^ > $@

include deps-coq
include deps-ml
