ML_SOURCE:=BasicsImpl.ml BasicResourceAlgebra.ml \
           FileNativeImpl.ml \
           CoqModules.ml Coqutil.ml TranslateAnnos.mli \
           TranslateTools.ml TranslateAnnos.ml BuiltinClasses.ml Translate.ml \
           main.ml

ML_OBJ:=coqextract.cmo $(patsubst %.ml,%.cmo,$(filter %.ml,$(ML_SOURCE)))
ML_OBJI:=$(ML_OBJ:.cmo=.cmi)

DEBUG:=-g

OCAMLC_OPTS:=-I ../extlib-1.5/ -I ../ocaml-jvml-bob/lib $(DEBUG)

.PHONY: all-local all all-sub clean recclean cleanocaml veryclean doc

all-local: coqjvm

all: all-local all-sub doc
all-sub:
	$(MAKE) -C ill all
	$(MAKE) -C verifier all

coqjvm: common.cmo coqextract.cmo $(ML_OBJ)
	ocamlc $(OCAMLC_OPTS) -o coqjvm unix.cma extLib.cma ocaml_jvml.cmo $^

doc:
	mkdir -p doc
	coqdoc -g --html --toc --multi-index -d doc -R ill ILL -R verifier Verifier *.v ill/*.v verifier/*.v

common.cmo common.cmi:
	$(MAKE) -C common
	cp common/common.cmo common/common.cmi .

coqextract.cmo coqextract.cmi: common.cmo common.cmi
	./mkcoqml

main.cmo: coqextract.cmi common.cmi
BasicsImpl.cmo: coqextract.cmi
BuiltinClasses.cmo: common.cmi
CoqModules.cmo: coqextract.cmi
Coqutil.cmo : coqextract.cmi
Translate.cmo: common.cmi

clean:
	rm -f $(ML_OBJ) $(ML_OBJI) \
	      ill_lexer.ml ill_parser.mli ill_parser.ml \
	      coqextract.ml coqextract.mli \
	      common.cmo common.cmi \
	      coqjvm \
	      *.vo \
	      *~ \
	      deps-coq deps-ml \
	      doc/*.html

recclean: clean
	$(MAKE) -C common clean
	$(MAKE) -C ill clean
	$(MAKE) -C verifier clean

cleanocaml:
	rm -f $(ML_OBJ) $(ML_OBJI) coqjvm *~

veryclean: recclean
	$(MAKE) -C extlib-1.5 clean
	$(MAKE) -C javaLib-1.0 clean

.SUFFIXES: .v .vo .ml .cmo .mli .cmi .class .java .mly .mll

.ml.cmo:
	ocamlc.opt $(OCAMLC_OPTS) -c $<

.mli.cmi:
	ocamlc.opt $(OCAMLC_OPTS) -c $<

.mly.mli:
	ocamlyacc $<

.mly.ml:
	ocamlyacc $<

.mll.ml:
	ocamllex $<

.v.vo:
	coqtop -compile $*

.java.class:
	javac $<

deps-coq: *.v
	coqdep -I .  $^ | sed -e 's/^Extraction.vo/coqextract.cmo coqextract.cmi/' > $@

deps-ml: $(ML_SOURCE)
	ocamldep $^ > $@

include deps-coq
include deps-ml
