ML_SOURCE:=Types.ml MLStringsImpl.ml
ML_OBJ:=$(patsubst %.ml,%.cmo,$(filter %.ml,$(ML_SOURCE)))
ML_OBJI:=$(ML_OBJ:.cmo=.cmi)

DEBUG:=-g

OCAMLC_OPTS:=$(DEBUG)

.PHONY: all clean

all: common.cmo common.cmi

clean:
	rm -f common.cmo common.cmi $(ML_OBJ) $(MK_OBJI) deps-ml

common.cmo common.cmi: $(ML_OBJ)
	ocamlc.opt -pack -o common.cmo $(ML_OBJ)

.SUFFIXES: .cmo .cmi .ml .mli

.ml.cmo:
	ocamlc.opt $(OCAMLC_OPTS) -c $<

.mli.cmi:
	ocamlc.opt $(OCAMLC_OPTS) -c $<

deps-ml: $(ML_SOURCE)
	ocamldep $^ > $@

include deps-ml