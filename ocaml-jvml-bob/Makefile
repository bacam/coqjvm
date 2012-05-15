# ocaml-jvml Makefile
# May 2006


# ---------------- Variables ---------------- #

EXTLIBDIR := ../extlib-1.5
EXTLIB    := extLib.cma
EXTLIBOPT := extLib.cmxa

OCAMLC        := ocamlc.opt
OCAMLFLAGS    := -g -I $(EXTLIBDIR) -I src
OCAMLOPTFLAGS := -I $(EXTLIBDIR) -I src
OCAMLOPT      := ocamlopt.opt
OCAMLDEP      := ocamldep.opt
OCAMLLEX      := ocamllex.opt

SRCP := Util.mli              Util.ml              \
        Zipfile.mli           Zipfile.ml           \
        JFloat.mli            JFloat.ml            \
        Jvmtype.mli           Jvmtype.ml           \
        AccessFlags.mli       AccessFlags.ml       \
        Constpool.mli         Constpool.ml         \
        LowlevelBytecode.mli  LowlevelBytecode.ml  \
        Classfile.mli         Classfile.ml         \
        ClassfileOutput.mli   ClassfileOutput.ml   \
        ClassfileInput.mli    ClassfileInput.ml    \
        Label.mli             Label.ml             \
        Bytecode.mli          Bytecode.ml          \
        Classdecl.mli         Classdecl.ml         \
        CompileBytecode.mli   CompileBytecode.ml   \
        Compile.mli           Compile.ml           \
        DecompileBytecode.mli DecompileBytecode.ml \
        Decompile.mli         Decompile.ml         \
        AnalysisBytecode.mli  AnalysisBytecode.ml

SRC := $(patsubst %,src/%,${SRCP})

CMO := $(patsubst %.ml,%.cmo,$(patsubst %.mli,%.cmi,$(SRC)))
CMX := $(patsubst %.ml,%.cmx,$(patsubst %.mli,%.cmi,$(SRC)))
CMI := $(patsubst %.ml,%.cmi,$(filter %.ml,$(SRC)))
MLI := $(filter %.mli,$(SRC))


.PHONY: all clean clean-all depend doc test

# ---------------- Targets ---------------- #

all: lib/ocaml_jvml.cmo lib/ocaml_jvml.cmx

$(EXTLIB):
	$(MAKE) -C $(EXTLIBDIR)

$(EXTLIBOPT):
	$(MAKE) -C $(EXTLIBDIR) opt

lib:
	@mkdir -p lib

doc: $(CMI)
	ocamldoc -I $(EXTLIBDIR) -I src -d doc -html $(MLI)

lib/ocaml_jvml.cmo: lib $(CMO)
	$(OCAMLC) -pack -o lib/ocaml_jvml.cmo $(filter-out %.cmi,$(CMO))

lib/ocaml_jvml.cmx: lib $(CMX)
	$(OCAMLOPT) -pack -o lib/ocaml_jvml.cmx $(filter-out %.cmi,$(CMX))

jas: lib/ocaml_jvml.cmo lib/ocaml_jvml.cmi assembler/Assembler_lexer.mll assembler/Assembler_parser.ml assembler/Assembler.ml
	$(OCAMLLEX) assembler/Assembler_lexer.mll
	$(OCAMLC) -g -I $(EXTLIBDIR) -I lib -I assembler -o jas $(EXTLIB) ocaml_jvml.cmo assembler/Assembler_parser.ml assembler/Assembler_lexer.ml assembler/Assembler.ml

jdis: lib/ocaml_jvml.cmo lib/ocaml_jvml.cmi assembler/Disassembler.ml
	$(OCAMLC) -g -I $(EXTLIBDIR) -I lib -I assembler -o jdis $(EXTLIB) ocaml_jvml.cmo assembler/Disassembler.ml

test: testrwjar testrwjar.opt decompilejar decompilejar.opt

testrwjar: lib/ocaml_jvml.cmo tests/testrwjar.ml
	$(OCAMLC) -I $(EXTLIBDIR) -I lib -g -o testrwjar $(EXTLIB) ocaml_jvml.cmo tests/testrwjar.ml

testrwjar.opt: lib/ocaml_jvml.cmx tests/testrwjar.ml
	$(OCAMLOPT) -I $(EXTLIBDIR) -I lib -g -o testrwjar.opt $(EXTLIBOPT) ocaml_jvml.cmx tests/testrwjar.ml

decompilejar: lib/ocaml_jvml.cmo tests/decompilejar.ml
	$(OCAMLC) -I $(EXTLIBDIR) -I lib -g -o decompilejar $(EXTLIB) ocaml_jvml.cmo tests/decompilejar.ml

decompilejar.opt: lib/ocaml_jvml.cmx tests/decompilejar.ml
	$(OCAMLOPT) -I $(EXTLIBDIR) -I lib -g -o decompilejar.opt $(EXTLIBOPT) ocaml_jvml.cmx tests/decompilejar.ml

# ---------------- Maintenance ---------------- #
.depend: $(SRC)
	@$(OCAMLDEP) -I src $(SRC) > .depend

clean:
	rm -f .depend
	rm -f src/*.cm[iox] src/*.o src/*~
	rm -f tests/*.cm[iox] tests/*.o tests/*~
	rm -f *~ doc/*~ doc/*.html
	rm -rf lib
	rm -f testrwjar testrwjar.opt
	rm -f decompilejar decompilejar.opt
	rm -f jas jdis
	rm -f assembler/*.cm[iox] assembler/*~ assembler/Assembler_lexer.ml

clean-all: clean
	cd $(EXTLIBDIR) && $(MAKE) clean

# ---------------- Common rules ---------------- #

.SUFFIXES: .ml .mll .mly .mli .cmo .cmi .cmx .o

.mll.ml:
	$(OCAMLLEX) $<

.mly.ml:
	$(OCAMLYACC) -v $<

.mly.mli:
	$(OCAMLYACC) $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -for-pack Ocaml_jvml -c $<


# ---------------- Include dependencies ---------------- #
-include .depend
