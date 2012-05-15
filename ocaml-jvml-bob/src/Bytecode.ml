(* Bytecode.sml
 *
 * K. MacKenzie
 * May 2006
 *)

(* The type of JVM instructions, extended with labels *)
type 'a instr =
  | Jlabel of Label.label * 'a
  | Jaaload
  | Jaastore
  | Jaconst_null
  | Jaload of int
  | Jarraylength
  | Jastore of int
  | Jathrow

  | Jbaload
  | Jbastore

  | Jcaload
  | Jcastore
  | Jcheckcast  of Jvmtype.jref_type
  | Jclassconst of Jvmtype.jref_type

  | Jd2f
  | Jd2i
  | Jd2l
  | Jdadd
  | Jdaload
  | Jdastore
  | Jdcmpg | Jdcmpl
  | Jdconst of float
  | Jddiv
  | Jdload of int
  | Jdmul
  | Jdneg
  | Jdrem
  | Jdstore of int
  | Jdsub
  | Jdup
  | Jdup_x1
  | Jdup_x2
  | Jdup2
  | Jdup2_x1
  | Jdup2_x2

  | Jf2d
  | Jf2i
  | Jf2l
  | Jfadd
  | Jfaload
  | Jfastore
  | Jfcmpg | Jfcmpl
  | Jfconst of JFloat.t
  | Jfdiv
  | Jfload of int
  | Jfmul
  | Jfneg
  | Jfrem
  | Jfstore of int
  | Jfsub

  | Jgetfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Jgetstatic of Jvmtype.jclass * string * Jvmtype.jtype
  | Jgoto of Label.label

  | Ji2b
  | Ji2c
  | Ji2d
  | Ji2f
  | Ji2l
  | Ji2s
  | Jiadd
  | Jiaload
  | Jiand
  | Jiastore
  | Jiconst of int32
  | Jidiv
  | Jif_acmpeq of Label.label | Jif_acmpne of Label.label
  | Jif_icmpeq of Label.label | Jif_icmpne of Label.label | Jif_icmplt of Label.label
  | Jif_icmpge of Label.label | Jif_icmpgt of Label.label | Jif_icmple of Label.label
  | Jifeq of Label.label | Jifne of Label.label | Jiflt of Label.label
  | Jifge of Label.label | Jifgt of Label.label | Jifle of Label.label
  | Jifnonnull of Label.label | Jifnull of Label.label
  | Jiinc of int * int
  | Jiload of int
  | Jimul
  | Jineg
  | Jinstanceof of Jvmtype.jref_type
  | Jinvokeinterface of Jvmtype.jclass * string * Jvmtype.methodsig
  | Jinvokespecial   of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Jinvokestatic    of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Jinvokevirtual   of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Jior
  | Jirem
  | Jishl
  | Jishr
  | Jistore of int
  | Jisub
  | Jiushr
  | Jixor

  | Jjsr of Label.label

  | Jl2d
  | Jl2f
  | Jl2i
  | Jladd
  | Jlaload
  | Jland
  | Jlastore
  | Jlcmp
  | Jlconst of int64
  | Jldiv
  | Jlload of int
  | Jlmul
  | Jlneg
  | Jlookupswitch of Label.label * (int32 * Label.label) list
  | Jlor
  | Jlrem
  | Jlshl
  | Jlshr
  | Jlstore of int
  | Jlsub
  | Jlushr
  | Jlxor

  | Jmonitorenter
  | Jmonitorexit

  | Jnew of Jvmtype.jclass
  | Jnewarray of Jvmtype.jtype * int
  | Jnop

  | Jpop
  | Jpop2
  | Jputfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Jputstatic of Jvmtype.jclass * string * Jvmtype.jtype

  | Jret of int
  | Jreturn

  | Jsaload
  | Jsastore
  | Jsconst of string
  | Jswap

  | Jtableswitch of Label.label * int32 * Label.label list

let strOfLabel l = Label.to_string l
let strOfIndex i = string_of_int i
let strOfCref c = Jvmtype.string_of_reftype c

let toString = function
  | Jlabel (l,_)       -> strOfLabel l ^ ":"
  | Jsconst s          -> "\tsconst " ^ "\"" ^ String.escaped s ^ "\""
  | Jaaload            -> "\taaload"
  | Jaastore           -> "\taastore"
  | Jaconst_null       -> "\taconst_null"
  | Jaload i           -> "\taload  " ^ strOfIndex i
  | Jarraylength       -> "\tarraylength"
  | Jastore i          -> "\tastore " ^ strOfIndex i
  | Jathrow            -> "\tathrow"
  | Jbaload            -> "\tbaload"
  | Jbastore           -> "\tbastore"
  | Jcaload            -> "\tcaload"
  | Jcastore           -> "\tcastore"
  | Jcheckcast c       -> "\tcheckcast " ^ strOfCref c
  | Jclassconst c      -> "\tclassconst " ^ strOfCref c
  | Jd2f               -> "\td2f"
  | Jd2i               -> "\td2i"
  | Jd2l               -> "\td2l"
  | Jdadd              -> "\tdadd"
  | Jdaload            -> "\tdaload"
  | Jdastore           -> "\tdastore"
  | Jdcmpg             -> "\tdcmpg"
  | Jdcmpl             -> "\tdcmpl"
  | Jdconst x          -> Printf.sprintf "\tdconst %f // APPROXIMATELY" x
  | Jddiv              -> "\tddiv"
  | Jdload i           -> "\tdload  " ^ strOfIndex i
  | Jdmul              -> "\tdmul"
  | Jdneg              -> "\tdneg"
  | Jdrem              -> "\tdrem"
  | Jdstore i          -> "\tdstore " ^ strOfIndex i
  | Jdsub              -> "\tdsub"
  | Jdup               -> "\tdup"
  | Jdup_x1            -> "\tdup_x1"
  | Jdup_x2            -> "\tdup_x2"
  | Jdup2              -> "\tdup2"
  | Jdup2_x1           -> "\tdup2_x1"
  | Jdup2_x2           -> "\tdup2_x2"
  | Jf2d               -> "\tf2d"
  | Jf2i               -> "\tf2i"
  | Jf2l               -> "\tf2l"
  | Jfadd              -> "\tfadd"
  | Jfaload            -> "\tfaload"
  | Jfastore           -> "\tfastore"
  | Jfcmpg             -> "\tfcmpg"
  | Jfcmpl             -> "\tfcmpl"
  | Jfconst x          -> Printf.sprintf "\tfconst %f // APPROXIMATELY" (JFloat.to_float x)
  | Jfdiv              -> "\tfdiv"
  | Jfload i           -> "\tfload  " ^ strOfIndex i
  | Jfmul              -> "\tfmul"
  | Jfneg              -> "\tfneg"
  | Jfrem              -> "\tfrem"
  | Jfstore i          -> "\tfstore " ^ strOfIndex i
  | Jfsub              -> "\tfsub"
  | Jgetfield (c,f,t)  -> "\tgetfield " ^ f
  | Jgetstatic (c,f,t) -> "\tgetstatic " ^ f
  | Jgoto l            -> "\tgoto   " ^ strOfLabel l
  | Ji2b               -> "\ti2b"
  | Ji2c               -> "\ti2c"
  | Ji2d               -> "\ti2d"
  | Ji2f               -> "\ti2f"
  | Ji2l               -> "\ti2l"
  | Ji2s               -> "\ti2s"
  | Jiadd              -> "\tiadd"
  | Jiaload            -> "\tiaload"
  | Jiand              -> "\tiand"
  | Jiastore           -> "\tiastore"
  | Jiconst c          -> Printf.sprintf "\ticonst %ld" c
  | Jidiv              -> "\tidiv"
  | Jif_acmpeq l       -> "\tif_acmpeq " ^ strOfLabel l
  | Jif_acmpne l       -> "\tif_acmpne " ^ strOfLabel l
  | Jif_icmpeq l       -> "\tif_icmpeq " ^ strOfLabel l
  | Jif_icmpne l       -> "\tif_icmpne " ^ strOfLabel l
  | Jif_icmplt l       -> "\tif_icmplt " ^ strOfLabel l
  | Jif_icmpge l       -> "\tif_icmpge " ^ strOfLabel l
  | Jif_icmpgt l       -> "\tif_icmpgt " ^ strOfLabel l
  | Jif_icmple l       -> "\tif_icmple " ^ strOfLabel l
  | Jifeq l            -> "\tifeq   " ^ strOfLabel l
  | Jifne l            -> "\tifne   " ^ strOfLabel l
  | Jiflt l            -> "\tiflt   " ^ strOfLabel l
  | Jifge l            -> "\tifge   " ^ strOfLabel l
  | Jifgt l            -> "\tifgt   " ^ strOfLabel l
  | Jifle l            -> "\tifle   " ^ strOfLabel l
  | Jifnonnull l       -> "\tifnonnull " ^ strOfLabel l
  | Jifnull l          -> "\tifnull " ^ strOfLabel l
  | Jiinc (var,const)  -> "\tiinc   " ^ strOfIndex var ^ " " ^ string_of_int const
  | Jiload i           -> "\tiload  " ^ strOfIndex i
  | Jimul              -> "\timul"
  | Jineg              -> "\tineg"
  | Jinstanceof c      -> "\tinstanceof " ^ strOfCref c
  | Jinvokeinterface (c,m,s) -> "\tinvokeinterface " ^ m
  | Jinvokespecial (c,m,s)   -> "\tinvokespecial " ^ m
  | Jinvokestatic (c,m,s)    -> "\tinvokestatic " ^ m
  | Jinvokevirtual (c,m,s)   -> "\tinvokevirtual " ^ m
  | Jior               -> "\tior"
  | Jirem              -> "\tirem"
  | Jishl              -> "\tishl"
  | Jishr              -> "\tishr"
  | Jistore i          -> "\tistore " ^ strOfIndex i
  | Jisub              -> "\tisub"
  | Jiushr             -> "\tiushr"
  | Jixor              -> "\tixor"
  | Jjsr l             -> "\tjsr    " ^ strOfLabel l
  | Jl2d               -> "\tl2d"
  | Jl2f               -> "\tl2f"
  | Jl2i               -> "\tl2i"
  | Jladd              -> "\tladd"
  | Jlaload            -> "\tlaload"
  | Jland              -> "\tland"
  | Jlastore           -> "\tlastore"
  | Jlcmp              -> "\tlcmp"
  | Jlconst c          -> Printf.sprintf "\tlconst %Ld" c
  | Jldiv              -> "\tldiv"
  | Jlload i           -> "\tlload  " ^ strOfIndex i
  | Jlmul              -> "\tlmul"
  | Jlneg              -> "\tlneg"
  | Jlookupswitch (default,cases) -> "\tlookupswitch\n"
                          ^ (List.fold_left
			       (fun s (n,l) ->
				 s ^ "\t"
				 ^ Int32.to_string n ^ ": "
				 ^ strOfLabel l ^ "\n")
			       "" cases)
                          ^ "\tdefault: " ^ strOfLabel default
  | Jlor               -> "\tlor"
  | Jlrem              -> "\tlrem"
  | Jlshl              -> "\tlshl"
  | Jlshr              -> "\tlshr"
  | Jlstore i          -> "\tlstore " ^ strOfIndex i
  | Jlsub              -> "\tlsub"
  | Jlushr             -> "\tlushr"
  | Jlxor              -> "\tlxor"
  | Jmonitorenter      -> "\tmonitorenter"
  | Jmonitorexit       -> "\tmonitorexit"
  | Jnew c             -> "\tnew " ^ Jvmtype.string_of_class c
  | Jnewarray (elem,dim) -> "\tnewarray " (*^ strOfType elem*)
                          ^ " " ^ string_of_int dim
  | Jnop               -> "\tnop"
  | Jpop               -> "\tpop"
  | Jpop2              -> "\tpop2"
  | Jputfield (c,f,t)  -> "\tputfield " ^ f
  | Jputstatic (c,f,t) -> "\tputstatic " ^ f
  | Jret i             -> "\tret   " ^ strOfIndex i
  | Jreturn            -> "\treturn"
  | Jsaload            -> "\tsaload"
  | Jsastore           -> "\tsastore"
  | Jswap              -> "\tswap"
  | Jtableswitch (default,offset,targets)     -> "\ttableswitch "
                         (* ^ Int32.to_string offset
                          ^ " "
                          ^ Int32.to_string (make_key (t.offset, Array.length t.targets))
                          ^ "\n"
                          ^ (Array.fold_left (fun s l -> s ^ "\t" ^ strOfLabel l ^ "\n") ""  t.targets)
                          ^ "\tdefault: "
                          ^ strOfLabel t.t_default*)

let printInstr k = print_string (toString k ^ "\n")

let printInstrs l = List.iter printInstr l
