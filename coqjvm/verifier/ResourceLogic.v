Require Import List.
Require Import OptionExt.
Require Import ListExt.

Require Import ClassDatatypesIface.
Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import CertRuntimeTypesIface.
Require Import Certificates.
Require Import StoreIface.
Require Import ResourceAlgebra.
Require Import AssignabilityIface.
Require Import PreassignabilityIface.
Require Import VirtualMethodLookupIface.
Require Import ResolutionIface.
Require Import VerifierAnnotationsIface.
Require Import AbstractLogic.
Require Import NativeMethodSpec.
Require Import ResourceLogicIface.
Require        FSetInterface.

Module ResourceLogic
        (B    : BASICS)
        (BASESEM : ILL_BASE_SEMANTICS B)
        (SYN0 : ILL_SYNTAX B BASESEM.SYN)
        (CERT : CERTIFICATE         with Definition asn := BASESEM.SYN.formula)
        (AL   : ILL_TYPE B BASESEM.SYN SYN0)
        (ANN  : VERIFIER_ANNOTATIONS B AL CERT)
        (C    : CLASSDATATYPES B ANN.GA.A)
        (CP   : CLASSPOOL B ANN.GA.A C)
        (A    : ASSIGNABILITY B ANN.GA.A C CP)
        (R    : RESOLUTION B ANN.GA.A C CP A)
        (RT   : CERTRUNTIMETYPES B ANN.GA.A C CP A)
        (RSEM : ILL_SEMANTICS B BASESEM SYN0)
        (VM   : VIRTUALMETHODLOOKUP B ANN.GA.A C CP A)
        (PA   : PREASSIGNABILITY B ANN.GA C CP A VM)
        (CLSNM: FSetInterface.S     with Definition E.t := B.Classname.t with Definition E.eq := B.Classname.eq)
        (NTSPC: NATIVE_METHOD_SPEC B ANN.GA.A)
        : RESOURCE_LOGIC B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC.

Import SYN0.
Import RSEM.
Import BASESEM.SYN.
Import BASESEM.
Import RA.
Import CERT.

Definition premethod_spec m := ANN.method_spec (C.premethod_annot m).
Definition method_spec m :=  ANN.method_spec (C.method_annot m).

Section WithPreclasses.

Hypothesis preclasses : CP.Preclasspool.t.
Hypothesis privilegedclasses : CLSNM.t.

Definition safe_override s1 s2 := match s1, s2 with
 | (P, Q, X), (P', Q', X') => 
     (forall r, sat r P' -> sat r P) /\ (forall r, sat r Q -> sat r Q') /\ (forall r, sat r X -> sat r X')
 end.

Lemma safe_override_refl : forall s, safe_override s s.
destruct s as [[P Q] X]. unfold safe_override. auto.
Save.

Lemma safe_override_trans : forall s1 s2 s3,
  safe_override s1 s2 -> safe_override s2 s3 ->
  safe_override s1 s3.
intros [[P1 Q1] X1] [[P2 Q2] X2] [[P3 Q3] X3]. unfold safe_override. firstorder.
Save.

Record constantpool_additional_correct (classes : CP.cert_classpool)
                                       (caller : B.Classname.t)
                                       (cp : C.ConstantPool.t)
                                       (cpa : ANN.ConstantPoolAdditional.t)
                                     : Prop :=
 { cpa_ins_class : forall idx clsnm, 
    C.ConstantPool.lookup cp idx = Some (C.cpe_classref clsnm) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_instantiable_class) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists H,
     R.resolve_class caller clsnm classes preclasses = CP.load_ok _ p oa c H
     /\ C.class_interface c = false
     /\ C.class_abstract c = false
 ; cpa_static_method : forall idx clsnm md mn P Q X,
    C.ConstantPool.lookup cp idx = Some (C.cpe_methodref clsnm mn md) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_static_method P Q X) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists m, exists H,
     R.resolve_method caller clsnm mn md classes preclasses = CP.load_ok _ p oa (c,m) H
     /\ C.method_static m = true
     /\ method_spec m = (P,Q,X)
     /\ C.class_interface c = false
     /\ C.method_abstract m = false (* enforced by the JVM anyway - could adjust Execution.v instead. *)
 ; cpa_static_field : forall idx clsnm fnm ty,
    C.ConstantPool.lookup cp idx = Some (C.cpe_fieldref clsnm fnm ty) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_static_field) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists f, exists H,
     R.resolve_field caller clsnm fnm ty classes preclasses = CP.load_ok _ p oa (c,f) H
     /\ C.field_static f = true
 ; cpa_instance_field : forall idx clsnm fnm ty,
    C.ConstantPool.lookup cp idx = Some (C.cpe_fieldref clsnm fnm ty) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_instance_field) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists f, exists H,
     R.resolve_field caller clsnm fnm ty classes preclasses = CP.load_ok _ p oa (c,f) H
     /\ C.field_static f = false
     /\ C.field_final f = false (* this it to get around the condition in putfield *)
 ; cpa_classref : forall idx clsnm,
    C.ConstantPool.lookup cp idx = Some (C.cpe_classref clsnm) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_classref) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists H,
     R.resolve_class caller clsnm classes preclasses = CP.load_ok _ p oa c H
 ; cpa_instance_special_method : forall idx clsnm md mn P Q X,
    C.ConstantPool.lookup cp idx = Some (C.cpe_methodref clsnm mn md) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_instance_special_method P Q X) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists m, exists H,
     R.resolve_method caller clsnm mn md classes preclasses = CP.load_ok _ p oa (c,m) H
     /\ C.method_abstract m = false
     /\ C.method_static m = false
     /\ method_spec m = (P,Q,X)
     /\ C.class_interface c = false
 ; cpa_instance_method : forall idx clsnm md mn P Q X,
    C.ConstantPool.lookup cp idx = Some (C.cpe_methodref clsnm mn md) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_instance_method P Q X) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists m, exists H,
     R.resolve_method caller clsnm mn md classes preclasses = CP.load_ok _ p oa (c,m) H
     /\ C.method_static m = false
     /\ method_spec m = (P,Q,X)
 ; cpa_interface_method : forall idx clsnm md mn P Q X,
    C.ConstantPool.lookup cp idx = Some (C.cpe_interfacemethodref clsnm mn md) ->
    ANN.ConstantPoolAdditional.lookup cpa idx = Some (ANN.cpae_interface_method P Q X) ->
    exists classes', exists p : CP.preserve_old_classes classes classes', exists oa, exists c, exists m, exists H,
     R.resolve_interface_method caller clsnm mn md classes preclasses = CP.load_ok _ p oa (c,m) H
     /\ C.method_static m = false
     /\ method_spec m = (P,Q,X)
 }.

Implicit Arguments cpa_ins_class [classes caller cp cpa].
Implicit Arguments cpa_static_method [classes caller cp cpa].
Implicit Arguments cpa_static_field [classes caller cp cpa].
Implicit Arguments cpa_instance_field [classes caller cp cpa].
Implicit Arguments cpa_classref [classes caller cp cpa].
Implicit Arguments cpa_instance_special_method [classes caller cp cpa].
Implicit Arguments cpa_instance_method [classes caller cp cpa].
Implicit Arguments cpa_interface_method [classes caller cp cpa].

Section InstructionPrecondition.

Hypothesis cert : Cert.t.
Hypothesis constantpool : C.ConstantPool.t.
Hypothesis ensures : formula.
Hypothesis exceptional_ensures : formula.

Inductive exception_handlers_assertion : nat -> list C.exception_handler -> formula -> Prop :=
| eha_nil : forall pc,
   exception_handlers_assertion pc nil exceptional_ensures
| eha_cons_within : forall pc start_pc end_pc handler_pc catch_type handlers a a',
   pc >= start_pc /\ pc < end_pc ->
   Cert.lookup cert handler_pc = Some a ->
   exception_handlers_assertion pc handlers a' ->
   exception_handlers_assertion pc (C.mkExcHandler start_pc end_pc handler_pc catch_type::handlers) (f_and a a')
| eha_cons_outwith : forall pc start_pc end_pc handler_pc catch_type handlers a,
   pc < start_pc \/ pc >= end_pc ->
   exception_handlers_assertion pc handlers a ->
   exception_handlers_assertion pc (C.mkExcHandler start_pc end_pc handler_pc catch_type::handlers) a.

Hypothesis constantpool_additional : ANN.ConstantPoolAdditional.t.
Hypothesis exception_handlers : list C.exception_handler.

Definition R_tensor c f := match R_new c with None => f | Some a => f_tensor (f_atom a) f end.

Inductive instruction_precondition : C.opcode -> nat -> formula -> Prop :=
 (* Constants *)
| v_iconst : forall pc a z,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition (C.op_iconst z) pc a

 (* Local Variables *)
| v_load : forall pc a ty n,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition (C.op_load ty n) pc a
| v_store : forall pc a ty n,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition (C.op_store ty n) pc a

 (* Arithmetic *)
| v_iarithb : forall pc a op,
   Cert.lookup cert (S pc) = Some a ->
   op = C.iadd \/ op = C.iand \/ op = C.imul \/ op = C.ior \/ op = C.isub \/ op = C.ixor ->
   instruction_precondition (C.op_iarithb op) pc a
| v_iarithu : forall pc a op,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition (C.op_iarithu op) pc a

 (* Control flow *)
| v_if_acmp : forall pc a a' op offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_if_acmp op offset) pc (f_and a a')
| v_if_icmp : forall pc a a' op offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_if_icmp op offset) pc (f_and a a')
| v_if : forall pc a a' op offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_if op offset) pc (f_and a a')
| v_ifnull : forall pc a a' offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_ifnull offset) pc (f_and a a')
| v_ifnonnull : forall pc a a' offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_ifnonnull offset) pc (f_and a a')
| v_goto : forall pc a offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   instruction_precondition (C.op_goto offset) pc a
| v_valreturn : forall pc ty,
   instruction_precondition (C.op_valreturn ty) pc ensures
| v_return : forall pc,
   instruction_precondition C.op_return pc ensures
| v_athrow : forall pc a,
   exception_handlers_assertion pc exception_handlers a ->
   instruction_precondition C.op_athrow pc (f_and a (R_tensor B.java_lang_NullPointerException a))

 (* OO instructions *)
| v_instanceof : forall pc a idx clsnm,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_classref clsnm) ->
   (   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_classref)
    \/ ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instantiable_class)) ->
   instruction_precondition (C.op_instanceof idx) pc a
| v_invokespecial : forall pc a idx a' P Q X clsnm mn md,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_methodref clsnm mn md) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instance_special_method P Q X) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_invokespecial idx) pc (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                                                               (R_tensor B.java_lang_NullPointerException a'))
| v_invokestatic : forall pc a idx a' P Q X clsnm mn md,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_methodref clsnm mn md) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_static_method P Q X) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_invokestatic idx) pc (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
| v_invokevirtual : forall pc a idx a' P Q X clsnm mn md,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_methodref clsnm mn md) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instance_method P Q X) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_invokevirtual idx) pc (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                                                               (f_and (R_tensor B.java_lang_NullPointerException a')
                                                                      (R_tensor B.java_lang_AbstractMethodError a')))
| v_invokeinterface : forall pc a idx a' P Q X clsnm mn md,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_interfacemethodref clsnm mn md) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_interface_method P Q X) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_invokeinterface idx) pc (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                                                               (f_and (R_tensor B.java_lang_NullPointerException a')
                                                                      (f_and (R_tensor B.java_lang_AbstractMethodError a')
                                                                             (R_tensor B.java_lang_IncompatibleClassChangeError a'))))
| v_aconst_null : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition (C.op_aconst_null) pc a
| v_checkcast : forall pc a a' idx clsnm,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_classref clsnm) ->
   (   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_classref)
    \/ ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instantiable_class)) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_checkcast idx) pc (f_and a (R_tensor B.java_lang_ClassCastException a'))
| v_new : forall pc a idx clsnm,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_classref clsnm) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instantiable_class) ->
   instruction_precondition (C.op_new idx) pc (R_tensor clsnm a)
| v_getfield : forall pc a a' idx clsnm fnm ty,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_fieldref clsnm fnm ty) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instance_field) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_getfield idx) pc (f_and a (R_tensor B.java_lang_NullPointerException a'))
| v_getstatic : forall pc a idx clsnm fnm ty,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_fieldref clsnm fnm ty) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_static_field) ->
   instruction_precondition (C.op_getstatic idx) pc a
| v_putfield : forall pc a a' idx clsnm fnm ty,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_fieldref clsnm fnm ty) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_instance_field) ->
   exception_handlers_assertion pc exception_handlers a' ->
   instruction_precondition (C.op_putfield idx) pc (f_and a (R_tensor B.java_lang_NullPointerException a'))
| v_putstatic : forall pc a idx clsnm fnm ty,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_fieldref clsnm fnm ty) ->
   ANN.ConstantPoolAdditional.lookup constantpool_additional idx = Some (ANN.cpae_static_field) ->
   instruction_precondition (C.op_putstatic idx) pc a

 (* Stack Operations *)
| v_dup : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup pc a
| v_dup_x1 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup_x1 pc a
| v_dup_x2 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup_x2 pc a
| v_dup2 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup2 pc a
| v_dup2_x1 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup2_x1 pc a
| v_dup2_x2 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup2_x2 pc a
| v_nop : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_nop pc a
| v_pop : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_pop pc a
| v_pop2 : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_pop2 pc a
| v_swap : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_swap pc a.

End InstructionPrecondition.

Inductive verified_instruction (cp:C.ConstantPool.t)
                               (cpa:ANN.ConstantPoolAdditional.t)
                               (ensures ex_ensures:formula)
                               (cert:CERT.Cert.t)
                               (handlers : list C.exception_handler)
                               (op : C.opcode)
                               (pc : nat) : Prop :=
| mk_verified_instruction : forall a1 a2,
    CERT.Cert.lookup cert pc = Some a1 ->
    instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a2 ->
    implies a1 a2 ->
    verified_instruction cp cpa ensures ex_ensures cert handlers op pc.

Inductive verified_precode (cp : C.ConstantPool.t)
                           (cpa:ANN.ConstantPoolAdditional.t)
                           (ensures ex_ensures : formula)
                           (code : C.precode)
                           (cert : CERT.Cert.t) : Prop :=
| mk_verified_precode :
    (* the certificate only covers the actual code *)
    (forall n a, CERT.Cert.lookup cert n = Some a -> n < length (C.precode_code code)) ->
    (* all the actual instructions are safe *)
    (forall n op, nth_error (C.precode_code code) n = Some op -> 
      verified_instruction cp cpa ensures ex_ensures cert (C.precode_exception_table code) op n) ->
    verified_precode cp cpa ensures ex_ensures code cert.

Inductive verified_code (cp : C.ConstantPool.t)
                        (cpa: ANN.ConstantPoolAdditional.t)
                        (ensures ex_ensures : formula)
                        (code : C.code) 
                        (cert : Cert.t) : Prop :=
| mk_verified_code : 
    (* the certificate only covers the actual code *)
    (forall n a, Cert.lookup cert n = Some a -> n < length (C.code_code code)) ->
    (* all the actual instructions are safe *)
    (forall n op, nth_error (C.code_code code) n = Some op -> 
      verified_instruction cp cpa ensures ex_ensures cert (C.code_exception_table code) op n) ->
    verified_code cp cpa ensures ex_ensures code cert.

Record preclass_verified (classes : CP.cert_classpool)
                         (pc : C.preclass)
                       : Prop :=
 { preclass_verified_cpa_ok  : constantpool_additional_correct classes (C.preclass_name pc) (C.preclass_constantpool pc) (snd (C.preclass_annotation pc))
 ; preclass_verified_methods : (forall md pm,
                                 C.has_premethod (C.preclass_methods pc) md pm ->
                                 (exists code, forall P Q X,
                                 premethod_spec pm = (P, Q, X) ->
                                 exists cert, exists P', exists Q', 
                                   C.premethod_code pm = Some code /\
                                      ((exists g, ANN.grants (C.premethod_annot pm) = Some g /\ CLSNM.In (C.preclass_name pc) privilegedclasses /\ Q' = AL.given_resexpr_have g Q)
                                        \/ (ANN.grants (C.premethod_annot pm) = None /\ Q' = Q))
                                   /\ verified_precode (C.preclass_constantpool pc) (snd (C.preclass_annotation pc)) Q' X code cert
                                   /\ (forall r, sat r P -> sat r P')
                                   /\ Cert.lookup cert 0 = Some P') \/
(* TO DO: should be check that the method is declared native rather than abstract? *)
                                 (C.premethod_code pm = None /\
                                   (C.premethod_abstract pm = true \/
                                     (NTSPC.SpecTable.MapsTo (C.preclass_name pc, C.premethod_name pm) (C.premethod_annot pm) NTSPC.table /\
                                     (CLSNM.In (C.preclass_name pc) privilegedclasses \/ ANN.grants (C.premethod_annot pm) = None)))))
 ; preclass_verified_overrides_classes1 :
                               forall cB nmB mA mB md,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 CP.class_loaded classes nmB cB ->
                                 PA.pc_cross_sub_class classes preclasses (C.preclass_name pc) nmB ->
                                 C.class_interface cB = false ->
                                 C.has_premethod (C.preclass_methods pc) md mA ->
                                 C.MethodList.lookup (C.class_methods cB) md = Some mB ->
                                 C.premethod_static mA = false ->
                                 C.method_static mB = false ->
                                 safe_override (premethod_spec mA) (method_spec mB)
 ; preclass_verified_overrides_classes2 :
                               forall cB nmB mA mB md,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 CP.Preclasspool.lookup preclasses nmB = Some cB ->
                                 (forall cB', ~CP.class_loaded classes nmB cB') ->
                                 PA.pc_sub_class classes preclasses (C.preclass_name pc) nmB ->
                                 C.preclass_interface cB = false ->
                                 C.has_premethod (C.preclass_methods pc) md mA ->
                                 C.has_premethod (C.preclass_methods cB) md mB ->
                                 C.premethod_static mA = false ->
                                 C.premethod_static mB = false ->
                                 safe_override (premethod_spec mA) (premethod_spec mB)
 ; preclass_verified_implements :
                               forall iface md ispec,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 PA.should_implement classes preclasses (C.preclass_name pc) iface ->
                                 PA.interface_reqs_method classes preclasses iface md ispec ->
                                 exists mspec,
                                   PA.minimal_methodspec classes preclasses (C.preclass_name pc) md mspec /\
                                   safe_override mspec ispec
 }.

Definition method_grants_ok (classname : B.Classname.t) (method : C.method) (Q':formula) :=
  let Q := snd (fst (method_spec method)) in
  (exists g, ANN.grants (C.method_annot method) = Some g /\ CLSNM.In classname privilegedclasses /\ Q' = AL.given_resexpr_have g Q)
    \/ (ANN.grants (C.method_annot method) = None /\ Q' = Q).

Record class_verified (classes : CP.cert_classpool)
                      (class : C.class)
                    : Prop :=
 { class_verified_cpa     : ANN.ConstantPoolAdditional.t
 ; class_verified_cpa_ok  : constantpool_additional_correct classes (C.class_name class) (C.class_constantpool class) class_verified_cpa
 ; class_verified_methods : (forall md m,
                               C.MethodList.lookup (C.class_methods class) md = Some m ->
                               (exists code, forall P Q X, 
                               method_spec m = (P, Q, X) ->
                               exists cert, exists P', exists Q',
                                 C.method_code m = Some code
                                /\ method_grants_ok (C.class_name class) m Q'
                                /\ verified_code (C.class_constantpool class) class_verified_cpa Q' X code cert
                                /\ (forall r, sat r P -> sat r P')
                                /\ Cert.lookup cert 0 = Some P') \/
(* TO DO: should be check that the method is declared native rather than abstract? *)
                               (C.method_code m = None /\
                                 (C.method_abstract m = true \/
                                   (NTSPC.SpecTable.MapsTo (C.class_name class, C.method_name m) (C.method_annot m) NTSPC.table /\
                                     (CLSNM.In (C.class_name class) privilegedclasses \/ ANN.grants (C.method_annot m) = None)))))
 ; class_verified_overrides_classes :
                            forall cB nmB md mA mB,
                              fst md <> B.init ->
                              C.class_interface class = false ->
                              CP.class_loaded classes nmB cB ->
                              A.assignable classes (C.ty_obj (C.class_name class)) (C.ty_obj nmB) ->
                              C.class_interface cB = false ->
                              C.MethodList.lookup (C.class_methods class) md = Some mA ->
                              C.MethodList.lookup (C.class_methods cB) md = Some mB ->
                              C.method_static mA = false ->
                              C.method_static mB = false ->
                              safe_override (method_spec mA) (method_spec mB)
 ; class_verified_implements_interfaces :
                            forall cI nmI md mI nmB cB mB,
                              fst md <> B.init ->
                              C.class_interface class = false ->
                              CP.class_loaded classes nmI cI ->
                              A.assignable classes (C.ty_obj (C.class_name class)) (C.ty_obj nmI) ->
                              C.class_interface cI = true ->
                              C.MethodList.lookup (C.class_methods cI) md = Some mI ->
                              CP.class_loaded classes nmB cB ->
                              A.assignable classes (C.ty_obj (C.class_name class)) (C.ty_obj nmB) ->
                              C.class_interface cB = false ->
                              C.MethodList.lookup (C.class_methods cB) md = Some mB ->
                              C.method_static mB = false ->
                              VM.lookup_minimal classes (C.class_name class) nmB md ->
                              safe_override (method_spec mB) (method_spec mI)
 }.

Definition all_classes_verified :=
  fun classes =>
    forall cnm class,
      CP.class_loaded classes cnm class ->
      C.class_interface class = false ->
      class_verified classes class.

Definition all_preclasses_verified :=
  fun classes =>
    forall cnm pc,
      CP.Preclasspool.lookup preclasses cnm = Some pc ->
      C.preclass_interface pc = false ->
      (forall c, ~CP.class_loaded classes cnm c) ->
      preclass_verified classes pc.


Inductive safe_frame_stack_rest (classes : CP.cert_classpool)
                         : list RT.frame -> formula -> formula -> res -> Prop :=
| safe_stack_nil  : forall ensures exsures,
   safe_frame_stack_rest classes nil ensures exsures e
| safe_stack_cons : forall fs ensures_internal ensures exsures caller_allowance class method code cert pc next_assertion ex_assertion callee_ensures callee_exsures total_allowance lvars stk this_allowance cpa,
   safe_frame_stack_rest classes fs ensures exsures caller_allowance ->
   verified_code (C.class_constantpool class) cpa ensures_internal exsures code cert ->
   constantpool_additional_correct classes (C.class_name class) (C.class_constantpool class) cpa ->
   Cert.lookup cert (S pc) = Some next_assertion ->
   exception_handlers_assertion cert exsures pc (C.code_exception_table code) ex_assertion ->
   (forall r, sat r callee_ensures -> sat (this_allowance :*: r) next_assertion) ->
   (forall r, sat r callee_exsures -> sat (this_allowance :*: r) ex_assertion) ->
   this_allowance :*: caller_allowance <: total_allowance ->
   method_grants_ok (C.class_name class) method ensures_internal ->
   snd (fst (method_spec method)) = ensures ->
   safe_frame_stack_rest classes (RT.mkFrame stk lvars pc code method class::fs) callee_ensures callee_exsures total_allowance.

Inductive safe_frame_stack : CP.cert_classpool -> list RT.frame -> RA.res -> Prop :=
 mk_safe_current_frame : forall classes stk lvars class method code pc this_allowance cert pre_condition ensures_internal ensures ex_ensures caller_allowance total_allowance fs cpa,
  verified_code (C.class_constantpool class) cpa ensures_internal ex_ensures code cert ->
  constantpool_additional_correct classes (C.class_name class) (C.class_constantpool class) cpa ->
  Cert.lookup cert pc = Some pre_condition ->
  sat this_allowance pre_condition ->
  this_allowance :*: caller_allowance <: total_allowance ->
  method_grants_ok (C.class_name class) method ensures_internal ->
  snd (fst (method_spec method)) = ensures ->
  safe_frame_stack_rest classes fs ensures ex_ensures caller_allowance ->
  safe_frame_stack classes (RT.mkFrame stk lvars pc code method class::fs) total_allowance.

Inductive safe_state : RT.pre_state RA.res -> Prop :=
 mk_safe_state : forall fs classes heap static_fields total_allowance current_allowance consumed,
  consumed :*: current_allowance <: total_allowance ->
  safe_frame_stack classes fs current_allowance ->
  all_classes_verified classes ->
  all_preclasses_verified classes ->
  safe_state (RT.mkState fs classes heap static_fields consumed total_allowance).

Inductive safe_allowance_change : RT.pre_state RA.res -> RT.pre_state RA.res -> Prop :=
  no_allowance_change : forall s s',
    RT.state_reslimit _ s = RT.state_reslimit _ s' ->
    safe_allowance_change s s'
| priv_allowance_change : forall fsh fst classes heap static_fields consumed total_allowance s',
    CLSNM.In (C.class_name (RT.frame_class fsh)) privilegedclasses ->
    safe_allowance_change (RT.mkState (fsh::fst) classes heap static_fields consumed total_allowance) s'.

End WithPreclasses.

End ResourceLogic.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)
