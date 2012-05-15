Require Import ClassDatatypesIface.
Require Import ILL.ILLInterfaces.
Require Import BasicMachineTypes.
Require Import OptionExt.
Require Import ClasspoolIface.
Require Import CertRuntimeTypesIface.
Require Import List.
Require Import Certificates.
Require Import ResourceAlgebra.
Require Import AssignabilityIface.
Require Import PreassignabilityIface.
Require Import VirtualMethodLookupIface.
Require Import ResolutionIface.
Require Import VerifierAnnotationsIface.
Require Import AbstractLogic.
Require Import VCs.
Require Import NativeMethodSpec.
Require ResourceLogic.
Require Import ErrorMonad.
Require Import ErrorMessages.
Require Import MLStrings.
Require OptionMonad.
Require GenericVerifier.
Require GenericOverrideChecker.
Require Import Bool.
Require SetoidList.
Require FSetInterface.
Require FMapCombine.
Require OrderedType.

Module ResourceChecker
        (RC_B    : BASICS)
        (BASESEM : ILL_BASE_SEMANTICS  RC_B)
        (   SYN0 : ILL_SYNTAX          RC_B BASESEM.SYN)
        (RC_CERT : CERTIFICATE         with Definition asn := BASESEM.SYN.formula)
        (   ILL  : ILL_TYPE            RC_B BASESEM.SYN SYN0)
        (RC_ANN  : VERIFIER_ANNOTATIONS RC_B ILL RC_CERT)
        (RC_C    : CLASSDATATYPES      RC_B RC_ANN.GA.A)
        (RC_CP   : CLASSPOOL           RC_B RC_ANN.GA.A RC_C)
        (   A    : ASSIGNABILITY       RC_B RC_ANN.GA.A RC_C RC_CP)
        (   R    : RESOLUTION          RC_B RC_ANN.GA.A RC_C RC_CP A)
        (   RT   : CERTRUNTIMETYPES    RC_B RC_ANN.GA.A RC_C RC_CP A)
        (   RSEM : ILL_SEMANTICS       RC_B BASESEM SYN0)
        (   VM   : VIRTUALMETHODLOOKUP RC_B RC_ANN.GA.A RC_C RC_CP A)
        (   PA   : PREASSIGNABILITY RC_B RC_ANN.GA RC_C RC_CP A VM)
        (   CLSNM: FSetInterface.S     with Definition E.t := RC_B.Classname.t with Definition E.eq := RC_B.Classname.eq)
        (   NTSPC: NATIVE_METHOD_SPEC RC_B RC_ANN.GA.A)
        (   VCs  : VERIFICATION_CONDITIONS RC_B ILL).

Module Logic := ResourceLogic.ResourceLogic RC_B BASESEM SYN0 RC_CERT ILL RC_ANN RC_C RC_CP A R RT RSEM VM PA CLSNM NTSPC.

Module DUMMY.
End DUMMY.

(* In this module:
   [DONE] copy over the checker from ResCodeVerifierBase and GenericVerifier (try to think of a way of keeping the verifier generic)
   [DONE] get the stuff from VirtualMethods to do checking of super class overriding (need to think about <init> methods)
   [DONE] write something to do checking of resolving of stuff in the classpool (constant_pool_additional)
   *)

Module ResCodeVerifierBase.

Import RC_CERT.
Import BASESEM.SYN.

Definition instruction_precondition := Logic.instruction_precondition.

Fixpoint get_exception_assertion (cert : Cert.t) (exceptional_ensures:formula) (pc : nat) (l : list RC_C.exception_handler) {struct l} : error_monad formula :=
  match l with
  | nil => ret exceptional_ensures
  | (RC_C.mkExcHandler start_pc end_pc handler_pc _)::t =>
      a' <- get_exception_assertion cert exceptional_ensures pc t;:
      if RC_C.is_within start_pc end_pc pc
        then a <- tagoptfail err_poorcert (Cert.lookup cert handler_pc);:
             ret (f_and a a')
        else ret a'
  end.

Definition get_instruction_precondition :
  RC_CERT.Cert.t ->
  RC_C.ConstantPool.t ->
  formula ->
  formula ->
  RC_ANN.ConstantPoolAdditional.t ->
  list RC_C.exception_handler ->
  RC_C.opcode ->
  nat ->
  error_monad formula
:=
fun cert cp ensures ex_ensures cpa handlers op pc =>
let lookup := fun loc => tagoptfail (err_poorcert mlapp (mlstring_of_nat pc)) (Cert.lookup cert loc) in
let pc_plus_offset := fun offset => tagoptfail (err_badoffset mlapp (mlstring_of_nat pc)) (RC_C.pc_plus_offset pc offset) in
let fail := fun msg => fail (msg mlapp (mlstring_of_nat pc)) in
match op with
| RC_C.op_iconst z => lookup (S pc)

| RC_C.op_load ty n => lookup (S pc)
| RC_C.op_store ty n => lookup (S pc)

| RC_C.op_iarithb op =>
  match op with
    | RC_C.iadd => lookup (S pc)
    | RC_C.iand => lookup (S pc)
    | RC_C.imul => lookup (S pc)
    | RC_C.ior => lookup (S pc)
    | RC_C.isub => lookup (S pc)
    | RC_C.ixor => lookup (S pc)
    | _ => fail err_unsupported
  end
| RC_C.op_iarithu op => lookup (S pc)

| RC_C.op_if_acmp op offset =>
  target <- pc_plus_offset offset;:
  a <- lookup target;:
  a' <- lookup (S pc);:
  ret (f_and a a')
| RC_C.op_if_icmp op offset =>
  target <- pc_plus_offset offset;:
  a <- lookup target;:
  a' <- lookup (S pc);:
  ret (f_and a a')
| RC_C.op_if op offset =>
  target <- pc_plus_offset offset;:
  a <- lookup target;:
  a' <- lookup (S pc);:
  ret (f_and a a')
| RC_C.op_ifnull offset =>
  target <- pc_plus_offset offset;:
  a <- lookup target;:
  a' <- lookup (S pc);:
  ret (f_and a a')
| RC_C.op_ifnonnull offset =>
  target <- pc_plus_offset offset;:
  a <- lookup target;:
  a' <- lookup (S pc);:
  ret (f_and a a')
| RC_C.op_goto offset =>
  target <- pc_plus_offset offset;:
  lookup target
| RC_C.op_valreturn ty => ret ensures
| RC_C.op_return => ret ensures
| RC_C.op_athrow =>
  a <- get_exception_assertion cert ex_ensures pc handlers;:
  ret (f_and a (Logic.R_tensor RC_B.java_lang_NullPointerException a))

| RC_C.op_instanceof idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_classref _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_classref => ret a
      | Some RC_ANN.cpae_instantiable_class => ret a
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_invokespecial idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_methodref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some (RC_ANN.cpae_instance_special_method P Q X) =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                          (Logic.R_tensor RC_B.java_lang_NullPointerException a'))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_invokestatic idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_methodref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some (RC_ANN.cpae_static_method P Q X) =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_invokevirtual idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_methodref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some (RC_ANN.cpae_instance_method P Q X) =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                                                        (f_and (Logic.R_tensor RC_B.java_lang_NullPointerException a')
                                                                   (Logic.R_tensor RC_B.java_lang_AbstractMethodError a')))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_invokeinterface idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_interfacemethodref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some (RC_ANN.cpae_interface_method P Q X) =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_and (f_tensor P (f_and (f_lolli Q a) (f_lolli X a')))
                                                        (f_and (Logic.R_tensor RC_B.java_lang_NullPointerException a')
                                                                   (f_and (Logic.R_tensor RC_B.java_lang_AbstractMethodError a')
                                                                          (Logic.R_tensor RC_B.java_lang_IncompatibleClassChangeError a'))))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_aconst_null => lookup (S pc)
| RC_C.op_checkcast idx =>
  a <- lookup (S pc);:
  a' <- get_exception_assertion cert ex_ensures pc handlers;:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_classref _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_classref => ret (f_and a (Logic.R_tensor RC_B.java_lang_ClassCastException a'))
      | Some RC_ANN.cpae_instantiable_class => ret (f_and a (Logic.R_tensor RC_B.java_lang_ClassCastException a'))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_new idx =>
  a <- lookup (S pc);:
  match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_classref clsnm) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_instantiable_class =>
          ret (Logic.R_tensor clsnm a)
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_getfield idx =>
  a <- lookup (S pc);:
 match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_fieldref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_instance_field =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_and a (Logic.R_tensor RC_B.java_lang_NullPointerException a'))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_getstatic idx =>
  a <- lookup (S pc);:
 match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_fieldref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_static_field =>
          ret a
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_putfield idx =>
  a <- lookup (S pc);:
 match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_fieldref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_instance_field =>
          a' <- get_exception_assertion cert ex_ensures pc handlers;:
          ret (f_and a (Logic.R_tensor RC_B.java_lang_NullPointerException a'))
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| RC_C.op_putstatic idx =>
  a <- lookup (S pc);:
 match RC_C.ConstantPool.lookup cp idx with
  | Some (RC_C.cpe_fieldref _ _ _) =>
      match RC_ANN.ConstantPoolAdditional.lookup cpa idx with
      | Some RC_ANN.cpae_static_field =>
          ret a
      | _ => fail err_missingcpainfo
      end
  | _ => fail err_missingcpinfo
  end
| (RC_C.op_dup | RC_C.op_dup_x1 | RC_C.op_dup_x2
  | RC_C.op_dup2 | RC_C.op_dup2_x1 | RC_C.op_dup2_x2
  | RC_C.op_nop | RC_C.op_pop | RC_C.op_pop2 | RC_C.op_swap) => lookup (S pc)

| _ => fail err_unsupported
end.

Hint Constructors Logic.instruction_precondition.
Hint Resolve cert_incl_lookup.

Lemma get_exception_assertion_sound : forall cert ex_ensures handlers pc a,
  get_exception_assertion cert ex_ensures pc handlers = Val a ->
  Logic.exception_handlers_assertion cert ex_ensures pc handlers a.
Proof.
induction handlers as [| h].
intros pc a get.

simpl in get. inject_err get. rewrite <- get.
apply Logic.eha_nil.

intros pc a get.
destruct h. simpl in get.
destruct_err (get_exception_assertion cert ex_ensures pc handlers) get a' rec.
destruct (RC_C.is_within exc_start_pc exc_end_pc pc) as [pcin | pcout].
destruct_err (tagoptfail err_poorcert (Cert.lookup cert exc_handler_pc)) get a'' certlookup.
inject_opttag certlookup.
inject_err get. rewrite <- get.
apply Logic.eha_cons_within. apply pcin. apply certlookup. apply IHhandlers. apply rec.

apply Logic.eha_cons_outwith. apply pcout. apply IHhandlers.
inject_err get. rewrite <- get. apply rec.
Save.

Hint Resolve get_exception_assertion_sound.

Lemma get_instruction_precondition_sound : forall cert cp ensures ex_ensures cpa handlers op pc a,
  get_instruction_precondition cert cp ensures ex_ensures cpa handlers op pc = Val a ->
  instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a.
Proof.
change instruction_precondition with Logic.instruction_precondition.
intros until a. intro precond.
destruct op; simpl in precond;
first [ (* None cases *)
        discriminate

        (* oo instructions *)
      | destruct_opttag precond a' pclookup;
        try (destruct_err (get_exception_assertion cert ex_ensures pc handlers) precond a'' exass);
        OptionMonad.destruct_opt (RC_C.ConstantPool.lookup cp t) precond c cplookup;
        destruct c; try discriminate;
        OptionMonad.destruct_opt (RC_ANN.ConstantPoolAdditional.lookup cpa t) precond add cpalookup;
        destruct add; try discriminate;
        try (destruct_err (get_exception_assertion cert ex_ensures pc handlers) precond a'' exass);
        inject_err precond; rewrite <- precond

        (* branching instructions *)
      | destruct_opttag precond r_target pcplusoff;
        destruct_opttag precond r_a targlook;
        destruct_opttag precond r_a' pclook;
        inject_err precond; rewrite <- precond

        (* goto *)
      | destruct_opttag precond r_target pcplusoff

        (* returns *)
      | inject_err precond; rewrite <- precond

        (* athrow *)
      | destruct_err (get_exception_assertion cert ex_ensures pc handlers) precond a' get_ex

        (* integer bop *)
      | destruct i; try discriminate

        (* trivial instructions *)
      | idtac
      ]; first [inject_err precond; rewrite <- precond| inject_opttag precond| idtac]; eauto 7.
Save.

Lemma cert_incl_exception_handlers : forall cert cert' ex_ensures pc handlers a,
  RC_CERT.cert_incl cert cert' ->
  Logic.exception_handlers_assertion cert  ex_ensures pc handlers a ->
  Logic.exception_handlers_assertion cert' ex_ensures pc handlers a.
Proof.
intros until handlers.
induction handlers; intros a1 cincl hyp;
inversion hyp.
apply Logic.eha_nil.
apply Logic.eha_cons_within; try assumption.
apply cert_incl_lookup with (c1:=cert); assumption.
apply IHhandlers; assumption.
apply Logic.eha_cons_outwith. assumption.
apply IHhandlers; assumption.
Save.

Hint Resolve cert_incl_exception_handlers.

Lemma cert_incl_instruction_precondition : forall cert cert' cp ensures ex_ensures cpa handlers op pc a,
  RC_CERT.cert_incl cert cert' ->
  instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a ->
  instruction_precondition cert' cp ensures ex_ensures cpa handlers op pc a.
Proof.
change instruction_precondition with Logic.instruction_precondition.
intros until a.
intros cincl hyp.
destruct hyp; eauto.
Save.

End ResCodeVerifierBase.

Module VCCombine := FMapCombine.FMapCombine VCs.VerificationConditions.
Definition vcset_union := VCCombine.combine (List.app (A:=VCs.vc_source)).

Module ResOverrideChecker <: GenericOverrideChecker.OVERRIDECHECKERBASE RC_B RC_ANN.GA RC_C RC_CP.

Definition vcset := VCs.vcset.
Definition vcset_empty := VCs.VerificationConditions.empty VCs.vc_sources.
Definition vcset_ok (vcs:vcset) := forall f f', VCs.VerificationConditions.In (f,f') vcs -> SYN0.implies f f'.
Definition vcset_union := vcset_union.
Lemma vcset_union_ok1 : forall vcs vcs', vcset_ok (vcset_union vcs vcs') -> vcset_ok vcs.
Proof.
intros vcs vcs' union_ok f f' invcs.
apply union_ok.
unfold vcset_union.
unfold ResourceChecker.vcset_union.
apply VCCombine.combine_3.
assumption.
Qed.
Lemma vcset_union_ok2 : forall vcs vcs', vcset_ok (vcset_union vcs vcs') -> vcset_ok vcs'.
Proof.
intros vcs vcs' union_ok f f' invcs.
apply union_ok.
unfold vcset_union.
unfold ResourceChecker.vcset_union.
apply VCCombine.combine_4.
assumption.
Qed.
Lemma vcset_union_ok3 : forall vcs vcs', vcset_ok vcs -> vcset_ok vcs' -> vcset_ok (vcset_union vcs vcs').
Proof.
intros vcs vcs' ok ok' f f' inunion.
unfold vcset_union in inunion.
unfold ResourceChecker.vcset_union in inunion.
destruct (VCCombine.combine_2 (f,f') _ _ inunion); auto.
Qed.

Definition safe_override : RC_ANN.method_specification -> RC_ANN.method_specification -> Prop := Logic.safe_override.

Definition safe_override_refl := Logic.safe_override_refl.

Definition safe_override_trans := Logic.safe_override_trans.

Definition check_override (src:RC_B.Classname.t*RC_B.Methodname.t) (ca:RC_ANN.class_annotation) (s1 s2:RC_ANN.method_specification) : error_monad vcset :=
  match src with (src_cls, src_mth) =>
  let src := VCs.vc_override src_cls src_mth in
  match s1, s2 with
    | ((P1, Q1), X1), ((P2, Q2), X2) =>
      ret (VCs.add_vc (VCs.add_vc (VCs.add_vc
        vcset_empty (P2,P1) src) (Q1,Q2) src) (X1,X2) src)
  end
  end.

Module VCFacts := OrderedType.OrderedTypeFacts VCs.VerificationConditions.E.

Lemma vc_add_in_1 : forall elt x y s m,
  VCs.VerificationConditions.E.eq x y ->
  VCs.VerificationConditions.In (elt:=elt) x (VCs.VerificationConditions.add y s m).
Proof.
  intros.
  exists s.
  apply VCs.VerificationConditions.add_1.
  apply VCs.VerificationConditions.E.eq_sym.
  assumption.
Qed.

Lemma vc_add_in_2 : forall elt x y s m,
  VCs.VerificationConditions.In (elt:=elt) x m ->
  VCs.VerificationConditions.In (elt:=elt) x (VCs.VerificationConditions.add y s m).
Proof.
  intros elt x y s m [s' maps].
  destruct (VCFacts.eq_dec y x).
    exists s.
    apply VCs.VerificationConditions.add_1.
    assumption.

    exists s'.
    apply VCs.VerificationConditions.add_2; auto.
Qed.

Lemma check_override_ok : forall src ca s1 s2 vcs,
  check_override src ca s1 s2 = Val vcs ->
  vcset_ok vcs ->
  safe_override s1 s2.
intros [srccls srcmth] ca [[P1 Q1] X1] [[P2 Q2] X2] vcs check_code vcs_ok.
simpl in check_code.
inject_err check_code.
assert (p2p1 : VCs.VerificationConditions.In (VCs.simplify_vc (P2,P1)) vcs).
  subst vcs. unfold VCs.add_vc. 
  do 2 apply vc_add_in_2.
  apply vc_add_in_1.
  apply VCs.VerificationConditions.E.eq_refl.
assert (q1q2 : VCs.VerificationConditions.In (VCs.simplify_vc (Q1,Q2)) vcs).
  subst vcs. unfold VCs.add_vc. 
  apply vc_add_in_2.
  apply vc_add_in_1.
  apply VCs.VerificationConditions.E.eq_refl.
assert (x1x2 : VCs.VerificationConditions.In (VCs.simplify_vc (X1,X2)) vcs).
  subst vcs. unfold VCs.add_vc. 
  apply vc_add_in_1.
  apply VCs.VerificationConditions.E.eq_refl.
assert (ok : forall f f', VCs.VerificationConditions.In (VCs.simplify_vc (f,f')) vcs -> SYN0.implies f f').
  intros.
  unfold vcset_ok in vcs_ok.
  unfold VCs.simplify_vc in H.
  apply vcs_ok in H.
  eapply SYN0.implies_trans.
    apply (proj1 (ILL.simplify_ok f)).
    eapply SYN0.implies_trans.
      apply H.
      apply (proj2 (ILL.simplify_ok f')).
apply ok in p2p1.
apply ok in q1q2.
apply ok in x1x2.

unfold safe_override. unfold Logic.safe_override. intuition eauto using RSEM.implies_soundness.
Qed.

End ResOverrideChecker.

Module MethodVerifier := GenericVerifier.MkCodeVerifier RC_B ILL RC_CERT RC_ANN RC_C ResCodeVerifierBase NTSPC VCs.
Module OverrideChecker := GenericOverrideChecker.GenericOverrideChecker RC_B RC_ANN.GA RC_C RC_CP A ResOverrideChecker VM PA.

Module DUMMY2.
End DUMMY2.

Definition check_spec_eq :=
  fun spec spec' =>
    match (spec,spec') with ((P,Q,X),(P',Q',X')) =>
      match BASESEM.SYN.formula_eq_dec P P' with
        | left _ =>
          match BASESEM.SYN.formula_eq_dec Q Q' with
            | left _ =>
              match BASESEM.SYN.formula_eq_dec X X' with
                | left _ => true
                | _ => false
              end
            | _ => false
          end
        | _ => false
      end
    end.

Lemma check_spec_eq_eq : forall spec spec', check_spec_eq spec spec' = true -> spec = spec'.
Proof.
  intros [[P Q] X] [[P' Q'] X'] H.
  unfold check_spec_eq in H.
  destruct (BASESEM.SYN.formula_eq_dec P P'); [|discriminate].
  destruct (BASESEM.SYN.formula_eq_dec Q Q'); [|discriminate].
  destruct (BASESEM.SYN.formula_eq_dec X X'); [|discriminate].
  subst.
  reflexivity.
Qed.

Definition check_constantpool_additional 
  (classes    : RC_CP.cert_classpool)
  (preclasses : RC_CP.Preclasspool.t)
  (cp         : RC_C.ConstantPool.t)
  (cpa        : RC_ANN.ConstantPoolAdditional.t)
  (caller     : RC_B.Classname.t)
  : error_monad unit
  := check_list (fun cpa_pair =>
    match cpa_pair with (key,cpav) =>
      tagboolfail (err_cpae_bad mlapp (RC_B.ConstantPoolRef.to_string key))
      (match RC_C.ConstantPool.lookup cp key with
         | None => true
         | Some cpv =>
           match (cpv,cpav) with
             | (RC_C.cpe_classref clsnm, RC_ANN.cpae_instantiable_class) =>
               match R.resolve_class caller clsnm classes preclasses with
                 | RC_CP.load_ok _ _ _ c _ => negb (RC_C.class_interface c || RC_C.class_abstract c)
                 | _ => false
               end
             | (RC_C.cpe_methodref clsnm mn md, RC_ANN.cpae_static_method P Q X) =>
               match R.resolve_method caller clsnm mn md classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,m) _ =>
                   check_spec_eq (RC_ANN.method_spec (RC_C.method_annot m)) (P,Q,X) &&
                   RC_C.method_static m && negb (RC_C.class_interface c) && negb (RC_C.method_abstract m)
                 | _ => false
               end
             | (RC_C.cpe_fieldref clsnm fnm ty, RC_ANN.cpae_static_field) =>
               match R.resolve_field caller clsnm fnm ty classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,f) _ => RC_C.field_static f
                 | _ => false
               end
             | (RC_C.cpe_fieldref clsnm fnm ty, RC_ANN.cpae_instance_field) =>
               match R.resolve_field caller clsnm fnm ty classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,f) _ => negb (RC_C.field_static f || RC_C.field_final f)
                 | _ => false
               end
             | (RC_C.cpe_classref clsnm, RC_ANN.cpae_classref) =>
               match R.resolve_class caller clsnm classes preclasses with
                 | RC_CP.load_ok _ _ _ c _ => true
                 | _ => false
               end
             | (RC_C.cpe_methodref clsnm mn md, RC_ANN.cpae_instance_special_method P Q X) =>
               match R.resolve_method caller clsnm mn md classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,m) _ =>
                   check_spec_eq (RC_ANN.method_spec (RC_C.method_annot m)) (P,Q,X) &&
                   negb (RC_C.class_interface c || RC_C.method_abstract m || RC_C.method_static m)
                 | _ => false
               end
             | (RC_C.cpe_methodref clsnm mn md, RC_ANN.cpae_instance_method P Q X) =>
               match R.resolve_method caller clsnm mn md classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,m) _ =>
                     check_spec_eq (RC_ANN.method_spec (RC_C.method_annot m)) (P,Q,X) && negb (RC_C.method_static m)
                 | _ => false
               end
             | (RC_C.cpe_interfacemethodref clsnm mn md, RC_ANN.cpae_interface_method P Q X) =>
               match R.resolve_interface_method caller clsnm mn md classes preclasses with
                 | RC_CP.load_ok _ _ _ (c,m) _ =>
                     check_spec_eq (RC_ANN.method_spec (RC_C.method_annot m)) (P,Q,X) && negb (RC_C.method_static m)
                 | _ => false
               end
             | _ => true
           end
       end) end) (RC_ANN.ConstantPoolAdditional.elements cpa).

Lemma check_constantpool_additional_ok : forall classes preclasses cp cpa caller,
  check_constantpool_additional classes preclasses cp cpa caller = Val tt ->
  Logic.constantpool_additional_correct preclasses classes caller cp cpa.
Proof.
  intros.
  unfold check_constantpool_additional in H.
  split; intros;
  apply RC_ANN.ConstantPoolAdditional.elements_1 in H1;
  destruct (proj1 (SetoidList.InA_alt _ _ _) H1) as [[xk xv] [[xkeq xveq] inlist]];
  simpl in xkeq, xveq;
  rewrite <- xkeq in *;
  subst xv;
  [ apply check_list_ok with (v:=(idx,RC_ANN.cpae_instantiable_class)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_static_method P Q X)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_static_field)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_instance_field)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_classref)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_instance_special_method P Q X)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_instance_method P Q X)) in H; [|assumption]
  | apply check_list_ok with (v:=(idx,RC_ANN.cpae_interface_method P Q X)) in H; [|assumption]
  ];
  inject_booltag H;
  rewrite H0 in H;
  [ destruct (R.resolve_class caller clsnm classes preclasses); [|discriminate]
  | destruct (R.resolve_method caller clsnm mn md classes preclasses); [|discriminate]
  | destruct (R.resolve_field caller clsnm fnm ty classes preclasses); [|discriminate]
  | destruct (R.resolve_field caller clsnm fnm ty classes preclasses); [|discriminate]
  | destruct (R.resolve_class caller clsnm classes preclasses); [|discriminate]
  | destruct (R.resolve_method caller clsnm mn md classes preclasses); [|discriminate]
  | destruct (R.resolve_method caller clsnm mn md classes preclasses); [|discriminate]
  | destruct (R.resolve_interface_method caller clsnm mn md classes preclasses); [|discriminate]
  ];
  exists classes'; exists p; exists o.
    exists a; exists c.
    rewrite negb_orb in H.
    apply andb_prop in H.
    destruct H.
    symmetry in H, H2.
    apply negb_sym in H.
    apply negb_sym in H2.
    simpl in H, H2.
    repeat split; auto.

    destruct a as [cl m].
    exists cl; exists m; exists a0.
    repeat (apply andb_prop in H; destruct H).
    symmetry in H2, H3; apply negb_sym in H2; apply negb_sym in H3; simpl in H2, H3.
    repeat split; auto using check_spec_eq_eq.

    destruct a as [cl f].
    exists cl; exists f; exists a0.
    auto.

    destruct a as [cl f].
    exists cl; exists f; exists a0.
    rewrite negb_orb in H.
    apply andb_prop in H.
    destruct H.
    symmetry in H, H2.
    apply negb_sym in H; apply negb_sym in H2.
    simpl in H, H2.
    auto.

    exists a; exists c.
    auto.

    destruct a as [cl m].
    exists cl; exists m; exists a0.
    repeat (rewrite negb_orb in H).
    apply andb_prop in H; destruct H.
    repeat (apply andb_prop in H2; destruct H2).
    symmetry in H2, H4, H3; apply negb_sym in H2; apply negb_sym in H4; apply negb_sym in H3; simpl in H2,H4,H3.
    repeat split; auto using check_spec_eq_eq.

    destruct a as [cl m].
    exists cl; exists m; exists a0.
    apply andb_prop in H; destruct H.
    symmetry in H2; apply negb_sym in H2; simpl in H2.
    repeat split; auto using check_spec_eq_eq.

    destruct a as [cl m].
    exists cl; exists m; exists a0.
    apply andb_prop in H; destruct H.
    symmetry in H2; apply negb_sym in H2; simpl in H2.
    repeat split; auto using check_spec_eq_eq.
Qed.

Definition discharge_vcs (prooftable : RC_ANN.ProofTable.t) 
                         (vcs: VCs.vcset)
                         : error_monad (list (VCs.vc*VCs.vc_sources)) :=
  let vcs' := VCs.VerificationConditions.elements vcs in
  filter_list (fun vc =>
    match vc with ((f,f'),_) => 
      match RC_ANN.ProofTable.lookup prooftable (f,f') with
        | Some prf => if SYN0.proof_check_single f f' prf then ret false else
          fail (err_badproof mlapp (BASESEM.SYN.string_of_formula f) mlapp err_entails
            mlapp (BASESEM.SYN.string_of_formula f'))
        | None => ret true
      end
    end) vcs'.

Lemma discharge_vcs_ok : forall prooftable vcs,
  discharge_vcs prooftable vcs = Val nil ->
  forall f f',
  VCs.VerificationConditions.In (f,f') vcs ->
  SYN0.implies f f'.
Proof.
intros until vcs. intro exec. intros f f' [src lookup]. unfold discharge_vcs in exec.
apply VCs.VerificationConditions.elements_1 in lookup.
set (vcs' := VCs.VerificationConditions.elements vcs) in *.
destruct (proj1 (SetoidList.InA_alt _ _ _) lookup) as [[[f0 f0'] src0] [[vceq _] vin]].
simpl in vceq.
apply VCs.vc_eq in vceq.
destruct vceq.
subst f0 f0'.
match type of exec with (filter_list ?x vcs' = Val nil) => set (filterfn := x) in * end.
assert (notinnil : ~In (f, f',src) nil) by auto.
pose (f_false := filter_list_out _ _ _ _ exec vin notinnil).
clearbody f_false.
simpl in f_false.
destruct (RC_ANN.ProofTable.lookup prooftable (f,f')); [|discriminate].
case_eq (SYN0.proof_check_single f f' o); intros.
  assumption.

  intros.
  rewrite H in f_false.
  discriminate.
Qed.

Definition check_preclass
  (classes    : RC_CP.cert_classpool)
  (preclasses : RC_CP.Preclasspool.t)
  (privclasses: CLSNM.t)
  (spectable  : OverrideChecker.ClassTable.t (OverrideChecker.SpecTable.t RC_ANN.method_specification))
  (pc         : RC_C.preclass)
  (H          : forall nm c,
    RC_CP.class_loaded classes nm c ->
    RC_C.class_interface c = false ->
    exists spec_table, OverrideChecker.ClassTable.MapsTo nm spec_table spectable /\ OverrideChecker.correct_specs preclasses classes nm spec_table)
  : error_monad (list (VCs.vc * VCs.vc_sources))
  :=
  meths_vcs <- MethodVerifier.check_preclass_methods pc (CLSNM.mem (RC_C.preclass_name pc) privclasses);:
  override_vcs <- tagfailure err_overriding_problem (OverrideChecker.check_preclass preclasses classes spectable H (RC_C.preclass_name pc));:
  check_constantpool_additional classes preclasses (RC_C.preclass_constantpool pc) (snd (RC_C.preclass_annotation pc)) (RC_C.preclass_name pc);;
  discharge_vcs (fst (RC_C.preclass_annotation pc)) (vcset_union meths_vcs (fst override_vcs)).

Lemma MV_implies_L_verified_precode : forall cp cpa Q X code cert,
  MethodVerifier.verified_precode cp cpa Q X code cert ->
  Logic.verified_precode cp cpa Q X code cert.
intros. destruct H.
econstructor.
 assumption.
 intros. destruct (H0 n op H1). econstructor; eauto.
Save.

Lemma check_preclass_ok : forall classes preclasses privclasses spectable pc,
  forall (spectable_ok : forall (nm : RC_B.Classname.t) (c : RC_C.class),
    RC_CP.class_loaded classes nm c ->
    RC_C.class_interface c = false ->
    exists
      spec_table : OverrideChecker.SpecTable.t RC_ANN.method_specification,
      OverrideChecker.ClassTable.MapsTo nm spec_table spectable /\
      OverrideChecker.correct_specs preclasses classes nm spec_table),
  RC_CP.Preclasspool.lookup preclasses (RC_C.preclass_name pc) = Some pc ->
  check_preclass classes preclasses privclasses spectable pc spectable_ok = Val nil ->
  (forall c, ~RC_CP.class_loaded classes (RC_C.preclass_name pc) c) ->
  Logic.preclass_verified preclasses privclasses classes pc.
intros classes preclasses privclasses spectable pc spectable_ok in_preclasses check_ok not_loaded.
unfold check_preclass in check_ok.
destruct_err (MethodVerifier.check_preclass_methods pc (CLSNM.mem (RC_C.preclass_name pc) privclasses)) check_ok meths_vcs meths_vcs_eq.
destruct_err (OverrideChecker.check_preclass preclasses classes spectable spectable_ok (RC_C.preclass_name pc)) check_ok ores ores_eq.
destruct_err (check_constantpool_additional classes preclasses (RC_C.preclass_constantpool pc) (snd (RC_C.preclass_annotation pc)) (RC_C.preclass_name pc)) check_ok cpares cpares_eq.
pose (discharged := discharge_vcs_ok _ _ check_ok).
destruct ores as [override_vcs specs]. simpl in *.
destruct (OverrideChecker.check_preclass_ok preclasses classes spectable spectable_ok pc (RC_C.preclass_name pc) specs override_vcs); auto.
eapply ResOverrideChecker.vcset_union_ok2. unfold ResOverrideChecker.vcset_ok. apply discharged.
econstructor; eauto.
 apply check_constantpool_additional_ok. destruct cpares. assumption.
 (* code is verified for every method *)
 assert (meths_discharged : ResOverrideChecker.vcset_ok meths_vcs).
  eapply ResOverrideChecker.vcset_union_ok1. 
  unfold ResOverrideChecker.vcset_ok.
  apply discharged.
 unfold ResOverrideChecker.vcset_ok in meths_discharged.
 pose (MethodVerifier.check_preclass_methods_ok pc (CLSNM.mem (RC_C.preclass_name pc) privclasses) meths_vcs meths_vcs_eq meths_discharged).
 unfold MethodVerifier.preclass_verified_methods in p.
 intros md pm pc_has_pm.
 destruct (p md pm pc_has_pm) as [[code p']|ok].
  left. exists code. intros P Q X pm_spec.
  destruct (p' P Q X pm_spec) as [cert [P' [Q' [pm_has_code [pm_grants X0]]]]].
  exists cert. exists P'. exists Q'.
  assert (pm_grants' : (exists g, RC_ANN.grants (RC_C.premethod_annot pm) = Some g /\
               CLSNM.In (RC_C.preclass_name pc) privclasses /\
               Q' = ILL.given_resexpr_have g Q) \/
               RC_ANN.grants (RC_C.premethod_annot pm) = None /\ Q' = Q)
    by (destruct pm_grants as [[g H1]|H2]; intuition eauto using CLSNM.mem_2).
  intuition eauto using MV_implies_L_verified_precode, RSEM.implies_soundness.

  right. intuition.
Save.

(** *** The initial classpool and its correctness. *)

Require BuiltinClasses.
Module BIC := BuiltinClasses.BuiltinClasses RC_B RC_ANN.GA.A RC_C RC_CP.

Definition initial_spectable : OverrideChecker.ClassTable.t (OverrideChecker.SpecTable.t RC_ANN.method_specification) :=
  OverrideChecker.ClassTable.add RC_B.java_lang_Object
  (OverrideChecker.SpecTable.empty _)
  (OverrideChecker.ClassTable.empty _).

Lemma initial_ok :
  forall preclasses nm c,
    RC_CP.class_loaded BIC.initial_classes nm c ->
    RC_C.class_interface c = false ->
    exists spec_table : OverrideChecker.SpecTable.t RC_ANN.method_specification,
      OverrideChecker.ClassTable.MapsTo nm spec_table initial_spectable /\
      OverrideChecker.correct_specs preclasses BIC.initial_classes nm spec_table.
Proof.
  intros.
  exists (OverrideChecker.SpecTable.empty _).
  destruct (RC_CP.initial_has_jlo _ _ _ _ _ H).
  split.
    subst nm c.
    apply OverrideChecker.ClassTable.add_1. apply OverrideChecker.ClassTable.E.eq_refl.

    constructor; try (intros; edestruct OverrideChecker.SpecTable.empty_1; eassumption).
      intros. destruct H5.
        apply RC_CP.initial_has_jlo in H7; destruct H7; subst cB; contradiction.
        apply RC_CP.initial_has_jlo in H5; destruct H5; subst cB; contradiction.
        apply RC_CP.initial_has_jlo in H4; destruct H4; subst nmA c0. destruct H9; apply H9 in H; contradiction.
      intros. apply RC_CP.initial_has_jlo in H3; destruct H3; subst nm c0. simpl in H5.
      unfold BIC.j_l_Object_methods in H5. apply RC_C.MethodList.indep_lookup_2 in H5. rewrite RC_C.MethodList.lookup_empty in H5. discriminate. unfold RC_C.MethodList.Key.eq. intro Hmd. destruct md. injection Hmd as Hmd' Hmd''. subst t. simpl in H4. destruct H4. reflexivity.
      intros [mdn mdd] notinit [nmS [cS [m [_ [loaded [_ [meth _]]]]]]].
      apply RC_CP.initial_has_jlo in loaded. destruct loaded. subst nmS cS. simpl in meth.
      unfold BIC.j_l_Object_methods in meth. apply RC_C.MethodList.indep_lookup_2 in meth. rewrite RC_C.MethodList.lookup_empty in meth. discriminate. unfold RC_C.MethodList.Key.eq. intro Hmd. injection Hmd as Hmd' Hmd''. subst mdn. simpl in notinit. destruct notinit. reflexivity.
      split; [intros spec|intros [notinit minimal]].
        apply OverrideChecker.SpecTable.empty_1 in spec. contradiction.
        destruct minimal.
      
        destruct (H3 _ H).
        apply RC_CP.initial_has_jlo in H7; destruct H7; subst cS.
        unfold BIC.j_l_Object_methods in H9. simpl in H9. apply RC_C.MethodList.indep_lookup_2 in H9. rewrite RC_C.MethodList.lookup_empty in H9. discriminate. unfold RC_C.MethodList.Key.eq. intro Hmd. destruct md. injection Hmd as Hmd' Hmd''. subst t. simpl in notinit. destruct notinit. reflexivity.
        destruct (H3 _ H).
Qed.

(** ** The main checking function. *)

Module CTOverlay := FMapOverlay.MakeOverlay OverrideChecker.ClassTable.

(** Check that the key from the preclasspool matches the preclass' actual name.
  *)

Definition check_name (pc : RC_CP.Preclasspool.key*RC_CP.Preclasspool.object) :=
  tagboolfail err_notfound (match RC_B.Classname.eq_dec (fst pc) (RC_C.preclass_name (snd pc)) with left _ => true | right _ => false end).

(** Check all of the preclasses in turn. *)

(* I would have liked to use Program Definition here, but the resulting proof
   obligation has unnecessary dependencies on vcs0 and vcs', which make the
   later proof more difficult. *)

(* begin show *)
Definition check_preclasses 
  (preclasses : RC_CP.Preclasspool.t)
  (privclasses: CLSNM.t)
  (spectable  : OverrideChecker.ClassTable.t (OverrideChecker.SpecTable.t RC_ANN.method_specification))
  : error_monad (list (VCs.vc * VCs.vc_sources)).
intros.
refine (
  let spectable' := CTOverlay.overlay _ initial_spectable spectable in
  fold_left (fun vcs' pc =>
             vcs0 <- vcs';:
             check_name pc;;
             vcs1 <- tagfailure ((RC_B.Classname.to_string (fst pc)) mlapp err_sep) (check_preclass BIC.initial_classes preclasses privclasses spectable' (snd pc) _);:
             ret (vcs0 ++ vcs1))
            (RC_CP.Preclasspool.elements preclasses) (ret nil)).
clear vcs0 vcs'.
intros.
destruct (initial_ok preclasses nm c) as [st [maps correct]]; auto.
exists st.
split; auto.
apply CTOverlay.overlay_law2.
tauto.
Defined.
(* end show *)

Lemma check_name_ok : forall pc, check_name pc = Val tt -> fst pc = RC_C.preclass_name (snd pc).
Proof.
  intros.
  destruct pc.
  destruct o.
  simpl in *. unfold check_name in H. simpl in H. destruct (RC_B.Classname.eq_dec k preclass_name). auto.
  discriminate.
Qed.

Lemma badfold_ok : forall {T:Type} (f:RC_CP.Preclasspool.key*RC_CP.Preclasspool.object-> error_monad (list T)) l e,
  fold_left (fun vcs' pc => vcs0 <- vcs';: check_name pc;; vcs1 <- f pc;: ret (vcs0 ++ vcs1)) l (Err e) = Err e.
Proof.
  induction l; simpl; auto.
Qed.

Lemma fold_ok : forall {T:Type} (f:RC_CP.Preclasspool.key*RC_CP.Preclasspool.object-> error_monad (list T)) l pc,
  fold_left (fun vcs' pc => vcs0 <- vcs';: check_name pc;; vcs1 <- f pc;: ret (vcs0 ++ vcs1)) l (ret nil) = Val nil ->
  SetoidList.InA RC_CP.Preclasspool.eq_key_obj pc l ->
  f pc = Val nil /\ fst pc = RC_C.preclass_name (snd pc).
Proof.
  induction l; intros; simpl in *; inversion H0; subst y l0;
    case_eq (f a); intros l0 feq; rewrite feq in H;
    case_eq (check_name a); intros u eq1; rewrite eq1 in H;
    simpl in H; try (rewrite badfold_ok in H; discriminate).
    assert (pc = a) by (clear - H2; destruct pc; destruct a; destruct H2; simpl in *; rewrite H; subst o; reflexivity).
    subst a. destruct l0. split. assumption. apply check_name_ok. destruct u. assumption.
      simpl in H. clear -H. elimtype False. assert (neq : t::l0 <> nil) by (intro e; inversion e). generalize (t::l0) H neq. clear. induction l; intros; simpl in H.
        injection H as H'. contradiction.
        destruct (f a); destruct (check_name a); simpl in H; try (rewrite badfold_ok in H; discriminate). eapply IHl. apply H. intro apeq; destruct (List.app_eq_nil _ _ apeq). contradiction.
    destruct l0; auto.
      simpl in H. clear -H. elimtype False. assert (neq : t::l0 <> nil) by (intro e; inversion e). generalize (t::l0) H neq. clear. induction l; intros; simpl in H.
        injection H as H'. contradiction.
        destruct (check_name a); destruct (f a); simpl in H; try (rewrite badfold_ok in H; discriminate). eapply IHl. apply H. intro apeq; destruct (List.app_eq_nil _ _ apeq). contradiction.
Qed.

(** Prove that [check_preclasses] verifies all of the preclasspool. *)

Theorem check_preclasses_ok : forall preclasses privclasses spectable,
  check_preclasses preclasses privclasses spectable = Val nil ->
  Logic.all_preclasses_verified preclasses privclasses BIC.initial_classes.
Proof.
  intros until spectable. intros check nm pc  pc_lookup _ not_loaded.
  unfold check_preclasses in check. set (pc_present := pc_lookup). apply RC_CP.Preclasspool.elements_1 in pc_present.
  match type of check with context [fun vcs' pc => vcs0 <- _;: check_name _;; vcs1 <- (@?F pc);: _] => set (foldfn:=F) end.
  destruct (fold_ok foldfn (RC_CP.Preclasspool.elements preclasses) (nm, pc) check pc_present) as [check_ok name_ok].
  unfold foldfn in check_ok. unfold tagfailure in check_ok. match type of check_ok with (match ?X with Val _ => _ | Err _ => _ end = Val _) => destruct X as [check_res|] _eqn:check_ok'; try discriminate end. simpl in check_ok'.  injection check_ok as res_nil. subst check_res. simpl in name_ok. rewrite name_ok in pc_lookup, not_loaded. apply check_preclass_ok in check_ok'; auto.
Qed.

End ResourceChecker.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)
