Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import Peano_dec.
Require Import StoreIface.
Require Import OptionExt.
Require Import List.
Require Import ListExt.
Require Import Compare_dec.
Require Import Arith.
Require Import Certificates.
Require Import VerifierAnnotationsIface.
Require Import AbstractLogic.
Require Import VCs.
Require Import ErrorMonad.
Require Import ErrorMessages.
Require Import MLStrings.
Require Import NativeMethodSpec.
Require Import Setoid.
Require Import Omega.

Module Type CODE_VERIFIER_BASE
  (B : BASICS)
  (AL : ABSTRACT_LOGIC B)
  (CERT : CERTIFICATE with Definition asn := AL.formula)
  (ANN : VERIFIER_ANNOTATIONS B AL CERT)
  (C : CLASSDATATYPES B ANN.GA.A).

Parameter instruction_precondition :
  CERT.Cert.t ->
  C.ConstantPool.t ->
  AL.formula ->
  AL.formula ->
  ANN.ConstantPoolAdditional.t ->
  list C.exception_handler ->
  C.opcode ->
  nat ->
  AL.formula ->
  Prop.

Parameter get_instruction_precondition :
  CERT.Cert.t ->
  C.ConstantPool.t ->
  AL.formula ->
  AL.formula ->
  ANN.ConstantPoolAdditional.t ->
  list C.exception_handler ->
  C.opcode ->
  nat ->
  error_monad AL.formula.

Hypothesis get_instruction_precondition_sound : forall cert cp ensures ex_ensures cpa handlers op pc a,
  get_instruction_precondition cert cp ensures ex_ensures cpa handlers op pc = Val a ->
  instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a.

Hypothesis cert_incl_instruction_precondition : forall cert cert' cp ensures ex_ensures cpa handlers op pc a,
  CERT.cert_incl cert cert' ->
  instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a ->
  instruction_precondition cert' cp ensures ex_ensures cpa handlers op pc a.

End CODE_VERIFIER_BASE.

Module MkCodeVerifier (B     : BASICS)
                      (AL    : ABSTRACT_LOGIC B)
                      (CERT  : CERTIFICATE with Definition asn := AL.formula)
                      (ANN   : VERIFIER_ANNOTATIONS B AL CERT)
                      (C     : CLASSDATATYPES B ANN.GA.A)
                      (Base  : CODE_VERIFIER_BASE B AL CERT ANN C)
                      (NTSPC : NATIVE_METHOD_SPEC B ANN.GA.A)
                      (VCs   : VERIFICATION_CONDITIONS B AL).

Import CERT.

Section ErrorHandling.

Definition getproof (prooftable : ANN.ProofTable.t) (hyp res : AL.formula) :=
  tagoptfail (err_noproof mlapp (AL.string_of_formula hyp) mlapp
              err_entails mlapp (AL.string_of_formula res))
  (ANN.ProofTable.lookup prooftable (hyp, res)).

End ErrorHandling.
    
Section CodeVerification.

Hypothesis cp : C.ConstantPool.t.
Hypothesis cpa : ANN.ConstantPoolAdditional.t.
Hypothesis ensures ex_ensures : AL.formula.

Inductive verified_instruction (cert:Cert.t)
                               (handlers : list C.exception_handler)
                               (op : C.opcode)
                               (pc : nat) : Prop :=
| mk_verified_instruction : forall a1 a2,
    CERT.Cert.lookup cert pc = Some a1 ->
    Base.instruction_precondition cert cp ensures ex_ensures cpa handlers op pc a2 ->
    AL.implies a1 a2 ->
    verified_instruction cert handlers op pc.

Hypothesis code : C.precode.

Inductive verified_precode (cert:Cert.t) : Prop :=
| mk_verified_code :
    (* the certificate only covers the actual code *)
    (forall n a, CERT.Cert.lookup cert n = Some a -> n < length (C.precode_code code)) ->
    (* all the actual instructions are safe *)
    (forall n op, nth_error (C.precode_code code) n = Some op -> 
      verified_instruction cert (C.precode_exception_table code) op n) ->
    verified_precode cert.

(* now we try to complete certificates *)

Hypothesis prooftable : ANN.ProofTable.t.

Definition method_vc := (VCs.VerificationConditions.key * nat)%type.

Definition completion_step : Cert.t -> nat -> C.opcode -> error_monad (Cert.t * list method_vc) :=
  fun cert pc op =>
  a <- Base.get_instruction_precondition cert cp ensures ex_ensures cpa (C.precode_exception_table code) op pc;:
  match Cert.lookup cert pc with
  | None => ret (Cert.update cert pc a, nil)
  | Some a' =>
     ret (cert, ((a',a),pc)::nil) 
  end.

Fixpoint complete_cert_aux (ops:list C.opcode) (cert:Cert.t) (pc:nat) {struct ops} : error_monad (Cert.t * list method_vc) :=
  match ops with
  | nil     => fail err_emptycode
  | op::nil => completion_step cert pc op 
  | op::ops => p1 <- complete_cert_aux ops cert (S pc);:
               match p1 with (cert',vcs) =>
                 p2 <- completion_step cert' pc op;:
                 match p2 with (cert'',vcs') =>
                   ret (cert'',vcs' ++ vcs)
                 end
               end
  end.

Definition complete_cert : error_monad (Cert.t * list method_vc) :=
  complete_cert_aux (C.precode_code code) (clean_cert (C.precode_annot code) (length (C.precode_code code))) 0.

Lemma step_incl : forall c c' vc n op, completion_step c n op = Val (c',vc) -> cert_incl c c'.
intros. unfold completion_step in H.
destruct (Base.get_instruction_precondition c cp ensures ex_ensures cpa (C.precode_exception_table code) op n) as [l|]; [|discriminate].
destruct (option_dec (Cert.lookup c n)) as [[a cert_lookup_result] | cert_lookup_result];
 rewrite cert_lookup_result in H.
 simpl in H. inversion H. apply cert_incl_refl.
 inversion H. apply cert_incl_update. apply cert_lookup_result.
Save.

Lemma complete_cert_incl : forall c c' vcs n ops,
  complete_cert_aux ops c n = Val (c',vcs) -> cert_incl c c'.
intros. generalize n c' vcs H. clear n c' vcs H.
induction ops; intros.
 discriminate.
 simpl in H. destruct ops.
  eapply step_incl. apply H.
  destruct_err (complete_cert_aux (o::ops) c (S n)) H cert'vcs' complete_cert_aux_result.
  destruct cert'vcs' as [cert' vcs'].
   eapply cert_incl_trans.
    eapply IHops. apply complete_cert_aux_result.
    destruct_err (completion_step cert' n a) H cert''vcs'' result.
    destruct cert''vcs'' as [cert'' vcs''].
    inversion H. subst.
    eapply step_incl.
    apply result.
Save.

Lemma complete_cert_aux_prop : forall n ops c c' vcs, n < length ops ->
  complete_cert_aux ops c 0 = Val (c',vcs) ->
  (exists c'', exists vcs'', complete_cert_aux (tail n ops) c n = Val (c'',vcs'')
               /\ cert_incl c c''
               /\ cert_incl c'' c'
               /\ forall vc, In vc vcs'' -> In vc vcs).
intros n ops c c' vcs n_lt_len_ops complete_cert_aux_result. 
rewrite <- (tail_0 ops) in complete_cert_aux_result.
pose (n':=n). assert (n_lt_n':n'<=n) by (auto with arith). replace 0 with (n-n') in complete_cert_aux_result by auto with arith.
pose (c3:=c'). assert (c3_incl_c':cert_incl c3 c') by (apply cert_incl_refl). replace c' with c3 in complete_cert_aux_result by reflexivity.
generalize c vcs c3 c3_incl_c' complete_cert_aux_result n_lt_n'. clear c vcs c3 c3_incl_c' complete_cert_aux_result n_lt_n'.
induction n'; intros.
 (* base case *)
 rewrite <- minus_n_O in complete_cert_aux_result. exists c3. exists vcs. intuition.
 eapply complete_cert_incl. apply complete_cert_aux_result.
 (* step case *)
 destruct (tail_minus ops n' n) as [op tail_eq]. omega. assumption.
 rewrite tail_eq in complete_cert_aux_result.
 simpl in complete_cert_aux_result.
 destruct (tail_S (n-n') ops) as [op' tail_eq']. omega.
 rewrite tail_eq' in complete_cert_aux_result.
 destruct_err (complete_cert_aux (op' :: tail (S (n - n')) ops) c (S (n - S n'))) complete_cert_aux_result cert'vcs' complete_cert_aux_result'.
 destruct cert'vcs' as [cert' vcs'].
  rewrite <- tail_eq' in complete_cert_aux_result'.
  replace (S (n - S n')) with (n-n') in complete_cert_aux_result'.
  destruct_err (completion_step cert' (n - S n') op) complete_cert_aux_result c3vcs result.
  destruct c3vcs. inversion complete_cert_aux_result.  subst.
  assert (cert'_c3 : cert_incl cert' c3).
   eapply step_incl.
   eassumption.
  assert (cert'_c' : cert_incl cert' c').
   eapply cert_incl_trans;eauto.
  destruct (IHn' _ _ _ cert'_c' complete_cert_aux_result') as [c'' [vcs'' [cca [incl1 [incl2 vc_in]]]]].
   omega.
   exists c''. exists vcs''. intuition. 
   omega.
Save.

Lemma completion_step_clean : forall c c' vcs pc op limit,
  pc < limit ->
  completion_step c pc op = Val (c',vcs) ->
  (forall n, n >= limit -> Cert.lookup c n = None) ->
  (forall n, n >= limit -> Cert.lookup c' n = None).
intros.
unfold completion_step in H0. 
destruct (Base.get_instruction_precondition c cp ensures ex_ensures cpa (C.precode_exception_table code) op pc) as [l|]; [|discriminate].
destruct (Cert.lookup c pc) as [a|].
 inversion H0. subst c'. eauto.
 inversion H0. subst c'. rewrite (Cert.indep_lookup c pc n); [auto|unfold Cert.Key.eq; omega].
Save.

Lemma complete_cert_aux_clean : forall c c' vcs n ops, 
  (forall m, m >= n+length ops -> Cert.lookup c m = None) ->
  complete_cert_aux ops c n = Val (c',vcs) -> 
  (forall m, m >= n+length ops -> Cert.lookup c' m = None).
intros. generalize n c' vcs H H0 m H1. clear n c' vcs H H0 m H1.
induction ops; intros.
 (* base case *)
 discriminate.
 (* step case *)
 simpl in H0.
 destruct ops.
  apply (completion_step_clean c c' vcs n a (n+length (a::nil))).
   simpl. omega.
   apply H0.
   apply H.
   apply H1.
  destruct_err (complete_cert_aux (o::ops) c (S n)) H0 cert'vcs complete_cert_aux_result.
  destruct cert'vcs as [cert' vcs'].
  destruct_err (completion_step cert' n a) H0 cert''vcs'' completion_step_result.
  destruct cert''vcs'' as [cert'' vcs''].
  inversion H0. subst c'.
   apply (completion_step_clean cert' cert'' vcs'' n a (n+length (a::o::ops))); auto.
    simpl. omega.
    intros. eapply (IHops (S n)); eauto.
     intros. apply H. simpl. simpl in H3. omega.
     simpl. simpl in H2. omega.
Save.

Lemma step_ok : forall c c' vcs op pc,
  completion_step c pc op = Val (c',vcs) ->
  (forall f f' s, In ((f,f'),s) vcs -> AL.implies f f') ->
  verified_instruction c' (C.precode_exception_table code) op pc.
intros. unfold completion_step in H.
destruct_err (Base.get_instruction_precondition c cp ensures ex_ensures cpa (C.precode_exception_table code) op pc) H a vcgen_result.
 destruct (option_dec (Cert.lookup c pc)) as [[a' lookup_res]|lookup_res]; rewrite lookup_res in H.
  inversion H. subst. eapply mk_verified_instruction; eauto.
   apply Base.get_instruction_precondition_sound. eassumption.
   eapply H0. left. reflexivity.
  inversion H. eapply mk_verified_instruction.
   apply Cert.lookup_update.
   eapply Base.cert_incl_instruction_precondition.
    apply CERT.cert_incl_update. assumption.
    apply Base.get_instruction_precondition_sound. eassumption.
   apply AL.implies_refl.
Save.

Lemma cert_incl_safe : forall handlers c1 c2 pc op,
   verified_instruction c1 handlers op pc -> cert_incl c1 c2 -> verified_instruction c2 handlers op pc.
intros.
destruct H. 
eapply mk_verified_instruction. 
  eapply cert_incl_lookup. apply H. apply H0.
  eapply Base.cert_incl_instruction_precondition. apply H0. apply H1.
  assumption.
Save.

Lemma complete_cert_ok : forall cert' vcs,
  complete_cert = Val (cert',vcs) ->
  (forall f f' s, In ((f,f'),s) vcs -> AL.implies f f') ->
  verified_precode cert'.
intros. unfold complete_cert in H.
eapply mk_verified_code.
 (* Only the positions in the certificate are mentioned *)
 apply clean_contra. intros.
 apply (complete_cert_aux_clean (clean_cert (C.precode_annot code) (length (C.precode_code code))) cert' vcs 0 (C.precode_code code)).
  intros. apply clean_ok. assumption.
  apply H.
  simpl. assumption.
 (* all instructions are safe *)
 intros.
 destruct (complete_cert_aux_prop n (C.precode_code code) _ cert' _ (nth_error_length_2 _ _ _ _ H1) H)
  as [cert'' [vcs' [complete_cert_aux_result [cert_incl_1 [cert_incl_2 vcs_incl]]]]].
 destruct (tail_nth_error n (C.precode_code code) op H1) as [ops tail_eq].
 rewrite tail_eq in complete_cert_aux_result. simpl in complete_cert_aux_result.
 destruct ops.
  eapply cert_incl_safe. eapply step_ok. apply complete_cert_aux_result.
   intros. eapply H0. apply vcs_incl. apply H2.
   apply cert_incl_2.
  destruct_err (complete_cert_aux (o::ops) (clean_cert (C.precode_annot code) (length (C.precode_code code))) (S n))
   complete_cert_aux_result cert''' complete_cert_aux_result'.
  destruct cert''' as [cert''' vcs'''].
  destruct_err (completion_step cert''' n op) complete_cert_aux_result cert'4 complete_cert_aux_result''.
  destruct cert'4 as [cert'4 vcs'4].
  inversion complete_cert_aux_result. subst cert'4 vcs'.
  eapply cert_incl_safe.
   eapply step_ok. apply complete_cert_aux_result''. intros. eapply H0. apply vcs_incl. apply List.in_or_app. left. apply H2.
   apply cert_incl_2.
Save.

End CodeVerification.

Module VCFacts := OrderedType.OrderedTypeFacts VCs.VerificationConditions.E.

Section PreclassVerification.

Hypothesis pcl : C.preclass.
Hypothesis ispriv : bool.
Definition prooftable : ANN.ProofTable.t := fst (C.preclass_annotation pcl).

(* Adapted from the full record definition in ResourceSafety. *)
Definition 
preclass_verified_methods : Prop :=
(forall md pm,
  C.has_premethod (C.preclass_methods pcl) md pm ->
  (exists code, forall P Q X,
    ANN.method_spec (C.premethod_annot pm) = (P, Q, X) ->
    exists cert, exists P', exists Q',
      C.premethod_code pm = Some code
      /\ ((exists g, ANN.grants (C.premethod_annot pm) = Some g /\ ispriv = true /\ Q' = AL.given_resexpr_have g Q)
        \/ (ANN.grants (C.premethod_annot pm) = None /\ Q' = Q))
      /\ verified_precode (C.preclass_constantpool pcl) (snd (C.preclass_annotation pcl)) Q' X code cert
      /\ AL.implies P P'
      /\ Cert.lookup cert 0 = Some P')
  \/
(* TO DO: should we check that the method is declared native rather than abstract? *)
  (C.premethod_code pm = None /\
    (C.premethod_abstract pm = true \/
      (NTSPC.SpecTable.MapsTo (C.preclass_name pcl, (C.premethod_name pm)) (C.premethod_annot pm) NTSPC.table /\
        (ispriv = true \/ ANN.grants (C.premethod_annot pm) = None)))))
.

Definition check_method (pm : C.premethod) : error_monad (Cert.t * list method_vc) :=
  tagfailure (err_checkmethod mlapp (B.Methodname.to_string (C.premethod_name pm)) mlapp err_sep)
  match C.premethod_code pm with
    | None => if C.premethod_abstract pm then ret (Cert.empty, nil) else
      match NTSPC.SpecTable.find (C.preclass_name pcl, C.premethod_name pm) NTSPC.table with
        | None => fail err_native_missing
        | Some annotation =>
          if ANN.method_annotation_eqdec annotation (C.premethod_annot pm)
            then
              match ANN.grants (C.premethod_annot pm) with
                | None => ret (Cert.empty, nil)
                | Some _ =>
                  if ispriv then ret (Cert.empty, nil)
                    else fail err_grants_no_privilege
              end
            else fail err_native_bad_spec
      end
    | Some code =>
      match ANN.method_spec (C.premethod_annot pm) with (P, Q, X) =>
        Q' <- match ANN.grants (C.premethod_annot pm) with
                | None => ret Q
                | Some g =>
                  if ispriv then ret (AL.given_resexpr_have g Q)
                    else fail err_grants_no_privilege
              end;:
        r <- complete_cert (C.preclass_constantpool pcl) (snd (C.preclass_annotation pcl)) Q' X code;:
        match r with (cert,vcs) =>
          (* Perhaps we can establish that this will never fail? *)
          P' <- tagoptfail err_incomplete (Cert.lookup cert O);:
          ret (cert, ((P,P'),0)::vcs)
        end
      end
  end.

Lemma check_method_ok : forall P Q X pm cert code vcs,
  C.premethod_code pm = Some code ->
  ANN.method_spec (C.premethod_annot pm) = (P, Q, X) ->
  check_method pm = Val (cert, vcs) ->
  (forall f f' s, In ((f,f'),s) vcs -> AL.implies f f') ->
  exists P', exists Q', C.premethod_code pm = Some code /\
  ((exists g, ANN.grants (C.premethod_annot pm) = Some g /\ ispriv = true /\ Q' = AL.given_resexpr_have g Q) \/
  (ANN.grants (C.premethod_annot pm) = None /\ Q' = Q)) /\
  verified_precode
  (C.preclass_constantpool pcl)
  (snd (C.preclass_annotation pcl))
  Q'
  X
  code
  cert
  /\ AL.implies P P'
  /\ Cert.lookup cert O = Some P'.
Proof.
intros until vcs.
intros method_code annot check vcs_ok.
unfold check_method in check.
unfold tagfailure in check.
(* We get the same code as before. *)
destruct (C.premethod_code pm).
injection method_code as codeeq'.
rewrite codeeq' in * |- *.
clear codeeq'.

rewrite annot in * |- *.

destruct_err (match ANN.grants (C.premethod_annot pm) return error_monad AL.formula with
                | Some g =>
                  if ispriv
                    then ret (T:=AL.formula) (AL.given_resexpr_have g Q)
                    else fail (T:=AL.formula) err_grants_no_privilege
                | None => ret (T:=AL.formula) Q
              end) check Q' Q'eq.
destruct_err (complete_cert (C.preclass_constantpool pcl) (snd (C.preclass_annotation pcl)) Q' X code) check cert' certeq.
destruct cert' as [cert' vcs'].
destruct_err (tagoptfail err_incomplete (Cert.lookup cert' O)) check P' P'eq.
inject_opttag P'eq.
injection check. intros vc_eq cert_eq. subst cert' vcs.

exists P'. exists Q'.
split; auto.
split; auto.
 destruct (ANN.grants (C.premethod_annot pm)) as [g|].
  left; exists g; intuition; destruct ispriv; [reflexivity|discriminate|injection Q'eq as Qeq; auto|discriminate].
  injection Q'eq as Qeq; right; intuition.
split. eapply complete_cert_ok; eauto.
intros. eapply vcs_ok. right. apply H.
split. eapply vcs_ok.  left. reflexivity.
assumption.

discriminate.

Save.

Fixpoint testall (T:Set) (f:T -> option error) (l:list T) :=
  match l with
    | nil => None
    | h::t => match f h with
                | None => testall T f t
                | Some e => Some e
              end
  end.

Implicit Arguments testall [T].

Lemma testall_ok: forall T f l, testall (T:=T) f l = None ->
                  forall i, In (A:=T) i l -> f i = None.
Proof.
induction l.
contradiction.
intros code i iinl.
simpl in code.
destruct (in_inv iinl).
rewrite H in * |- *.
destruct (f i).
discriminate.
reflexivity.

destruct (f a).
discriminate.
apply IHl; assumption.
Save.

Definition add_vcs (t:VCs.vcset) (vcs:list method_vc) (c:B.Classname.t) (m:B.Methodname.t):=
  List.fold_left (fun vcs vc => match vc with (vc',s) => VCs.add_vc vcs vc' (VCs.vc_spec c m s) end) vcs t.

Lemma add_vcs_mono : forall l t t' c m vc,
  add_vcs t l c m = t' ->
  VCs.VerificationConditions.In vc t ->
  VCs.VerificationConditions.In vc t'.
Proof.
  induction l; intros.
    simpl in H.
    subst. assumption.

    destruct a as [vc' src].
    simpl in H.
    unfold VCs.add_vc in H.
    destruct H0 as [s0 lookup].
    set (vc'' := VCs.simplify_vc vc') in *.
    destruct (VCFacts.eq_dec vc vc'') as [vc_eq|vc_neq].
      apply (VCs.VerificationConditions.MapsTo_1 (elt:=VCs.vc_sources) (m:=t) (e:=s0) vc_eq) in lookup.
      rewrite (VCs.VerificationConditions.find_1 lookup) in H.
      eapply IHl; eauto.
      exists ((VCs.vc_spec c m src)::s0).
      apply VCs.VerificationConditions.add_1.
      apply VCs.VerificationConditions.E.eq_sym.
      assumption.

      eapply IHl; eauto.
      unfold VCs.VerificationConditions.In.
      eapply ex_intro.
      apply VCs.VerificationConditions.add_2; eauto.
Qed.

Lemma add_vcs_ok : forall vcs t t' c m f f' src,
  add_vcs t vcs c m = t' -> In ((f,f'),src) vcs ->
  VCs.VerificationConditions.In (VCs.simplify_vc (f,f')) t'.
Proof.
  induction vcs; intros.
    destruct H0.

    inversion H0.
      subst a.
      simpl in H.
      eapply add_vcs_mono; eauto.
      unfold VCs.add_vc.
      destruct (VCs.VerificationConditions.find (VCs.simplify_vc (f, f')) t).
        exists ((VCs.vc_spec c m src) :: v).
        apply VCs.VerificationConditions.add_1.
        apply VCs.VerificationConditions.E.eq_refl.

        exists ((VCs.vc_spec c m src) :: nil).
        apply VCs.VerificationConditions.add_1.
        apply VCs.VerificationConditions.E.eq_refl.

      eapply IHvcs; eauto.
      simpl in H.
      apply H.
Qed.

Definition check_preclass_methods : error_monad VCs.vcset :=
  List.fold_left (fun vcs_e m =>
    vcs <- vcs_e;:
    r <- check_method m;:
    match r with (cert, m_vcs) =>
      ret (add_vcs vcs m_vcs (C.preclass_name pcl) (C.premethod_name m))
    end) (C.preclass_methods pcl) (ret (VCs.VerificationConditions.empty VCs.vc_sources)).

Lemma check_preclass_methods_ok : forall vcs,
  check_preclass_methods = Val vcs ->
  (forall p p', VCs.VerificationConditions.In (p,p') vcs -> AL.implies p p') ->
  preclass_verified_methods.
Proof.
  intros vcs exec vcs_ok.
  unfold check_preclass_methods in exec.
  unfold preclass_verified_methods.
  intros.
  set (init_vcs := VCs.VerificationConditions.empty VCs.vc_sources) in *.
  clearbody init_vcs.
  revert init_vcs exec.
  induction (C.preclass_methods pcl); intros.
    inversion H.

    inversion H.
      (* This is the right method. *)
      rewrite H3 in *.
      subst a md.
      simpl in exec.
      case_eq (check_method pm).
        intros [m_cert m_vcs] check.
        destruct code as [code'|] _eqn: code_eq.
          left.
          exists code'.
          exists m_cert.
          eapply check_method_ok; auto. subst pm; reflexivity. eassumption.
          intros.
          assert (vcs_incl : VCs.VerificationConditions.In (VCs.simplify_vc (f,f')) vcs).
            subst meths.
            clear IHl.
            rewrite check in exec.
            simpl in exec.
            set (suff_vcs := add_vcs init_vcs m_vcs (C.preclass_name pcl) (C.premethod_name pm)) in exec.
            (* Establish that adding to the vcs now will ensure that the vc is in
               the final result. *)
            assert (have_vc : VCs.VerificationConditions.In (VCs.simplify_vc (f,f')) suff_vcs) by apply (add_vcs_ok _ _ _ _ _ _ _ _ (refl_equal suff_vcs) H1).
            clearbody suff_vcs.
            revert suff_vcs have_vc exec.
            induction l; intros.
              simpl in exec.
              inject_err exec.
              subst vcs.
              assumption.

              simpl in exec.
              destruct (check_method a) as [[a_cert a_vcs]|].
                simpl in exec.
                set (new_vcs := add_vcs suff_vcs a_vcs (C.preclass_name pcl) (C.premethod_name a)) in *.
                assert (new_vcs_is : (add_vcs suff_vcs a_vcs (C.preclass_name pcl) (C.premethod_name a) = new_vcs)) by reflexivity.
                eapply IHl.
                  rewrite <- H3.
                  apply C.has_premethod_cons_1.

                  eapply add_vcs_mono. apply new_vcs_is.
                  apply have_vc.

                  apply exec.

                (* We have to show that failures are propogated to the end. *)
                elimtype False.
                clear - exec.
                induction l.
                  discriminate.

                  apply IHl.
                    assumption.

          unfold VCs.simplify_vc in vcs_incl.
          eapply AL.implies_trans.
            apply (proj1 (AL.simplify_ok f)).
            eapply AL.implies_trans.
              eapply vcs_ok. apply vcs_incl.
              apply (proj2 (AL.simplify_ok f')).

        right. subst pm. split.
          reflexivity.
          unfold check_method in check. simpl in check.
          destruct abstract; auto.
          right.
          simpl in *. destruct (NTSPC.SpecTable.find (C.preclass_name pcl, nm) NTSPC.table) as [spec|] _eqn:finds; try discriminate.
          destruct (ANN.method_annotation_eqdec spec annot); try discriminate;
          destruct (ANN.grants annot); destruct ispriv; try discriminate;
          (split;
            [apply NTSPC.SpecTable.find_2; rewrite finds;
              simpl in check; inversion check; subst spec; reflexivity| tauto]).

      (* Again, propogate failures. *)
      intros.
      rewrite H0 in *.
      elimtype False.
      clear - exec.
      induction l.
        discriminate.
        
        auto.


    (* This is some other method *)
    subst meths md m.
    simpl in exec.
    destruct (check_method a) as [[a_cert a_vcs]|].
      simpl in exec.
      eapply IHl; auto.
        apply exec.

      (* Again, propogate failures. *)
      elimtype False.
      clear - exec.
      induction l; [discriminate|auto].
Qed.

End PreclassVerification.

End MkCodeVerifier.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)












