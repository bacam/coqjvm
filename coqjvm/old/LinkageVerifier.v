Require Import GenericVerifierIface.
Require Import ClassDatatypesIface.
Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import OptionMonad.
Require Import OptionExt.
Require Import ClasspoolIface.
Require Import CertRuntimeTypesIface.
Require Import List.
Require Import Execution.

Module ResourceVerifierOuter
        (B : BASICS)
        (SYN : ILL_SYNTAX with Module SYN.B := B)
        (CERT : CERTIFICATE with Module SYN := SYN)
        (ANN : ILLANNOTATIONS with Module SYN := SYN with Module CERT := CERT)
        (RA : RESOURCE_ALGEBRA with Module B := B)
        (C : CLASSDATATYPES with Module B := B with Module A := ANN)
        (CP : CLASSPOOL with Module B := B with Module C := C)
        (RT : CERTRUNTIMETYPES with Module B := B with Module C := C with Module CP := CP)
        (RSEM : ILL_SEMANTICS with Module RA := RA with Module SYN := SYN).

Module ResourceCodeVerifierBase.

Module SYN := SYN.
Module CERT := CERT.
Module C := C.

Import CERT.
Import SYN.

Definition vcgen (class : C.class)
                 (method : C.method)
                 (certificate : Cert.t)
                 (pc : nat)
                 (op : C.opcode)
               : option formula
  := match op with
     | C.op_iconst _ =>
         Cert.lookup certificate (S pc)
     | C.op_new idx =>
         a <- Cert.lookup certificate (S pc);:
         ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
         match ref with
         | C.cpe_classref cls_nm =>
            ret (f_tensor (f_atom (R_new cls_nm)) a)
         | _ =>
            fail
         end
     | _ =>
         fail
     end.

Lemma cert_incl_vcgen : forall class method cert1 cert2 n op a,
  vcgen class method cert1 n op = Some a ->
  CERT.cert_incl cert1 cert2 ->
  vcgen class method cert2 n op = Some a.
intros class method cert1 cert2 pc op a vcgen_cert1 cert1_incl_cert2.
destruct op; first
 [discriminate
 |simpl in *; destruct (cert1_incl_cert2 (S pc)); try discriminate; assumption
 ].
Save.

End ResourceCodeVerifierBase.


Module Inner (RCV : CODE_VERIFIER with Module SYN := SYN
                                  with Module CERT := CERT
                                  with Module ANN := ANN
                                  with Module C := C
                                  with Module Base := ResourceCodeVerifierBase).

Import SYN.
Import CERT.
Import RCV.
Import RSEM.
Import RA.

Lemma resource_shuffle : forall used future total current newfuture realcurrent,
  used :*: future <: total ->
  current :*: newfuture <: future ->
  realcurrent <: current ->
  used :*: realcurrent :*: newfuture <: total.
intros used future total current newfuture realcurrent uf_t cn_f r_c.
eapply leq_trans.
 apply leq_refl. apply eq_symm. apply combine_assoc.
 eapply leq_trans.
  eapply combine_order.
   eapply leq_refl. eapply eq_refl.
   eapply leq_trans.
    eapply combine_order.
     apply r_c.
     eapply leq_refl. apply eq_refl.
    apply cn_f.
  assumption.
Save. 

Module E := Execution.Execution B RA C CP RT.

Inductive safe_current_frame : CP.cert_classpool -> RT.frame -> res -> Prop :=
| mk_safe_current_frame : forall classes op_stack lvars pc code method class res_assertion allowed_res cert,
    CP.Classpool.lookup (CP.classpool classes) (C.class_name class) = Some class ->
    safe_code class method cert code ->
    Cert.lookup cert pc = Some res_assertion ->
    sat allowed_res res_assertion ->
    safe_current_frame classes (RT.mkFrame op_stack lvars pc code class) allowed_res.

Inductive safe_state : CP.Preclasspool.t -> E.state -> Prop :=
| mk_safe_state : forall f fs classes preclasses heap statics used_res touse_res total_res,
   safe_current_frame classes f touse_res ->
   used_res :*: touse_res <: total_res ->
   safe_state preclasses (RT.mkState (f::fs) classes heap statics (E.mkResInfo used_res total_res)).

Lemma exec_safe : forall preclasses s result,
  safe_state preclasses s ->
  E.exec preclasses s = result ->
    (exists s', E.cont s' = result /\ safe_state preclasses s')
  \/(exists s', exists v, E.stop s' v = result /\ safe_state preclasses s')
  \/(exists s', exists e, E.stop_exn s' e = result /\ safe_state preclasses s')
  \/E.wrong = result.
intros preclasses s result.
intros s_safe CODE.
destruct s_safe as [f fs classes preclasses heap statics used_res touse_res total_res f_safe res_ok].
simpl in CODE.
destruct f_safe as [classes op_stack lvars pc code method class res_assertion allowed_res cert class_exists code_safe pc_assertion assertion_sat].
destruct (safe_code_implies _ _ _ _ _ _ code_safe pc_assertion) as [op [assertion' [op_exists [op_vcgen pc_implies_assertion']]]].
replace (nth_error (RT.C.code_code code) pc) with (Some op) in CODE.
destruct op; try discriminate.

(* op_new *)
simpl in op_vcgen.
destruct (option_informative (Cert.lookup cert (S pc))) as [[a_Spc lookup_a_Spc] | no_a_Spc].
 rewrite lookup_a_Spc in op_vcgen.
 destruct (option_informative (C.ConstantPool.lookup (C.class_constantpool class) t)) as [[ref lookup_ref] | no_ref].
  (* reference was found in the constantpool *)
  rewrite lookup_ref in op_vcgen.
  simpl in op_vcgen. destruct ref; try discriminate.
  inversion op_vcgen. clear op_vcgen. subst assertion'.
  simpl in CODE.
  replace (RT.C.ConstantPool.lookup (RT.C.class_constantpool class) t) with (Some (C.cpe_classref t0)) in CODE.
  destruct (RT.CP.resolve_class (RT.C.class_name class) t0 classes preclasses) as [classes' preserved only_add c c_exists | classes' preserved only_add exn].
   (* class resolution succeeded *)
   destruct (bool_informative (RT.C.class_abstract c)) as [c_abstract | c_not_abstract].
    (* c is abstract *)
    rewrite c_abstract in CODE. Focus 2.
    (* c is not abstract *)
    rewrite c_not_abstract in CODE. destruct (bool_informative (RT.C.class_interface c)) as [c_interface | c_not_interface].
     (* c is interface *)
     Focus 2.
     (* c not interface *)
     match goal with _:match ?x with Twosig.pack2 _ _ _ => _ end = result |- _ => destruct x as [heap0 addr [H1 [H2 [H3 [H4 H5]]]]] end.
     left.
     match goal with _:E.cont ?s = result |- _ => exists s end. split.
      assumption.
      assert (sat allowed_res (f_tensor (f_atom (R_new t0)) a_Spc)).
       eapply implies_soundness; eassumption.
      simpl in H. destruct H as [r1 [r2 [r1r2_allowed [t0_r1 r2_aSpc]]]].
      eapply mk_safe_state.
       eapply mk_safe_current_frame.
        auto.
        eassumption.
        eassumption.
        apply r2_aSpc.
       eapply resource_shuffle; eauto. eapply leq_trans.
        eapply leq_refl. apply r_new_match.
        assumption.
   (* class resolution failed *)


setoid_rewrite (r_new_match t0).  
        
assumption.
     

     destruct (RT.heap_new (RT.preserve_cert_heap heap preserved t0 

  change C.class with RT.C.class in class.
  change C.B.Classname.t with RT.C.B.Classname.t in t0.
  change (C.ConstantPool.lookup (C.class_constantpool class) t = Some (C.cpe_classref t0))
    with (RT.C.ConstantPool.lookup (RT.C.class_constantpool class) t = Some (RT.C.cpe_classref t0)) in lookup_ref.

(* op_iconst *)
simpl in CODE.
simpl in op_vcgen.
left.
match goal with _:E.cont ?s = result |- _ => exists s end. split.
 assumption.
 eapply mk_safe_state.
  eapply mk_safe_current_frame; intuition.
   apply code_safe.
   apply op_vcgen.
   eapply implies_soundness; eassumption.
  assumption.

   






