Require Import Certificates.
Require Import ClassDatatypesIface.
Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import List.
Require Import OptionMonad.
Require Import OptionExt.
Require Import DestructExt.

Module ResInstructionVerifier (B0    : BASICS)
                              (SYN0  : ILL_SYNTAX with Module SYN.B := B0)
                              (CERT0 : CERTIFICATE with Definition asn := SYN0.SYN.formula)
                              (C0    : CLASSDATATYPES with Module B := B0).

Module B := B0.
Module SYN := SYN0.
Module CERT := CERT0.
Module C := C0.

Import SYN.
Import CERT.

Section VerifiedInstruction.

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

Hint Constructors exception_handlers_assertion.

Fixpoint check_exception_handlers (pc:nat) (eh:list C.exception_handler) {struct eh} : option formula :=
 match eh with
 | nil =>
    ret exceptional_ensures
 | C.mkExcHandler start_pc end_pc handler_pc catch_type::handlers =>
    a <- check_exception_handlers pc handlers;:
    if C.is_within start_pc end_pc pc then
      a' <- Cert.lookup cert handler_pc;:
      ret (f_and a' a)
    else
      ret a
 end.

Lemma check_exception_handlers_sound : forall pc handlers a,
 check_exception_handlers pc handlers = Some a -> exception_handlers_assertion pc handlers a.
induction handlers as [|[start_pc end_pc handler_pc check_type] handlers]; intros a CODE. 
 (* nil case *)
 inversion CODE. subst a. apply eha_nil.
 (* cons case *)
 unfold check_exception_handlers in CODE. fold check_exception_handlers in CODE.
 destruct (option_dec (check_exception_handlers pc handlers))
       as [[a' check_handlers_res] | check_handlers_res]; rewrite check_handlers_res in CODE.
  (* checking the handlers succeeded *)
  destruct (C.is_within start_pc end_pc pc) as [within | outwith].
   (* this handler is within *)
   destruct (option_dec (Cert.lookup cert handler_pc)) as [[a'' cert_lookup_res] | cert_lookup_res]; rewrite cert_lookup_res in CODE.
    (* lookup in certificate succeeded *)
    inversion CODE. subst a. eauto.
    (* lookup in certificate failed *)
    discriminate.
   (* this handler is not applicable here *)
   inversion CODE. subst a. eauto.
  (* checking handlers failed *)
  discriminate.
Save.

Hint Resolve check_exception_handlers_sound.

Hypothesis exception_handlers : list C.exception_handler.

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
| v_goto : forall pc a a' offset target,
   C.pc_plus_offset pc offset = Some target ->
   Cert.lookup cert target = Some a ->
   Cert.lookup cert (S pc) = Some a' ->
   instruction_precondition (C.op_goto offset) pc (f_and a a')
| v_valreturn : forall pc ty,
   instruction_precondition (C.op_valreturn ty) pc ensures
| v_return : forall pc,
   instruction_precondition C.op_return pc ensures
| v_athrow : forall pc a,
   exception_handlers_assertion pc exception_handlers a ->
   instruction_precondition C.op_athrow pc a

 (* OO instructions *)
| v_new : forall pc a idx clsnm,
   Cert.lookup cert (S pc) = Some a ->
   C.ConstantPool.lookup constantpool idx = Some (C.cpe_classref clsnm) ->
   (* FIXME: also that the reference is actually resolvable and an instantiable class *)
   instruction_precondition (C.op_new idx) pc (f_tensor (f_atom (R_new clsnm)) a)

 (* Stack Operations *)
| v_dup : forall pc a,
   Cert.lookup cert (S pc) = Some a ->
   instruction_precondition C.op_dup pc a.

Hint Constructors instruction_precondition.

Definition get_instruction_precondition : C.opcode -> nat -> option formula :=
 fun op pc =>
 match op with
  (* Constants *)
 | C.op_iconst _
  (* Local variables *)
 | C.op_load _ _
 | C.op_store _ _
  (* Arithmetic *)
 | C.op_iarithb _
 | C.op_iarithu _
  (* Stack operations *)
 | C.op_dup =>
   Cert.lookup cert (S pc)
  (* Control flow *)
 | C.op_if_acmp _ offset
 | C.op_if_icmp _ offset
 | C.op_if _ offset
 | C.op_ifnonnull offset
 | C.op_ifnull offset
 | C.op_goto offset =>
   target <- C.pc_plus_offset pc offset;:
   a <- Cert.lookup cert target;:
   a' <- Cert.lookup cert (S pc);:
   ret (f_and a a')
 | C.op_valreturn _
 | C.op_return =>
   ret ensures
 | C.op_athrow =>
   check_exception_handlers pc exception_handlers
  (* OO instructions *)
 | C.op_new idx =>
   a <- Cert.lookup cert (S pc);:
   ref <- C.ConstantPool.lookup constantpool idx;:
   match ref with
   | C.cpe_classref clsnm =>
      ret (f_tensor (f_atom (R_new clsnm)) a)
   | _ =>
      fail
   end
 | _ => fail
 end.

Lemma get_instruction_precondition_sound : forall op pc asn,
  get_instruction_precondition op pc = Some asn -> instruction_precondition op pc asn.
destruct op; intros pc asrn CODE;
  try discriminate; unfold get_instruction_precondition in CODE; 
 first [
   (* handles most instructions with only one step of verification *)
   eauto; fail
 | (* op_new *)
   destruct (option_dec (Cert.lookup cert (S pc))) as [[a cert_lookup_res] | cert_lookup_res]; rewrite cert_lookup_res in CODE; [|discriminate];
   destruct (option_dec (C.ConstantPool.lookup constantpool t)) as [[ref cp_lookup_res] | cp_lookup_res]; rewrite cp_lookup_res in CODE; [|discriminate];
   simpl in CODE; destruct ref; try discriminate;
   inversion CODE; subst asrn; eauto
 | (* op_if_acmp and friends *)
   destruct (option_dec (C.pc_plus_offset pc z)) as [[target ppo_res] | ppo_res]; rewrite ppo_res in CODE; [|discriminate];
   simpl in CODE;
   destruct (option_dec (Cert.lookup cert target)) as [[a' cert_target_res] | cert_target_res]; rewrite cert_target_res in CODE; [|discriminate];
   destruct (option_dec (Cert.lookup cert (S pc))) as [[a'' cert_Spc_res] | cert_Spc_res]; rewrite cert_Spc_res in CODE; [|discriminate];
   inversion CODE; subst asrn; eauto
 | (* op_(val)return *)
   inversion CODE; subst asrn; eauto
 ].
Save.

End VerifiedInstruction.

Hint Resolve cert_incl_lookup.
Hint Constructors instruction_precondition exception_handlers_assertion.

Lemma cert_incl_eha : forall cert cert' exensures pc handlers a,
 cert_incl cert cert' ->
 exception_handlers_assertion cert exensures pc handlers a ->
 exception_handlers_assertion cert' exensures pc handlers a.
intros cert cert' exensures pc handlers a cert_in_cert' eha_cert.
induction eha_cert; eauto.
Save.

Hint Resolve cert_incl_eha.

Lemma cert_incl_instruction_precondition : forall cert cert' cp ensures exensures handlers op pc a,
  cert_incl cert cert' ->
  instruction_precondition cert cp ensures exensures handlers op pc a ->
  instruction_precondition cert' cp ensures exensures handlers op pc a.
intros cert cert' cp ensures exensures handlers op pc a cert_in_cert' cert_v.
destruct cert_v; eauto.
Save.

End ResInstructionVerifier.
