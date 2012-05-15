Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import RuntimeDatatypesIface.
Require Import ILLInterfaces.
Require Execution.
Require Import List.

Module ExecutionBisim (B:BASICS)
                      (RA1:RESOURCE_ALGEBRA)
                      (RAC1:RESOURCE_ALGEBRA_CONSTANTS with Module B:=B with Module RA:=RA1)
                      (RA2:RESOURCE_ALGEBRA)
                      (RAC2:RESOURCE_ALGEBRA_CONSTANTS with Module B:=B with Module RA:=RA2)
                      (C:CLASSDATATYPES with Module B:=B)
                      (CP:CLASSPOOL with Module B:=B with Module C:=C)
                      (RDT:RUNTIME_DATATYPES with Module B:=B with Module C:=C with Module CP:=CP).

Module E1 := Execution.Execution B RA1 RAC1 C CP RDT.
Module E2 := Execution.Execution B RA2 RAC2 C CP RDT.

Inductive state_rel : E1.state -> E2.state -> Prop :=
| mk_state_rel : forall fs cp h sf r1 r2,
   state_rel (RDT.mkState fs cp h sf r1) (RDT.mkState fs cp h sf r2).

Inductive exec_result_rel : E1.exec_result -> E2.exec_result -> Prop :=
| rel_cont : forall s1 s2,
   state_rel s1 s2 ->
   exec_result_rel (E1.cont s1) (E2.cont s2)
| rel_stop : forall s1 s2 ov,
   state_rel s1 s2 ->
   exec_result_rel (E1.stop s1 ov) (E2.stop s2 ov)
| rel_stop_exn : forall s1 s2 a,
   state_rel s1 s2 ->
   exec_result_rel (E1.stop_exn s1 a) (E2.stop_exn s2 a)
| rel_wrong :
   exec_result_rel E1.wrong E2.wrong.

Hint Resolve rel_cont rel_stop rel_stop_exn rel_wrong mk_state_rel.

Ltac do_destruct :=
  first [ match goal with |- exec_result_rel (_ (match ?x with E1.mkResInfo _ _ => _ end) _) (_ (match ?y with E2.mkResInfo _ _ => _ end) _) => destruct x; destruct y end
        | match goal with |- exec_result_rel (match ?x with nil => _ | cons _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match match ?r1 with E1.mkResInfo _ _ => _ end with Some _ => _ | None => _ end)
                                             (match match ?r2 with E2.mkResInfo _ _ => _ end with Some _ => _ | None => _ end) =>
           destruct r1; destruct r2 end
        | match goal with |- exec_result_rel (match match ?b1 with left _ => _ | right _ => _ end with Some _ => _ | None => _ end)
                                             (match match ?b2 with left _ => _ | right _ => _ end with Some _ => _ | None => _ end) =>
           destruct b1; destruct b2 end
        | match goal with |- exec_result_rel (match match ?x with 0 => _ | S _ => _ end with None => _ | Some _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.rt_int _ => _ | RDT.rt_addr _ => _ | RDT.rt_long => _ | RDT.rt_double => _ | RDT.rt_float => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with Some _ => _ | None => _ end) _ => destruct x end
        | match goal with |- exec_result_rel _ (match ?x with Some _ => _ | None => _ end) => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.C.category1 => _ | RDT.C.category2 => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.C.cpe_methodref _ _ _ => _ | RDT.C.cpe_interfacemethodref _ _ _ => _ | RDT.C.cpe_fieldref _ _ _ => _ | RDT.C.cpe_int _ => _ | RDT.C.cpe_classref _ => _ | RDT.C.cpe_other => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.CP.load_ok _ _ _ _ _ => _ | RDT.CP.load_err _ _ _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.hp_object _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with conj _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with E1.mkResInfo _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with true => _ | false => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with inleft _ => _ | inright _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with inl _ => _ | inr _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.CP.pack2  _ _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with (_,_) => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.mkFrame _ _ _ _ _ => _ end) _ => destruct x end
        | match goal with |- exec_result_rel (match ?x with RDT.mkState _ _ _ _ _ => _ end) _ => destruct x end
        ].

Inductive handler_result_rel : E1.find_handler_result -> E2.find_handler_result -> Prop :=
| rel_found : forall n,
   handler_result_rel (E1.handler_found n) (E2.handler_found n)
| rel_notfound :
   handler_result_rel (E1.handler_notfound) E2.handler_notfound
| rel_hwrong :
   handler_result_rel E1.handler_wrong E2.handler_wrong.

Hint Resolve rel_found rel_notfound rel_hwrong.

Lemma search_handlers_bisim : forall cp h pc cl cnm,
  handler_result_rel (E1.search_handlers cp h pc cl cnm) (E2.search_handlers cp h pc cl cnm).
intros. induction h.
 simpl. auto.
 simpl. destruct a; auto.
 destruct (RDT.C.is_within exc_start_pc exc_end_pc pc); auto.
 destruct exc_catch_type; auto.
 destruct (RDT.C.ConstantPool.lookup (RDT.C.class_constantpool cl) t); auto.
 destruct o; auto.
 destruct (RDT.CP.check_assignable cp cnm t0); auto.
Save.

Lemma unwind_stack_eq : forall cp fs n cnm,
  E1.unwind_stack cp fs n cnm = E2.unwind_stack cp fs n cnm.
intros. induction fs.
 reflexivity.
 simpl. destruct a.
 assert (X:handler_result_rel (E1.search_handlers cp (RDT.C.code_exception_table frame_code) frame_pc frame_class cnm)
                              (E2.search_handlers cp (RDT.C.code_exception_table frame_code) frame_pc frame_class cnm)).
  apply search_handlers_bisim.
 inversion X; auto.
Save.

Lemma throw_exception_bisim : forall fs cp h sf r1 r2 n,
  exec_result_rel (E1.throw_exception (RDT.mkState fs cp h sf r1) n)
                  (E2.throw_exception (RDT.mkState fs cp h sf r2) n).
intros. simpl.
do_destruct; auto.
do_destruct.
rewrite unwind_stack_eq.
do_destruct; auto.
do_destruct; auto.
Save.

Lemma pop_n_eq : forall n l,
  E1.pop_n n l = E2.pop_n n l.
intros. generalize n. clear n. induction l.
 reflexivity.
 destruct n.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Save.

Lemma stack_to_lvars_eq : forall l n,
  E1.stack_to_lvars l n = E2.stack_to_lvars l n.
induction l.
 trivial.
 intros. simpl. destruct (RDT.val_category a).
  destruct n.
   reflexivity.
   rewrite IHl. reflexivity.
  destruct n.
   reflexivity.
   destruct n.
    reflexivity.
    rewrite IHl. reflexivity.
Save.

Ltac do_destructs := simpl; auto; repeat (do_destruct;
                                          unfold E1.update_lvars; unfold E2.update_lvars;
                                          unfold E1.gather_class_exists_evidence; unfold E2.gather_class_exists_evidence;
                                          unfold E1.option_addr_eq_dec; unfold E2.option_addr_eq_dec;
                                          try (rewrite pop_n_eq); try (rewrite stack_to_lvars_eq);
                                          first [apply throw_exception_bisim|auto]).

Lemma bisim : forall p s1 s2,
  state_rel s1 s2 ->
  exec_result_rel (E1.exec p s1) (E2.exec p s2).
intros p s1 s2 s1_R_s2.
inversion s1_R_s2. clear s1_R_s2. subst.
do_destructs. destruct o; auto; try (do_destructs; case a0; case a; intros; do_destructs).

do_destructs. 
match goal with |- exec_result_rel (_ (match ?x with E1.mkResInfo _ _ => _ end)) (_ (match ?y with E2.mkResInfo _ _ => _ end)) => destruct x; destruct y end.
auto.

simpl. do_destruct; auto.
do_destruct; auto.
do_destruct; auto.
do_destruct; auto.
do_destruct; auto.
do_destruct; auto.
assert (X:handler_result_rel (E1.search_handlers cp (RDT.C.code_exception_table frame_code) frame_pc frame_class t)
                              (E2.search_handlers cp (RDT.C.code_exception_table frame_code) frame_pc frame_class t)).
 apply search_handlers_bisim.
inversion X; auto.
rewrite unwind_stack_eq.
do_destructs.
do_destructs.
Save.

End ExecutionBisim.
