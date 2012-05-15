Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import Store.
Require Import ClassDatatypesIface.
Require Import BasicMachineTypes.
Require Import AnnotationIface.
Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import RelationUtils.
Require Omega.

Module MkClassDatatypes (B : BASICS) (A : ANNOTATION B)
                      : CLASSDATATYPES B A.

(* Constants *)
Inductive double_constant : Set := d0 | d1 : double_constant.
Inductive float_constant : Set := f0 | f1 | f2 : float_constant.
Inductive long_constant : Set := l0 | l1 : long_constant.

(* Comparison operations *)
Inductive acmp : Set := acmp_eq | acmp_ne : acmp.
Inductive cmp : Set := cmp_eq | cmp_ne | cmp_lt | cmp_ge | cmp_gt | cmp_le : cmp.
Inductive float_cmp_opt : Set := fcmp_l | fcmp_g : float_cmp_opt.

(* Arithmetic operations *)
Inductive integer_bop : Set :=
 iadd | idiv | iand | imul | ior | irem | ishl | ishr | isub | iushr | ixor : integer_bop.

Inductive integer_uop : Set :=
 ineg : integer_uop.

Inductive float_bop : Set :=
 fadd | fdiv | fmul | frem | fsub : float_bop.

Inductive float_uop : Set :=
 fneg : float_uop.

Inductive array_type : Set :=
 aty_boolean | aty_char | aty_float | aty_double | aty_byte | aty_short | aty_int | aty_long : array_type.

Inductive stack_type : Set :=
 sty_int | sty_long | sty_double | sty_float | sty_addr.

Inductive opcode : Set :=
(* Arithmetic *)
| op_iarithb : integer_bop -> opcode
| op_iarithu : integer_uop -> opcode
| op_larithb : integer_bop -> opcode
| op_larithu : integer_uop -> opcode
| op_iinc    : nat -> B.Int32.t -> opcode
| op_darithb : float_bop -> opcode
| op_darithu : float_uop -> opcode
| op_farithb : float_bop -> opcode
| op_farithu : float_uop -> opcode

(* Stack Operations *)
| op_dup     : opcode
| op_dup_x1  : opcode
| op_dup_x2  : opcode
| op_dup2    : opcode
| op_dup2_x1 : opcode
| op_dup2_x2 : opcode
| op_nop     : opcode
| op_pop     : opcode
| op_pop2    : opcode
| op_swap    : opcode

(* Local Variables *)
| op_load   : stack_type -> nat -> opcode
| op_store  : stack_type -> nat -> opcode

(* OO *)
| op_instanceof      : B.ConstantPoolRef.t -> opcode
| op_invokeinterface : B.ConstantPoolRef.t -> opcode
| op_invokespecial   : B.ConstantPoolRef.t -> opcode
| op_invokestatic    : B.ConstantPoolRef.t -> opcode
| op_invokevirtual   : B.ConstantPoolRef.t -> opcode
| op_aconst_null     : opcode
| op_checkcast       : B.ConstantPoolRef.t -> opcode
| op_getfield        : B.ConstantPoolRef.t -> opcode
| op_getstatic       : B.ConstantPoolRef.t -> opcode
| op_new             : B.ConstantPoolRef.t -> opcode
| op_putfield        : B.ConstantPoolRef.t -> opcode
| op_putstatic       : B.ConstantPoolRef.t -> opcode

(* Comparisons and flow control *)
| op_if_acmp : acmp -> Z -> opcode
| op_if_icmp : cmp -> Z -> opcode
| op_if      : cmp -> Z -> opcode
| op_ifnonnull : Z -> opcode
| op_ifnull  : Z -> opcode
| op_goto    : Z -> opcode
| op_valreturn : stack_type -> opcode
| op_return  : opcode
| op_athrow  : opcode
| op_dcmp    : float_cmp_opt -> opcode
| op_fcmp    : float_cmp_opt -> opcode
| op_lcmp    : opcode
| op_lookupswitch : Z -> Z -> list (Z * Z) -> opcode
| op_tableswitch : Z -> Z -> Z -> list Z -> opcode

(* Arrays *)
| op_iaload  : opcode
| op_iastore : opcode
| op_aaload  : opcode
| op_aastore : opcode
| op_anewarray : B.ConstantPoolRef.t -> opcode
| op_arraylength : opcode
| op_baload  : opcode
| op_bastore : opcode
| op_caload  : opcode
| op_castore : opcode
| op_daload  : opcode
| op_dastore : opcode
| op_faload  : opcode
| op_fastore : opcode
| op_laload  : opcode
| op_lastore : opcode
| op_multianewarray : B.ConstantPoolRef.t -> nat -> opcode
| op_newarray : array_type -> opcode
| op_saload  : opcode
| op_sastore : opcode

(* Constants *)
| op_iconst : B.Int32.t -> opcode
| op_dconst : double_constant -> opcode
| op_fconst : float_constant -> opcode
| op_lconst : long_constant -> opcode
| op_ldc    : B.ConstantPoolRef.t -> opcode
| op_ldc2   : B.ConstantPoolRef.t -> opcode

(* Concurrency *)
| op_monitorenter : opcode
| op_monitorexit  : opcode

(* Conversions *)
| op_i2b    : opcode
| op_i2c    : opcode
| op_i2d    : opcode
| op_i2f    : opcode
| op_i2l    : opcode
| op_i2s    : opcode
| op_d2f    : opcode
| op_d2i    : opcode
| op_d2l    : opcode
| op_f2d    : opcode
| op_f2i    : opcode
| op_f2l    : opcode
| op_l2d    : opcode
| op_l2f    : opcode
| op_l2i    : opcode.

Definition pc_plus_offset : nat -> Z -> option nat :=
  fun pc offset =>
  match (Z_of_nat pc + offset)%Z with
  | Z0 => Some 0%nat
  | Zpos p => Some (nat_of_P p)
  | Zneg _ => None
  end.

(* Java types, equality and an ordering upon them *)

Inductive java_type : Set :=
| ty_byte
| ty_char
| ty_double
| ty_float
| ty_int
| ty_long
| ty_boolean
| ty_short : java_type
| ty_ref : java_ref_type -> java_type
with java_ref_type : Set :=
| ty_obj : B.Classname.t -> java_ref_type
| ty_arr : java_type -> java_ref_type.

Scheme java_type_ref_typeP := Induction for java_type Sort Prop
  with java_ref_type_typeP := Induction for java_ref_type Sort Prop.

Scheme java_type_ref_typeT := Induction for java_type Sort Type
  with java_ref_type_typeT := Induction for java_ref_type Sort Type.

Module JavaType_as_UOT : UsualOrderedType with Definition t := java_type.

Definition t := java_type.

Definition ref_eq := (@eq java_ref_type).
Definition eq := (@eq java_type).

Definition eq_refl := (@refl_equal java_type).
Definition eq_sym := (@sym_eq java_type).
Definition eq_trans := (@trans_eq java_type).

Fixpoint lt (a:java_type) (b:java_type) {struct a} : Prop :=
 match a with
 | ty_byte =>
    match b with
    | ty_byte => False
    | _       => True
    end
 | ty_char =>
    match b with
    | ty_byte | ty_char => False
    | _ => True
    end
 | ty_double =>
    match b with
    | ty_byte | ty_char | ty_double => False
    | _ => True
    end
 | ty_long =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long => False
    | _ => True
    end
 | ty_int =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long | ty_int => False
    | _ => True
    end
 | ty_float =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long | ty_int | ty_float => False
    | _ => True
    end
 | ty_boolean =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long | ty_int | ty_float | ty_boolean => False
    | _ => True
    end
 | ty_short =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long | ty_int | ty_float | ty_boolean | ty_short => False
    | _ => True
    end
 | ty_ref rt1 =>
    match b with
    | ty_byte | ty_char | ty_double | ty_long | ty_int | ty_float | ty_boolean | ty_short => False
    | ty_ref rt2 => lt_ref rt1 rt2
    end
 end
with lt_ref (a:java_ref_type) (b:java_ref_type) {struct a} : Prop :=
 match a with
 | ty_obj nm1 =>
    match b with
    | ty_obj nm2 => B.Classname.lt nm1 nm2
    | ty_arr _   => True
    end
 | ty_arr t1 =>
    match b with
    | ty_obj _ => False
    | ty_arr t2 => lt t1 t2
    end
 end.

Lemma lt_trans : transitive _ lt.
unfold transitive.
intro x.
elim x using (java_type_ref_typeP (fun x => forall y z, lt x y -> lt y z -> lt x z)
                                  (fun x => forall y z, lt_ref x y -> lt_ref y z -> lt_ref x z)); intros;
first [ destruct y; destruct z; simpl; intuition eauto; fail
      | inversion H0
      | destruct y; try (inversion H0); destruct z; try (inversion H1); simpl in *; intuition eauto
      ].
Save.

Lemma lt_not_eq : forall j1 j2, lt j1 j2 -> ~eq j1 j2.
intro j1.
elim j1 using (java_type_ref_typeP (fun j1 => forall j2, lt j1 j2 -> ~eq j1 j2)
                                   (fun j1 => forall j2, lt_ref j1 j2 -> j1<>j2));
destruct j2; simpl; intuition; try discriminate.
inversion H1. eauto.
inversion H0. apply (B.Classname.lt_not_eq H H2).
inversion H1. eauto.
Save.

Lemma java_type_eq_lt : forall x y z, eq x y -> lt y z -> lt x z.
intros. unfold eq in H. subst. assumption.
Save.

Lemma java_type_lt_eq : forall x y z, eq x y -> lt z y -> lt z x.
unfold eq. intros. subst. assumption.
Save.

Hint Unfold symmetric reflexive transitive lt eq lt_ref ref_eq.
Hint Immediate eq_sym.
Hint Resolve eq_refl eq_trans lt_trans lt_not_eq java_type_lt_eq java_type_eq_lt.
Hint Constructors Compare.

Definition compare : forall x y, Compare lt eq x y.
intro x.
elim x using (java_type_ref_typeT (fun x => forall y, Compare lt eq x y)
                                  (fun x => forall y, Compare lt_ref ref_eq x y));
 destruct y; intuition eauto.
 destruct (H j0); intuition eauto. apply EQ. rewrite r. apply eq_refl.
 destruct (B.Classname.compare t0 t1); unfold B.Classname.eq in *; subst; intuition eauto.
 destruct (H j0); intuition eauto. apply EQ. rewrite e. unfold ref_eq. reflexivity.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.


End JavaType_as_UOT.

Inductive value_category : Set := category1 | category2.

Definition java_type_category : java_type -> value_category :=
  fun ty => match ty with
  | ty_byte => category1
  | ty_char => category1
  | ty_short => category1
  | ty_boolean => category1
  | ty_int => category1
  | ty_float => category1
  | ty_ref _ => category1
  | ty_double => category2
  | ty_long => category2
  end.

Definition stack_type_category : stack_type -> value_category :=
  fun ty => match ty with
  | sty_int => category1
  | sty_float => category1
  | sty_double => category2
  | sty_addr => category1
  | sty_long => category2
  end.

Record descriptor : Set := mkDescriptor
 { descriptor_ret_type : option java_type
 ; descriptor_arg_types : list java_type
 }.

Module Descriptor_as_UOT <: UsualOrderedType with Definition t := descriptor.

Definition t := descriptor.

Module OJT : UsualOrderedType with Definition t := option java_type := OptionUsualOrderedType JavaType_as_UOT.
Module LJT : UsualOrderedType with Definition t := list java_type := ListUsualOrderedType JavaType_as_UOT.
Module OJTFacts := OrderedTypeFacts OJT.

Definition eq := @eq descriptor.
Definition eq_refl := @refl_equal descriptor.
Definition eq_sym := @sym_eq descriptor.
Definition eq_trans := @trans_eq descriptor.

Hint Unfold OJT.eq.
Hint Resolve OJT.lt_trans OJT.eq_trans LJT.lt_trans.

Definition lt (d1 d2:descriptor) :=
 match d1, d2 with
 | mkDescriptor rt1 at1, mkDescriptor rt2 at2 =>
    OJT.lt rt1 rt2 \/ OJT.eq rt1 rt2 /\ LJT.lt at1 at2
 end.

Lemma lt_trans : transitive _ lt.
unfold transitive. destruct x. destruct y. destruct z. simpl. intuition eauto.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
destruct x. destruct y. simpl. intuition eauto.
 unfold eq in H0. inversion H0. apply (OJT.lt_not_eq _ _ H1 H2).
 unfold eq in H0. inversion H0. apply (LJT.lt_not_eq _ _ H2 H4).
Save.

Hint Immediate eq_sym.
Hint Resolve eq_refl eq_trans lt_trans lt_not_eq.
Hint Unfold eq lt OJT.eq LJT.eq.
Hint Constructors Compare.

Definition compare : forall x y, Compare lt eq x y.
destruct x. destruct y.
destruct (OJT.compare descriptor_ret_type0 descriptor_ret_type1);
destruct (LJT.compare descriptor_arg_types0 descriptor_arg_types1);
 intuition eauto 6.
 apply EQ. unfold OJT.eq in e. unfold LJT.eq in e0. subst. unfold eq. reflexivity.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.

End Descriptor_as_UOT.

Record exception_handler : Set := mkExcHandler
  { exc_start_pc : nat
  ; exc_end_pc   : nat
  ; exc_handler_pc : nat
  ; exc_catch_type : option B.ConstantPoolRef.t
  }.

(* for checking if the current program counter is in the range of an exception handler *)
Definition is_within : forall (s e p:nat), ({p >= s /\ p < e} + {p < s \/ p >= e})%nat.
intros. destruct (le_lt_dec s p). 
 destruct (le_lt_dec e p).
  right. omega. 
  left. omega.
 right. omega.
Defined.

Record precode : Type := mkPreCode
  { precode_max_stack       : nat
  ; precode_max_lvars       : nat
  ; precode_code            : list opcode            (* FIXME: need a better representation than lists *)
  ; precode_exception_table : list exception_handler
  ; precode_annot           : A.code_annotation
  }. (* + certificate *)

Record code : Set := mkCode
  { code_max_stack       : nat
  ; code_max_lvars       : nat
  ; code_code            : list opcode
  ; code_exception_table : list exception_handler
  }. (* + certificate *)

Record premethod : Type := mkPreMethod
  { premethod_name         : B.Methodname.t
  ; premethod_descriptor   : descriptor
  ; premethod_public       : bool
  ; premethod_protected    : bool
  ; premethod_private      : bool
  ; premethod_abstract     : bool (* if this is false, and the code does not exist, then the method is native *)
  ; premethod_static       : bool
  ; premethod_final        : bool
  ; premethod_synchronized : bool
  ; premethod_strict       : bool
  ; premethod_code         : option precode
  ; premethod_annot        : A.method_annotation
  }. (* + attributes *)

Record method : Type := mkMethod
  { method_name         : B.Methodname.t
  ; method_descriptor   : descriptor
  ; method_public       : bool
  ; method_protected    : bool
  ; method_private      : bool
  ; method_abstract     : bool (* if this is false, and the code does not exist, then the method is native *)
  ; method_static       : bool
  ; method_final        : bool
  ; method_synchronized : bool
  ; method_strict       : bool
  ; method_code         : option code
  ; method_annot        : A.method_annotation
  }. (* + attributes *)

Module MethodDesc := PairUsualOrderedType B.Methodname Descriptor_as_UOT.
Module Method.
Definition t := method.
End Method.
Module MethodList := MkStore MethodDesc Method.

Record field : Set := mkField
  { field_name      : B.Fieldname.t
  ; field_type      : java_type
  ; field_public    : bool
  ; field_private   : bool
  ; field_protected : bool
  ; field_static    : bool
  ; field_final     : bool
  ; field_volatile  : bool
  ; field_transient : bool
  }. (* + attributes (ConstantValue) *)

Module FieldDesc := PairOrderedType B.Fieldname JavaType_as_UOT.
Module Field.
Definition t := field.
End Field.
Module FieldList := MkStore FieldDesc Field.

Inductive constantpool_entry : Set :=
| cpe_methodref : B.Classname.t -> B.Methodname.t -> descriptor -> constantpool_entry
| cpe_interfacemethodref : B.Classname.t -> B.Methodname.t -> descriptor -> constantpool_entry
| cpe_fieldref  : B.Classname.t -> B.Fieldname.t -> java_type -> constantpool_entry
| cpe_int       : B.Int32.t -> constantpool_entry
| cpe_classref  : B.Classname.t -> constantpool_entry
| cpe_other     : constantpool_entry.

Module ConstantPoolEntry.
Definition t := constantpool_entry.
End ConstantPoolEntry.
Module ConstantPool := MkStore B.ConstantPoolRef ConstantPoolEntry.

Record preclass : Type := mkPreClass
  { preclass_name         : B.Classname.t
  ; preclass_super_name   : option B.Classname.t
  ; preclass_super_interfaces : list B.Classname.t
  ; preclass_public       : bool
  ; preclass_final        : bool
  ; preclass_super        : bool
  ; preclass_interface    : bool
  ; preclass_abstract     : bool
  ; preclass_methods      : list premethod
  ; preclass_fields       : FieldList.t
  ; preclass_constantpool : ConstantPool.t
  ; preclass_annotation   : A.class_annotation
  }. (* + attributes *)

(*Module CP := FinitePoset.FinitePoset B.Classname.*)

Record class : Type := mkClass
  { class_name         : B.Classname.t
  ; class_super_class  : option B.Classname.t
  ; class_interfaces   : list B.Classname.t
  ; class_public       : bool
  ; class_final        : bool
  ; class_super        : bool
  ; class_interface    : bool
  ; class_abstract     : bool
  ; class_methods      : MethodList.t
  ; class_fields       : FieldList.t
  ; class_constantpool : ConstantPool.t
  }. (* + attributes *)

Inductive has_premethod : list premethod -> B.Methodname.t * descriptor -> premethod -> Prop :=
| has_premethod_cons_1 : forall nm d public protected private abstract static final synchronized strict code annot meths,
   has_premethod (mkPreMethod nm d public protected private abstract static final synchronized strict code annot::meths)
                 (nm,d)
                 (mkPreMethod nm d public protected private abstract static final synchronized strict code annot)
| has_premethod_cons_2 : forall nm d public protected private abstract static final synchronized strict code annot meths nm' d' m,
   has_premethod meths (nm',d') m ->
   (nm <> nm' \/ d <> d') ->
   has_premethod (mkPreMethod nm d public protected private abstract static final synchronized strict code annot::meths)
                 (nm',d')
                 m.

Definition descriptor_eq_dec : forall (d d':descriptor), {d=d'}+{d<>d'}.
intros. destruct (Descriptor_as_UOT.compare d d').
 right. apply Descriptor_as_UOT.lt_not_eq. apply l.
 left. apply e.
 right. unfold not. intros. symmetry in H. generalize H. apply Descriptor_as_UOT.lt_not_eq. apply l.
Save.

Definition mdesc_eq_dec : forall (d d' : B.Methodname.t * descriptor), {d=d'}+{d<>d'}.
decide equality. apply descriptor_eq_dec. apply B.Methodname.eq_dec.
Save. 

Definition has_premethod_dec : forall ms mdesc,
 (exists m, has_premethod ms mdesc m)\/(forall m, ~has_premethod ms mdesc m).
intros ms mdesc.
induction ms.
 (* ms -> nil *)
 right. unfold not. intros. inversion H.
 (* ms -> a::ms *)
 destruct a as [a b c d e f g h i j k l]. destruct mdesc as [a' b'].
 destruct (B.Methodname.eq_dec a a'); subst.
  destruct (descriptor_eq_dec b b'); subst.
   left. exists (mkPreMethod a' b' c d e f g h i j k l). constructor.
   destruct IHms as [[m ms_m] | not_ms_m].
    left. exists m. constructor; intuition.
    right. unfold not. intros. inversion H.
     contradiction.
     apply (not_ms_m _ H16).
  destruct IHms as [[m ms_m] | not_ms_m].
   left. exists m. constructor; intuition.
   right. unfold not. intros. inversion H.
    contradiction.
    apply (not_ms_m _ H16).
Save.

Lemma has_premethod_functional : forall ms mdesc mA mB,
 has_premethod ms mdesc mA ->
 has_premethod ms mdesc mB ->
 mA = mB.
induction ms; intros.
 inversion H.
 destruct a. inversion H; subst.
  inversion H0; subst.
   reflexivity.
   elimtype False. destruct H18; apply H1; reflexivity.
  inversion H0; subst.
   elimtype False. destruct H17; apply H1; reflexivity.
   eauto.
Save.

Lemma has_premethod_in : forall ms m,
  has_premethod ms (premethod_name m, premethod_descriptor m) m ->
  In m ms.
Proof.
  intros.
  induction H.
   simpl. left. reflexivity.
   simpl. right. assumption.
Qed.

Lemma has_premethod_name : forall ms md m,
  has_premethod ms md m -> md = (premethod_name m, premethod_descriptor m).
Proof.
  intros.
  induction H. reflexivity. assumption.
Qed.

End MkClassDatatypes.











