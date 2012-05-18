Require Import ZArith.
Require Import List.
Require Import Bool.
Require        BoolExt.
Require        OptionExt.
Require        ListExt.
Require Import Twosig.
Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import CertRuntimeTypesIface.
Require Import ResourceAlgebra.
Require Import JVMState.
Require Import NativeMethods.
Require Import AnnotationIface.
Require        FSetInterface.

Module Execution (B    : BASICS)
                 (RA   : RESOURCE_ALGEBRA B)
                 (ANN  : ANNOTATION B)
                 (C    : CLASSDATATYPES B ANN)
                 (CP   : CLASSPOOL B ANN C)
                 (A    : ASSIGNABILITY B ANN C CP)
                 (R    : RESOLUTION B ANN C CP A)
                 (VM   : VIRTUALMETHODLOOKUP B ANN C CP A)
                 (RDT  : CERTRUNTIMETYPES B ANN C CP A)
                 (JVM  : JVMSTATE B RA ANN C CP A R VM RDT)
                 (NATIVE : NATIVE_METHODS B RA ANN C CP A R VM RDT JVM)
                 (ClassnameSet :FSetInterface.S with Definition E.t := B.Classname.t with Definition E.eq := B.Classname.eq).


Import RDT.
Import JVM.

Section WithPreclasses.

Hypothesis preclasses : CP.Preclasspool.t.
Hypothesis privilegedclasses : ClassnameSet.t.

(* Exception handling *)
Section ExceptionHandling.

Hypothesis classes : CP.cert_classpool.

Inductive find_handler_result : Set :=
| handler_found : nat -> find_handler_result
| handler_notfound : find_handler_result
| handler_wrong : find_handler_result.

Definition search_handlers (handlers:list C.exception_handler)
                           (pc:nat)
                           (class:C.class)
                           (exc_cls:B.Classname.t)
                         : find_handler_result
  :=
  let fix search_handlers_aux (handlers:list C.exception_handler) : find_handler_result :=
        match handlers with
        | nil =>
           handler_notfound
        | C.mkExcHandler start_pc end_pc handler_pc opt_type_idx::handlers =>
           if C.is_within start_pc end_pc pc then
              match opt_type_idx with
              | None =>
                 handler_found handler_pc
              | Some type_idx =>
                 match C.ConstantPool.lookup (C.class_constantpool class) type_idx with
                 | Some (C.cpe_classref cls_nm) =>
                    if A.is_assignable classes (C.ty_obj exc_cls) (C.ty_obj cls_nm) then
                       handler_found handler_pc
                    else
                       search_handlers_aux handlers
                 | _ => handler_wrong
                 end
              end
           else
              search_handlers_aux handlers
        end in
    search_handlers_aux handlers.

Fixpoint unwind_stack (frames:list frame)
                      (ref:Heap.addr_t)
                      (exc_cls:B.Classname.t)
                      {struct frames}
                    : option (list frame)
  :=
  match frames with
  | nil => Some nil
  | mkFrame _ lvars pc code mth class::frames =>
     match search_handlers (C.code_exception_table code) pc class exc_cls with
     | handler_found pc =>
        Some (mkFrame (rt_addr (Some ref)::nil) lvars pc code mth class::frames)
     | handler_notfound =>
        unwind_stack frames ref exc_cls
     | handler_wrong =>
        None
     end
  end.

(* need to make this abstract by hiding the implementation and just specifying what happens:
 * - gets the least 
 *)

End ExceptionHandling.

Definition throw_exception : state -> Heap.addr_t -> exec_result :=
  fun state ref => match state with
  | mkState fs classes heap statics res reslimit =>
     match heap_lookup_class heap ref with
     | inleft (exist cls_nm _) =>
        match unwind_stack classes fs ref cls_nm with
        | Some nil =>
           stop_exn (mkState nil classes heap statics res reslimit) ref
        | Some fs =>
           cont (mkState fs classes heap statics res reslimit)
        | None => wrong
        end
     | inright _ => wrong
     end
  end.

Definition add_res_new : B.Classname.t -> state -> state :=
  fun clsnm state => match state with
  | mkState fs classes heap statics used reslimit =>
     let new_used := match RA.r_new clsnm with
                       | None => used
                       | Some r => RA.combine used r
                     end in
       mkState fs classes heap statics new_used reslimit
  end.

(* FIXME: this doesn't really create the objects properly: it never runs their initialiser, nor does it resolve the classes.
          we should add an invariant that states that the builtin exception classes have already been loaded *)
Definition throw_builtin_exception : state -> CP.exn -> exec_result :=
  fun state e => match state with
  | mkState fs classes heap statics res reslimit =>
     let cls_nm := CP.builtin_exception_to_class_name e in
     match CP.gather_class_exists_evidence classes cls_nm with (* FIXME: need an invariant that states that builtin exception classes always exist *)
     | inright evidence =>
        match heap_new heap cls_nm evidence with
        | pack2 heap' addr (conj _ (conj _ (conj _ (conj preserve _)))) =>
           let statics' := preserve_cert_fieldstore_over_heap statics preserve in
           let state' := add_res_new cls_nm (mkState fs classes heap' statics' res reslimit) in
            throw_exception state' addr
        end
     | inleft _ => wrong
     end
  end.

(* Instruction implementations *)

Definition exec_iconst : B.Int32.t -> state -> exec_result :=
  fun i state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     cont (mkState (mkFrame (rt_int i::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
  | _ => wrong
  end.

Definition exec_iarithb : C.integer_bop -> state -> exec_result :=
  fun op state => match state with
  | mkState (mkFrame (rt_int z2::rt_int z1::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let result := match op with
                   | C.iadd => Some (B.Int32.add z1 z2)
                   | C.isub => Some (B.Int32.sub z1 z2)
                   | C.imul => Some (B.Int32.mul z1 z2)
                   | C.iand => Some (B.Int32.logand z1 z2)
                   | C.ior  => Some (B.Int32.logor z1 z2)
                   | C.ixor => Some (B.Int32.logxor z1 z2)
                   | _    => None
                   end in
     match result with
     | None => undefined
     | Some z =>
        cont (mkState (mkFrame (rt_int z::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_iarithu : C.integer_uop -> state -> exec_result :=
  fun op state => match state with
  | mkState (mkFrame (rt_int i::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let r := match op with C.ineg => B.Int32.neg i end in
     cont (mkState (mkFrame (rt_int r::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
  | _ => wrong
  end.

Definition exec_load : nat -> state -> exec_result :=
  fun n state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match OptionExt.option_mult (nth_error lvars n) with
     | None => wrong
     | Some v =>
        cont (mkState (mkFrame (v::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition update_lvars : nat -> rt_val -> list (option rt_val) -> option (list (option rt_val)) :=
  fun n v lvars0 =>
  let olvars1 := match n with
                | O => Some lvars0
                | S n' =>
                   (* obliterate the preceding value if it is a category 2 one *)
                   match nth_error lvars0 n' with
                   | None => None
                   | Some None => Some lvars0
                   | Some (Some v) =>
                      match val_category v with
                      | C.category1 => Some lvars0
                      | C.category2 => ListExt.list_update lvars0 n' None
                      end
                   end
                end in
  match olvars1 with
  | None => None
  | Some lvars1 =>
     match ListExt.list_update lvars1 n (Some v) with
     | None => None
     | Some lvars2 =>
        match val_category v with
        | C.category1 => Some lvars2
        | C.category2 => ListExt.list_update lvars2 (S n) None
        end
     end
  end.

Definition exec_store : nat -> state -> exec_result :=
  fun n state => match state with
  | mkState (mkFrame (v::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match update_lvars n v lvars with
     | None => wrong
     | Some new_lvars =>
        cont (mkState (mkFrame op_stack new_lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition update_reslimit (cls:C.class) (mth:C.method) (limit:RA.res) :=
  match ANN.grants (C.method_annot mth) with
    | None => limit
    | Some grant =>
      if ClassnameSet.mem (C.class_name cls) privilegedclasses then RA.combine limit (RA.res_parse grant) else limit
  end.

Definition exec_valreturn : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v::_) _ _ _ omth oclass::nil) classes heap statics res reslimit =>
     stop (mkState nil classes heap statics res (update_reslimit oclass omth reslimit)) (Some v)
  | mkState (mkFrame (v::_) _ _ _ omth oclass::mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     cont (mkState (mkFrame (v::op_stack) lvars (S pc) code mth class::fs) classes heap statics res (update_reslimit oclass omth reslimit))
  | _ =>
     wrong
  end.

Definition exec_return : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame _ _ _ _ omth oclass::nil) classes heap statics res reslimit =>
     stop (mkState nil classes heap statics res (update_reslimit oclass omth reslimit)) None
  | mkState (mkFrame _ _ _ _ omth oclass::mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res (update_reslimit oclass omth reslimit))
  | _ => wrong
  end.

Definition exec_goto : Z -> state -> exec_result :=
  fun offset state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.pc_plus_offset pc offset with
     | None => wrong
     | Some new_pc =>
        cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_dup : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v with
     | C.category1 =>
        cont (mkState (mkFrame (v::v::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | C.category2 =>
        wrong
     end
  | _ => wrong
  end.

Definition exec_dup_x1 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::v2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v1, val_category v2 with
     | C.category1, C.category1 =>
        cont (mkState (mkFrame (v1::v2::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | _,_ => wrong
     end
  | _ => wrong
  end.

Definition exec_dup_x2 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::v2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v1, val_category v2 with
     | C.category1, C.category1 =>
        match op_stack with
        | nil => wrong
        | v3::op_stack =>
           match val_category v3 with
           | C.category1 =>
              cont (mkState (mkFrame (v1::v2::v3::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
           | C.category2 =>
              wrong
           end
        end
     | C.category1, C.category2 =>
       cont (mkState (mkFrame (v1::v2::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | _,_ => wrong
     end
  | _ => wrong
  end.

Definition exec_dup2 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v1 with
     | C.category1 =>
        match op_stack with
        | nil => wrong
        | v2::op_stack =>
           cont (mkState (mkFrame (v1::v2::v1::v2::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
        end
     | C.category2 =>
        cont (mkState (mkFrame (v1::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_dup2_x1 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::v2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v1 with
     | C.category1 =>
        match op_stack with
        | nil => wrong
        | v3::op_stack =>
           cont (mkState (mkFrame (v1::v2::v3::v1::v2::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
        end
     | C.category2 =>
        cont (mkState (mkFrame (v1::v2::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_dup2_x2 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::v2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v2 with
     | C.category1 =>
        match op_stack with
        | nil => wrong
        | v3::op_stack =>
           match val_category v1, val_category v3 with
           | C.category1, C.category1 =>
              match op_stack with
              | nil => wrong
              | v4::op_stack =>
                 match val_category v4 with
                 | C.category1 =>
                    cont (mkState (mkFrame (v1::v2::v3::v4::v1::v2::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                 | C.category2 =>
                    wrong
                 end
              end
           | C.category1, C.category2 =>
              cont (mkState (mkFrame (v1::v2::v3::v1::v2::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
           | C.category2, C.category1 =>
              cont (mkState (mkFrame (v1::v2::v3::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
           | C.category2, C.category2 =>
              wrong
           end
        end
     | C.category2 =>
        match val_category v1 with
        | C.category1 => wrong
        | C.category2 =>
           cont (mkState (mkFrame (v1::v2::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
        end
     end
  | _ => wrong
  end.

Definition exec_nop : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
  | _ => wrong
  end.

Definition exec_pop : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v with
     | C.category1 =>
        cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | C.category2 =>
        wrong
     end
  | _ => wrong
  end.

Definition exec_pop2 : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v with
     | C.category1 =>
        match op_stack with
        | nil => wrong
        | _::op_stack =>
           cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
        end
     | C.category2 =>
        cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Fixpoint make_padding_lvars (n:nat) : list (option rt_val) :=
  match n with 0 => nil | S n => None::make_padding_lvars n end.

Definition default_value : C.java_type -> rt_val :=
  fun ty => match ty with
  | C.ty_byte    => rt_int B.Int32.zero
  | C.ty_int     => rt_int B.Int32.zero
  | C.ty_short   => rt_int B.Int32.zero
  | C.ty_char    => rt_int B.Int32.zero
  | C.ty_boolean => rt_int B.Int32.zero
  | C.ty_double  => rt_double
  | C.ty_float   => rt_float
  | C.ty_long    => rt_long
  | C.ty_ref _   => rt_addr None
  end.

Definition exec_putstatic : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame (v::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_fieldref cls_nm field_nm ty) =>
        match R.resolve_field (C.class_name class) cls_nm field_nm ty classes preclasses with
        | CP.load_ok classes preserved _ (c,f) (conj c_exists f_exists) =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           match BoolExt.bool_informative (C.field_static f) with
           | left is_static =>
              match type_check_rt_val classes heap v ty with
              | left well_typed =>
                 let f_ok := (ex_intro _ c (ex_intro _ f (conj c_exists (conj f_exists is_static)))) in
                 match fieldstore_update statics (C.class_name c) field_nm ty v well_typed f_ok with
                 | exist statics' _ =>
                    cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                 end
              | right _ =>
                 wrong
              end
            | right not_static =>
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
            end
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_getstatic : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_fieldref cls_nm field_nm ty) =>
        match R.resolve_field (C.class_name class) cls_nm field_nm ty classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ (c,f) (conj c_exists f_exists) =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           match BoolExt.bool_informative (C.field_static f) with
           | left f_static =>
              let f_ok := ex_intro _ c (ex_intro _ f (conj c_exists (conj f_exists f_static))) in
              match fieldstore_lookup statics (C.class_name c) field_nm ty f_ok with
              | exist v _ =>
                 cont (mkState (mkFrame (v::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
              end
           | right not_static =>
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
           end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_new : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_classref cls_nm) =>
        match R.resolve_class (C.class_name class) cls_nm classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ c c_exists =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           if C.class_abstract c then
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errInstantiation
           else match BoolExt.bool_informative (C.class_interface c) with
                | left is_interface =>
                  throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errInstantiation
                | right not_interface =>
                   match heap_new heap cls_nm (ex_intro _ c (conj c_exists not_interface)) with
                   | pack2 heap addr (conj _ (conj _ (conj _ (conj preserved _)))) => 
                      let statics := preserve_cert_fieldstore_over_heap statics preserved in
                      let state' := mkState (mkFrame (rt_addr (Some addr)::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit in
                       cont (add_res_new cls_nm state')
                   end
                end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_getfield : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_fieldref cls_nm field_nm ty) =>
        match R.resolve_field (C.class_name class) cls_nm field_nm ty classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ (c,f) (conj H1 H2) =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           if C.field_static f then
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
           else
              match a with
              | None =>
                 throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errNullPointer
              | Some a =>
                 match heap_lookup_field heap a (C.class_name c) (C.field_name f) ty with
                 | inleft (exist v _) =>
                    cont (mkState (mkFrame (v::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                 | inright _ =>
                    wrong
                 end
              end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_putfield : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame (v::rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_fieldref cls_nm field_nm ty) =>
        match R.resolve_field (C.class_name class) cls_nm field_nm ty classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ (c,f) (conj H1 H2) =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           if C.field_static f then
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
           else if C.field_final f &&
                   (if B.Classname.eq_dec (C.class_name class) (C.class_name c) then false else true) then
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIllegalAccess
           else
              match a with
              | None =>
                 throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errNullPointer
              | Some a =>
                 match type_check_rt_val classes heap v ty with
                 | left welltyped =>
                    match heap_update_field heap a (C.class_name c) (C.field_name f) ty v welltyped with
                    | inleft (exist heap (conj _ (conj preserved _))) =>
                       let statics := preserve_cert_fieldstore_over_heap statics preserved in
                       cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                    | inright _ =>
                       wrong
                    end
                 | right _ =>
                    wrong
                 end
              end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Fixpoint pop_n (n:nat) (l:list rt_val) {struct n} : option (list rt_val * list rt_val) :=
  match n, l with
  | 0,   l     => Some (nil,l)
  | S n, nil   => None
  | S n, v::vs => match pop_n n vs with None => None | Some (l',rest) => Some (v::l', rest) end
  end.

Fixpoint stack_to_lvars (stack:list rt_val) (required_lvars:nat) {struct stack} : option (list (option rt_val)) :=
  match stack with
  | nil      => Some (make_padding_lvars required_lvars)
  | v::stack =>
     match val_category v, required_lvars with
     | C.category1, S n     => 
        match stack_to_lvars stack n with
        | None => None
        | Some stack' => Some (Some v::stack')
        end
     | C.category2, S (S n) =>
        match stack_to_lvars stack n with
        | None => None
        | Some stack' => Some (Some v::None::stack')
        end
     | _, _ => None
     end
  end.

Definition basic_invoke : C.class -> C.method -> list rt_val -> state -> exec_result :=
  fun class method args state => match state with
  | mkState fs classes heap statics res reslimit =>
     match C.method_code method with
       (* Callers rule out abstract methods *)
     | None => 
       match NATIVE.native_invoke class method args state with
         | None => wrong
         | Some (NATIVE.Build_result (NATIVE.exn exn) classes' heap' statics' res' reslimit') =>
           throw_exception (mkState fs classes' heap' statics' res' reslimit') exn
         | Some (NATIVE.Build_result NATIVE.void classes' heap' statics' res' reslimit') =>
           match fs with
             | (mkFrame op_stack lvars pc code mth class::fs') =>
               cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs') classes' heap' statics' res' reslimit')
             | _ => wrong
           end
         | Some (NATIVE.Build_result (NATIVE.val val) classes' heap' statics' res' reslimit') =>
           match fs with
             | (mkFrame op_stack lvars pc code mth class::fs') =>
               cont (mkState (mkFrame (val::op_stack) lvars (S pc) code mth class::fs') classes' heap' statics' res' reslimit')
             | _ => wrong
           end
       end
     | Some code =>
        match stack_to_lvars args (C.code_max_lvars code) with
        | None => wrong
        | Some lvars =>
           cont (mkState (mkFrame nil lvars 0 code method class::fs) classes heap statics res reslimit)
        end
     end
  end.

Definition basic_invokestatic : B.Classname.t -> B.Classname.t -> B.Methodname.t -> C.descriptor -> list rt_val -> state -> exec_result :=
  fun caller clsname meth_name meth_desc args state => match state with
  | mkState fs classes heap statics res reslimit =>
     match R.resolve_method caller clsname meth_name meth_desc classes preclasses with
     | CP.load_err classes preserved _ e =>
        let heap := preserve_cert_heap heap preserved in
        let statics := preserve_cert_fieldstore_over_classes statics preserved in
        throw_builtin_exception (mkState fs classes heap statics res reslimit) e
     | CP.load_ok classes preserved _ (class,method) (conj H1 H2) =>
        let heap := preserve_cert_heap heap preserved in
        let statics := preserve_cert_fieldstore_over_classes statics preserved in
        if C.method_static method then
           basic_invoke class method args (mkState fs classes heap statics res reslimit)
        else
           throw_builtin_exception (mkState fs classes heap statics res reslimit) CP.errIncompatibleClassChange
     end
  end.

Definition exec_invokestatic : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_methodref clsname methname methdescrip) =>
        match pop_n (length (C.descriptor_arg_types methdescrip)) op_stack with
        | None => wrong
        | Some (args, op_stack) =>
           let state' := mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit in
           basic_invokestatic (C.class_name class) clsname methname methdescrip (rev args) state'
        end
     | _ => wrong
     end
  | _ => wrong
  end.

(* FIXME: need to properly understand the ACC_SUPER flag on page 284 *)
Definition exec_invokespecial : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_methodref clsname methname methdescrip) =>
        match R.resolve_method (C.class_name class) clsname methname methdescrip classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ (c,m) (conj H1 H2) =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           match pop_n (length (C.descriptor_arg_types methdescrip)) op_stack with
           | Some (preargs, rt_addr (Some addr)::op_stack) =>
              let args := rt_addr (Some addr)::rev preargs in
              if C.method_static m then
                 throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
              else if C.method_abstract m then
                 throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errAbstractMethod
              else (* FIXME: need a special check for instance initialization methods *)
                 let state' := mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit in
                 basic_invoke c m args state'
           | Some (args, rt_addr None::op_stack) =>
              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errNullPointer
           | _ => wrong
           end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_invokevirtual : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state =>
    match state with
      | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
        match C.ConstantPool.lookup (C.class_constantpool class) idx with
          | Some (C.cpe_methodref clsname methname methdescrip) =>
            match B.Methodname.eq_dec methname B.init with
              | left _ => wrong (* cannot call methods called '<init>' via invokevirtual *)
              | right _ =>
                match R.resolve_method (C.class_name class) clsname methname methdescrip classes preclasses with
                  | CP.load_err classes preserved _ e =>
                    let heap := preserve_cert_heap heap preserved in
                      let statics := preserve_cert_fieldstore_over_classes statics preserved in
                        throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
                  | CP.load_ok classes preserved _ (c,m) (conj H1 H2) =>
                    let heap := preserve_cert_heap heap preserved in
                      let statics := preserve_cert_fieldstore_over_classes statics preserved in
                        if C.method_static m then
                          throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
                          else
                            match pop_n (length (C.descriptor_arg_types methdescrip)) op_stack with
                              | Some (preargs, rt_addr (Some addr)::op_stack) =>
                                let args := rt_addr (Some addr)::rev preargs in
                                  match heap_lookup_class heap addr with
                                    | inleft (exist cls_nm addr_is_cls_nm) =>
                                      if A.is_assignable classes (C.ty_obj cls_nm) (C.ty_obj clsname) then
                                        let evidence := object_class_implies_class_exists addr_is_cls_nm in
                                          match VM.lookup_virtual_method classes cls_nm (methname, methdescrip) evidence with
                                            | Some (pack2 c' m' _) =>
                                              if C.method_abstract m' then
                                                throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errAbstractMethod
                                                else
                                                  let state' := mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit in
                                                    basic_invoke c' m' args state'
                                            | None =>
                                              throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errAbstractMethod
                                          end
                                        else
                                          wrong
                                    | inright _ => wrong
                                  end
                              | Some (_, rt_addr None::op_stack) =>
                                throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errNullPointer
                              | _ => wrong
                            end
                end
            end
          | _ => wrong
        end
      | _ => wrong
    end.

Definition exec_invokeinterface : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_interfacemethodref clsname methname methdescrip) =>
       match B.Methodname.eq_dec methname B.init with
       | left _ => wrong (* cannot call methods called '<init>' via invokeinterface *)
       | right _ =>
         match R.resolve_interface_method (C.class_name class) clsname methname methdescrip classes preclasses with
         | CP.load_err classes preserved _ e =>
            let heap := preserve_cert_heap heap preserved in
            let statics := preserve_cert_fieldstore_over_classes statics preserved in
            throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
         | CP.load_ok classes preserved _ (c,m) (conj H1 H2) =>
            let heap := preserve_cert_heap heap preserved in
            let statics := preserve_cert_fieldstore_over_classes statics preserved in
            if C.method_static m then (* FIXME: this should be automatic from the fact that this is an interface *)
               throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
            else
               match pop_n (length (C.descriptor_arg_types methdescrip)) op_stack with
               | Some (preargs, rt_addr (Some addr)::op_stack) =>
                  let args := rt_addr (Some addr)::rev preargs in
                  match heap_lookup_class heap addr with
                  | inleft (exist cls_nm addr_is_cls_nm) =>
                     if A.is_assignable classes (C.ty_obj cls_nm) (C.ty_obj clsname) then
                       let evidence := object_class_implies_class_exists addr_is_cls_nm in
                       match VM.lookup_virtual_method classes cls_nm (methname, methdescrip) evidence with
                       | Some (pack2 c' m' _) =>
                          if C.method_abstract m' then
                             throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errAbstractMethod
                          else
                             let state' := mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit in
                             basic_invoke c' m' args state'
                       | None =>
                          throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errAbstractMethod
                       end
                     else
                       throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errIncompatibleClassChange
                  | _ => wrong
                  end
               | Some (_, rt_addr None::op_stack) =>
                  throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errNullPointer
               | _ => wrong
               end
         end
       end
     | _ => wrong
     end
  | _ => wrong
  end.


Definition exec_if : C.cmp -> Z -> state -> exec_result :=
  fun test offset state => match state with
  | mkState (mkFrame (rt_int z::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let test_succeeded :=
          match test with
          | C.cmp_eq => B.Int32.eq z B.Int32.zero
          | C.cmp_ne => B.Int32.neq z B.Int32.zero
          | C.cmp_lt => B.Int32.lt z B.Int32.zero
          | C.cmp_le => B.Int32.le z B.Int32.zero
          | C.cmp_gt => B.Int32.gt z B.Int32.zero
          | C.cmp_ge => B.Int32.ge z B.Int32.zero
          end in
     match (if test_succeeded then (C.pc_plus_offset pc offset) else (Some (S pc))) with
     | None => wrong
     | Some new_pc =>
        cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_if_icmp : C.cmp -> Z -> state -> exec_result :=
  fun test offset state => match state with
  | mkState (mkFrame (rt_int z2::rt_int z1::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let test_succeeded :=
          match test with
          | C.cmp_eq => B.Int32.eq z1 z2
          | C.cmp_ne => B.Int32.neq z1 z2
          | C.cmp_lt => B.Int32.lt z1 z2
          | C.cmp_le => B.Int32.le z1 z2
          | C.cmp_gt => B.Int32.gt z1 z2
          | C.cmp_ge => B.Int32.ge z1 z2
          end in
     match (if test_succeeded then (C.pc_plus_offset pc offset) else (Some (S pc))) with
     | None => wrong
     | Some new_pc =>
        cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_swap : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (v1::v2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match val_category v1, val_category v2 with
     | C.category1, C.category1 =>
        cont (mkState (mkFrame (v2::v1::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | _,_ =>
        wrong
     end
  | _ => wrong
  end.

Definition exec_iinc : nat -> B.Int32.t -> state -> exec_result :=
  fun n c state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match OptionExt.option_mult (nth_error lvars n) with
     | Some (rt_int z) =>
        match update_lvars n (rt_int (B.Int32.add z c)) lvars with
        | None => wrong
        | Some new_lvars =>
           cont (mkState (mkFrame op_stack new_lvars (S pc) code mth class::fs) classes heap statics res reslimit)
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_aconst_null : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     cont (mkState (mkFrame (rt_addr None::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
  | _ => wrong
  end.

Definition option_addr_eq_dec : forall (a b:option Heap.addr_t), {a=b}+{a<>b}.
decide equality.
generalize a a0. decide equality.
Defined.

Definition exec_if_acmp : C.acmp -> Z -> state -> exec_result :=
  fun test offset state => match state with
  | mkState (mkFrame (rt_addr a1::rt_addr a2::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let test_succeeded :=
          match test with
          | C.acmp_eq => if option_addr_eq_dec a1 a2 then true else false
          | C.acmp_ne => if option_addr_eq_dec a1 a2 then false else true
          end in
     match (if test_succeeded then (C.pc_plus_offset pc offset) else (Some (S pc))) with
     | None => wrong
     | Some new_pc =>
        cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
     end
  | _ => wrong
  end.

Definition exec_if_nonnull : Z -> state -> exec_result :=
  fun offset state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match a with
     | None =>
        cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | Some _ =>
        match C.pc_plus_offset pc offset with
        | None => wrong
        | Some new_pc =>
           cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
        end
     end
  | _ => wrong
  end.

Definition exec_if_null : Z -> state -> exec_result :=
  fun offset state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match a with
     | Some _ =>
        cont (mkState (mkFrame op_stack lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | None =>
        match C.pc_plus_offset pc offset with
        | None => wrong
        | Some new_pc =>
           cont (mkState (mkFrame op_stack lvars new_pc code mth class::fs) classes heap statics res reslimit)
        end
     end
  | _ => wrong
  end.

Definition exec_ldc : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_int i) =>
        cont (mkState (mkFrame (rt_int i::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
     | _ => undefined (* FIXME: do floats and strings *)
     end
  | _ => wrong
  end.

Definition exec_ldc2 : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | _ => undefined (* FIXME: do longs and doubles *)
     end
  | _ => wrong
  end.

Definition exec_instanceof : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_classref cls_nm) =>
        match R.resolve_class (C.class_name class) cls_nm classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ T H =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           match a with
           | None => (* It was a null pointer *)
              cont (mkState (mkFrame (rt_int B.Int32.zero::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
           | Some a =>
              match heap_lookup_class heap a with
              | inleft (exist obj_cls_nm _) =>
                 if A.is_assignable classes (C.ty_obj obj_cls_nm) (C.ty_obj cls_nm) then
                    cont (mkState (mkFrame (rt_int B.Int32.one::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                 else
                    cont (mkState (mkFrame (rt_int B.Int32.zero::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
              | inright _ => wrong
              end
           end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_checkcast : B.ConstantPoolRef.t -> state -> exec_result :=
  fun idx state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     match C.ConstantPool.lookup (C.class_constantpool class) idx with
     | Some (C.cpe_classref cls_nm) =>
        match R.resolve_class (C.class_name class) cls_nm classes preclasses with
        | CP.load_err classes preserved _ e =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) e
        | CP.load_ok classes preserved _ T H =>
           let heap := preserve_cert_heap heap preserved in
           let statics := preserve_cert_fieldstore_over_classes statics preserved in
           match a with
           | None => (* null pointer *)
              cont (mkState (mkFrame (rt_addr None::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
           | Some a =>
              match heap_lookup_class heap a with
              | inleft (exist obj_cls_nm _) =>
                 if A.is_assignable classes (C.ty_obj obj_cls_nm) (C.ty_obj cls_nm) then
                    cont (mkState (mkFrame (rt_addr (Some a)::op_stack) lvars (S pc) code mth class::fs) classes heap statics res reslimit)
                 else
                    throw_builtin_exception (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) CP.errClassCast
              | inright _ => wrong
              end
           end
        end
     | _ => wrong
     end
  | _ => wrong
  end.

Definition exec_athrow : state -> exec_result :=
  fun state => match state with
  | mkState (mkFrame (rt_addr a::op_stack) lvars pc code mth class::fs) classes heap statics res reslimit =>
     let state := (mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit) in
     match a with
     | None =>
        throw_builtin_exception state CP.errNullPointer
     | Some r =>
        match heap_lookup_class heap r with
        | inleft (exist cls_nm _) =>
           if A.is_assignable classes (C.ty_obj cls_nm) (C.ty_obj B.java_lang_Throwable) then
              throw_exception state r
           else
              wrong
        | inright _ => wrong
        end
     end
  | _ => wrong
  end.

Definition exec : state -> exec_result := 
  fun state => match state with
  | mkState (mkFrame op_stack lvars pc code mth class::fs) classes heap statics res reslimit =>
     match nth_error (C.code_code code) pc with
     | None => wrong
     | Some op =>
  match op with
  (* Constants *)
  | C.op_iconst i         => exec_iconst i
  | C.op_ldc idx          => exec_ldc idx
  | C.op_ldc2 idx         => exec_ldc2 idx

  (* Arithmetic *)
  | C.op_iinc n c         => exec_iinc n c
  | C.op_iarithb op       => exec_iarithb op
  | C.op_iarithu op       => exec_iarithu op

  (* Local variables *)
  | C.op_load ty n        => exec_load n
  | C.op_store ty n       => exec_store n

  (* Stack operations *)
  | C.op_dup              => exec_dup
  | C.op_dup_x1           => exec_dup_x1
  | C.op_dup_x2           => exec_dup_x2
  | C.op_dup2             => exec_dup2
  | C.op_dup2_x1          => exec_dup2_x1
  | C.op_dup2_x2          => exec_dup2_x2
  | C.op_nop              => exec_nop
  | C.op_pop              => exec_pop
  | C.op_pop2             => exec_pop2
  | C.op_swap             => exec_swap

  (* OO *)
  | C.op_aconst_null      => exec_aconst_null
  | C.op_invokestatic idx => exec_invokestatic idx
  | C.op_putstatic idx    => exec_putstatic idx
  | C.op_getstatic idx    => exec_getstatic idx
  | C.op_putfield idx     => exec_putfield idx
  | C.op_getfield idx     => exec_getfield idx
  | C.op_new idx          => exec_new idx
  | C.op_invokeinterface idx => exec_invokeinterface idx
  | C.op_invokespecial idx=> exec_invokespecial idx
  | C.op_invokevirtual idx=> exec_invokevirtual idx
  | C.op_instanceof idx   => exec_instanceof idx
  | C.op_checkcast idx    => exec_checkcast idx

  (* Flow control *)
  | C.op_if test offset   => exec_if test offset
  | C.op_if_acmp test offset => exec_if_acmp test offset
  | C.op_if_icmp test offset => exec_if_icmp test offset
  | C.op_ifnonnull offset => exec_if_nonnull offset
  | C.op_ifnull offset    => exec_if_null offset
  | C.op_valreturn ty     => exec_valreturn
  | C.op_return           => exec_return
  | C.op_goto offset      => exec_goto offset
  | C.op_athrow           => exec_athrow

  | _ => fun s => undefined
  end state
  end
  | _ => wrong
  end.

Definition init : B.Classname.t -> B.Methodname.t -> C.descriptor -> list rt_val -> state -> exec_result :=
  fun clsname methname methdescrip args state => match state with
  | mkState nil classes heap statics res reslimit =>
     basic_invokestatic clsname clsname methname methdescrip args state
  | _ => wrong
  end.

End WithPreclasses.

End Execution.







