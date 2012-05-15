Require Import OrderedType.
Require Import MLStrings.

Module Type INT32.

Parameter t : Set.
Parameter zero : t.
Parameter one : t.
Parameter minus_one : t.
Parameter neg : t -> t.
Parameter add : t -> t -> t.
Parameter sub : t -> t -> t.
Parameter mul : t -> t -> t.
Parameter div : t -> t -> t.
Parameter logor : t -> t -> t.
Parameter logand : t -> t -> t.
Parameter logxor : t -> t -> t.
Parameter rem : t -> t -> t.
Parameter eq : t -> t -> bool.
Parameter neq : t -> t -> bool.
Parameter lt : t -> t -> bool.
Parameter le : t -> t -> bool.
Parameter gt : t -> t -> bool.
Parameter ge : t -> t -> bool.

End INT32.

Module Type NAMETYPE.

Parameter t : Set.

Definition eq := (@eq t).
Parameter lt : t -> t -> Prop.

Definition eq_refl := @refl_equal t.
Definition eq_sym := @sym_eq t.
Definition eq_trans := @trans_eq t.

Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Axiom lt_not_eq : forall {x y : t}, lt x y -> ~ eq x y.

Parameter compare : forall x y : t, Compare lt eq x y.

Parameter eq_dec : forall (a b:t), {a=b}+{a<>b}.

Hint Immediate eq_sym.
Hint Unfold eq.
Hint Resolve eq_refl eq_trans @lt_not_eq lt_trans.

Axiom to_string : t -> MLString.

End NAMETYPE.

Module Type BASICS.

Declare Module Int32 : INT32.
Declare Module Classname : NAMETYPE.
Declare Module Methodname : NAMETYPE.
Declare Module Fieldname : NAMETYPE.
Declare Module ConstantPoolRef : NAMETYPE.

Parameter java_lang_Object : Classname.t.
Parameter java_lang_Throwable : Classname.t.
Parameter java_lang_Error : Classname.t.
Parameter java_lang_LinkageError : Classname.t.
Parameter java_lang_ClassCircularityError : Classname.t.
Parameter java_lang_ClassFormatError : Classname.t.
Parameter java_lang_IncompatibleClassChangeError : Classname.t.
Parameter java_lang_NoClassDefFoundError : Classname.t.
Parameter java_lang_AbstractMethodError : Classname.t.
Parameter java_lang_IllegalAccessError : Classname.t.
Parameter java_lang_InstantiationError : Classname.t.
Parameter java_lang_NoSuchFieldError : Classname.t.
Parameter java_lang_NoSuchMethodError : Classname.t.
Parameter java_lang_VerifyError : Classname.t.
Parameter java_lang_Exception : Classname.t.
Parameter java_lang_RuntimeException : Classname.t.
Parameter java_lang_NullPointerException : Classname.t.
Parameter java_lang_ClassCastException : Classname.t.
Parameter init : Methodname.t.

End BASICS.
