.bytecode 50.0
.class public super Integer
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method Integer <init> (I)V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Integer
.linkinfo instance_field Integer i I

.field i I
.end field

.proof "java.lang.NullPointerException" "((TT)*(((TT)-o((java.lang.NullPointerException)&((java.lang.NullPointerException)*(TT))))&((TT)-o(TT))))&((java.lang.NullPointerException)*(TT))" "(tt*((@t:TT . (x&(x*tt)))&(@t2:TT . t2)))&(x*tt)"

.method public <init> (I)V
  .requires "java.lang.NullPointerException"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"
  .code
    .max_stack 1
    .locals 1

   label0:
    aload 0
    invokespecial java/lang/Object <init> ()V
    aload 0
    iload 1
    putfield Integer i I
    return
  .end code
.end method
