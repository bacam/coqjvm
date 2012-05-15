.bytecode 50.0
.class public super IDiv
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method IDiv <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class IDiv

.proof "java.lang.NullPointerException" "(TT*((TT-ojava.lang.NullPointerException)&(TT-oTT))) & (java.lang.NullPointerException*TT)" "(tt * ((@ y : TT . x) & (@ x : TT . x))) & (x * tt)"

.proof "TT" "TT" "tt"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 1
    aload 0
    invokespecial java/lang/Object <init> ()V
    return
  .end code
.end method

.method public static test (I)I
  .requires "TT"
  .ensures  "TT"
  .exsures  "TT"
  .code
    .max_stack 2
    .locals 1

   label0:
    .line 3
    iload 0
    iconst 0
    idiv
    return
  .end code
.end method
