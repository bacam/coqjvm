.bytecode 50.0
.source "C.java"
.class public super C
.super java/lang/Object
.implements I

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method C <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class C
.linkinfo instance_special_method E <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class E

.proof "java.lang.NullPointerException" "(TT*((TT-ojava.lang.NullPointerException)&(TT-oTT))) & (java.lang.NullPointerException*TT)" "(tt * ((@ y : TT . x) & (@ x : TT . x))) & (x * tt)"

.proof "TT" "TT" "tt"

.proof "java.lang.NullPointerException*E" "java.lang.NullPointerException& E*java.lang.NullPointerException" "let n*e be x in n&e*n end"
.proof "java.lang.NullPointerException*E" "java.lang.NullPointerException*E" "x"
.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"
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

.method public maythrow (Z)V
  .throws E
  .requires "java.lang.NullPointerException*E"
  .ensures "java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 3
    iload 1
    ifeq label2
   label1:
    .line 4
    new E
    dup
    invokespecial E <init> ()V
    athrow
   label2:
    .line 5
    return
  .end code
.end method
