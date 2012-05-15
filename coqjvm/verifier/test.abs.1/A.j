.bytecode 50.0
.class public super abstract A
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method A <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo class A

.proof "java.lang.NullPointerException" "(TT*((TT-ojava.lang.NullPointerException)&(TT-oTT))) & (java.lang.NullPointerException*TT)" "(tt * ((@ y : TT . x) & (@ x : TT . x))) & (x * tt)"
.proof "TT" "TT" "tt"

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

.method public abstract foo ()I
  .requires "TT"
  .ensures  "TT"
  .exsures  "TT"
.end method

.method public bar ()I
  .requires "TT"
  .ensures  "TT"
  .exsures  "TT"
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 4
    iconst 1
    return
  .end code
.end method
