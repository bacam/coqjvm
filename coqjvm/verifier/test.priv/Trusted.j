.bytecode 50.0
.class public super Trusted
.super java/lang/Object

.field i I
.end field

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method NoMore <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method Trusted <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class NoMore
.linkinfo instantiable_class Trusted
.linkinfo instance_field Trusted i I

.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"
.proof "NoMore * java.lang.NullPointerException" "Integer -o (NoMore * java.lang.NullPointerException * Integer) & java.lang.NullPointerException & java.lang.NullPointerException & java.lang.NullPointerException & NoMore * java.lang.NullPointerException & java.lang.NullPointerException" "let nm*np be x in (@i:Integer . nm*np*i) & np & np & np & nm * np & np end"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"
  .code
    .max_stack 2
    .locals 1

   label0:
    aload 0
    invokespecial java/lang/Object <init> ()V
   label1:
    aload 0
    iconst 0
    putfield Trusted i I
    return
  .end code
.end method

.method public nextPlease ()I
  .requires "NoMore*java.lang.NullPointerException"
  .ensures  "NoMore*java.lang.NullPointerException*Integer"
  .exsures  "TT"
  .grants   "Integer"
  .throws NoMore
  .code
    .max_stack 3
    .locals 1

   label0:
    aload 0
    getfield Trusted i I
    iconst 10
    if_icmpne label2
   label1:
    new NoMore
    dup
    invokespecial NoMore <init> ()V
    athrow
   label2:
    aload 0
    dup
    getfield Trusted i I
    iconst 1
    iadd
    putfield Trusted i I
   label3:
    aload 0
    getfield Trusted i I
    return
  .end code
.end method
