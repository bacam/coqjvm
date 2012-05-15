.bytecode 50.0
.class public super Static
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method Static <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Static

.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"

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

.method public static foo (II)I
  .requires "TT"
  .ensures "TT"
  .exsures "TT"
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 3
    iload 0
    iload 1
    iadd
    return
  .end code
.end method
