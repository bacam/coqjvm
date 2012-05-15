.bytecode 50.0
.class public super NoMore
.super java/lang/Exception

.linkinfo instance_special_method java/lang/Exception <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method NoMore <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class NoMore

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
    invokespecial java/lang/Exception <init> ()V
    return
  .end code
.end method
