.bytecode 50.0
.class public super B
.super A

.linkinfo instance_special_method A <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method B <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class B

.proof "java.lang.NullPointerException" "(java.lang.NullPointerException*((java.lang.NullPointerException -o java.lang.NullPointerException)&(TT -o TT)))&(java.lang.NullPointerException * TT)" "(x*((@n:java.lang.NullPointerException . n)&(@t:TT . t)))&(x*tt)"
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
    invokespecial A <init> ()V
    return
  .end code
.end method

.method public foo ()I
  .requires "TT"
  .ensures  "TT"
  .exsures  "TT"
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 3
    iconst 2
    return
  .end code
.end method
