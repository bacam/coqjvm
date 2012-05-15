.bytecode 50.0
.class public super Test
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method Test <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Test
.linkinfo instance_special_method Impl <init> ()V "java.lang.Object * java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Impl
.linkinfo interface_method Iface foo ()Ljava/lang/Object; "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"

.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"
.proof "Impl * java.lang.Object * java.lang.NullPointerException * (java.lang.AbstractMethodError & java.lang.IncompatibleClassChangeError)" "Impl * (java.lang.Object * java.lang.NullPointerException * java.lang.NullPointerException -o (java.lang.NullPointerException & (java.lang.NullPointerException & (java.lang.AbstractMethodError & java.lang.IncompatibleClassChangeError))) & java.lang.NullPointerException)" "let r1*ex be x in let r2*np be r1 in let i*o be r2 in i*(o*np*(@np:java.lang.NullPointerException . np & (np & ex)) & np) end end end"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 1
    .locals 1

    aload 0
    invokespecial java/lang/Object <init> ()V
    return
  .end code
.end method

.method public test ()Ljava/lang/Object;
  .requires "Impl * java.lang.Object * java.lang.NullPointerException * (java.lang.AbstractMethodError & java.lang.IncompatibleClassChangeError)"
  .ensures  "TT"
  .exsures  "TT"
  .code
    .max_stack 2
    .locals 2

    new Impl
    dup
    invokespecial Impl <init> ()V
    astore 1
    aload 1
    invokeinterface Iface foo ()Ljava/lang/Object;
    return
  .end code
.end method
