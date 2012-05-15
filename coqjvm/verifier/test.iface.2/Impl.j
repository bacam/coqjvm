.bytecode 50.0
.class public super Impl
.super java/lang/Object
.implements Iface

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_field Impl obj Ljava/lang/Object;
.linkinfo instantiable_class java/lang/Object
.linkinfo instance_special_method Impl <init> ()V "java.lang.Object * java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Impl

.proof "TT" "TT" "tt"
.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"
.proof "java.lang.Object * java.lang.NullPointerException" "java.lang.Object * java.lang.NullPointerException & java.lang.NullPointerException" "let o*np be x in o*np&np end"

.field private obj Ljava/lang/Object;
.end field

.method public <init> ()V
  .requires "java.lang.Object * java.lang.NullPointerException"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 3
    .locals 1

    aload 0
    invokespecial java/lang/Object <init> ()V
    aload 0
    new java/lang/Object
    dup
    invokespecial java/lang/Object <init> ()V
    putfield Impl obj Ljava/lang/Object;
    return
  .end code
.end method

.method public foo ()Ljava/lang/Object;
  .requires "java.lang.NullPointerException"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 1
    .locals 1

    aload 0
    getfield Impl obj Ljava/lang/Object;
    return
  .end code
.end method
