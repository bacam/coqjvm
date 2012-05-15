; This is a test file for the assembler

.class public super test

.bytecode 50.0
.source "Test.java"
.super java/lang/Object
;.implements foo/bar/maz
;.implements fuggle/buggle/boggle/baggle

.attribute "fuggle" "boggle"

.annotation visible Lmy/madeup/annotation;
  .element foo .byte 12
  .element bar .annotation Lsome/other/annot;
    .element default .int 12
  .end annotation
  .element baz .array
    .int 34
    .int 56
    .annotation I
      .element default .int 78
    .end annotation
  .end array
.end annotation

.field static public var I
  .constantvalue 12

  .attribute "myfakeattribute" "here it is"
.end field

.field protected var2 Lmy/fictitious/class;
  .annotation visible Lmy/fake/annotation;
    .element default .int 12
  .end annotation
.end field

.method abstract foo ()V
  .synthetic
  .throws an/exception/class
  .deprecated
  .attribute "foo" "bar"
.end method

.method public static main ([Ljava/lang/String;)V
  .code
    .locals 1
    .max_stack 1
    
    .line 56
    iconst 0
    return
  .end code
.end method

.method public static test3 ()V
  .code
    .max_stack 1
    .locals 1

   label0:
    iconst 0
    istore 0
   label1:
    iinc 0 1
   label2:
    iload 0
    ifgt label1
   label3:
    return
  .end code
.end method

.method public static factorial (I)I
  .code
    .max_stack 2
    .locals 2

   label0:
    iconst 1
    istore 1
   label1:
    iload 0
    ifeq label4
   label2:
    iload 1
    iload 0
    imul
    istore 1
   label3:
    iload 0
    iconst 1
    isub
    istore 0
    goto label1
   label5:
   label4:
    iload 1
    return
  .end code
.end method

.method public static mkObj ()I
  .code
    .max_stack 2
    .locals 0

   label0:
    new java/lang/Object
    dup
    invokespecial java/lang/Object <init> ()V
    pop
   label1:
    iconst 1
    return
  .end code
.end method
