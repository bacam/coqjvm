.bytecode 50.0
.source "TestAnn.java"
.class public super TestAnn
.super java/lang/Object

.attribute "uk.ac.ed.inf.request.ConstantPoolAdditional" "java/lang/Object;ic;java/lang/Object <init> ()V;isTT TT TT;TestAnn var I;sf;TestAnn testvar1 ()I;smTT TT TT"

.attribute "uk.ac.ed.inf.request.ProofTable" "TT (TT/\\TT);(x/\\x);TT (TT /\\ TT)/\\TT;(x/\\x)/\\x;"

.field static var I
.end field

.method public <init> ()V
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 11
    aload 0
    invokespecial java/lang/Object <init> ()V
    return
  .end code
.end method

.method public static testvar1 ()I
  .code
    .max_stack 1
    .locals 0

   label0:
    .line 15
    getstatic TestAnn var I
    return
  .end code
.end method

.method public static testvar (I)I
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 19
    iload 0
    putstatic TestAnn var I
   label1:
    .line 20
    invokestatic TestAnn testvar1 ()I
    return
  .end code
.end method

.method public static foo (II)I
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 24
    iload 0
    iload 1
    invokestatic TestAnn bar (II)I
    return
  .end code
.end method

.method public static bar (II)I
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 28
    iload 0
    iload 1
    isub
    return
  .end code
.end method

.method public static baz ()I
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 33
    iconst 1
    istore 0
   label1:
    .line 34
    iload 0
    return
  .end code
.end method

.method public static foo2 (II)I
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 38
    iload 0
    iload 1
    isub
    return
  .end code
.end method

.method public static add (I)I
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 43
    iconst 0
    istore 1
   label1:
    .line 44
    iload 0
    ifeq label4
   label2:
    .line 45
    iload 1
    iconst 1
    iadd
    istore 1
   label3:
    .line 46
    iload 0
    iconst 1
    isub
    istore 0
    goto label1
   label4:
    .line 48
    iload 1
    return
    .attribute "uk.ac.ed.inf.request.Certificate" "label1;TT"
  .end code
.end method

.method public static factorial (I)I
  .code
    .max_stack 2
    .locals 2

   label0:
    .line 54
    iconst 1
    istore 1
   label1:
    .line 55
    iload 0
    ifeq label4
   label2:
    .line 56
    iload 1
    iload 0
    imul
    istore 1
   label3:
    .line 57
    iload 0
    iconst 1
    isub
    istore 0
    goto label1
   label4:
    .line 59
    iload 1
    return
    .attribute "uk.ac.ed.inf.request.Certificate" "label1;TT"
  .end code
  .attribute "uk.ac.ed.inf.request.Spec" "TT*TT TT/\\TT TT"
.end method

.method public static factorial2 (I)I
  .code
    .max_stack 3
    .locals 1

   label0:
    .line 63
    iload 0
    ifne label1
    iconst 1
    return
   label1:
    .line 64
    iload 0
    iload 0
    iconst 1
    isub
    invokestatic TestAnn factorial2 (I)I
    imul
    return
  .end code
.end method

.method public static mkObj ()I
  .code
    .max_stack 2
    .locals 0

   label0:
    .line 68
    new java/lang/Object
    dup
    invokespecial java/lang/Object <init> ()V
    pop
   label1:
    .line 69
    iconst 1
    return
  .end code
.end method

.method public static mkObj2 ()I
  .code
    .max_stack 2
    .locals 1

   label0:
    .line 73
    new java/lang/Object
    dup
    invokespecial java/lang/Object <init> ()V
    astore 0
   label1:
    .line 74
    iconst 1
    return
  .end code
.end method

.method public static test3 ()V
  .code
    .max_stack 1
    .locals 1

   label0:
    .line 78
    iconst 0
    istore 0
   label1:
    .line 80
    iinc 0 1
   label2:
    .line 81
    iload 0
    ifgt label1
   label3:
    .line 82
    return
  .end code
.end method
