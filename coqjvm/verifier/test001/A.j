.class public super A

.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method A <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class A

.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"
.proof "java.lang.NullPointerException * !A" "A * (java.lang.NullPointerException * java.lang.NullPointerException -o (java.lang.NullPointerException * !A) & java.lang.NullPointerException)" "let np*ba be x in let !a be ba in a * (np * (@np2:java.lang.NullPointerException . np2 * !a) &np) end end"
.proof "java.lang.NullPointerException * !A" "java.lang.NullPointerException * !A" "x"
.proof "java.lang.NullPointerException * A * A" "A * java.lang.NullPointerException" "let npa2*a be x in let np * a2 be npa2 in a * np end end"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"
  .code
    .max_stack 1
    .locals 1

    aload 0
    invokespecial java/lang/Object <init> ()V
    return
  .end code
.end method

.method public test ()V
  .requires "java.lang.NullPointerException * A * A"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"

  .code
    .max_stack 2
    .locals 1
    
    new A
    dup
    invokespecial A <init> ()V
    pop
    return
  .end code
.end method

.method public loop (I)V
  .requires "java.lang.NullPointerException * !A"
  .ensures "TT"
  .exsures "TT"

  .code
    .max_stack 2
    .locals 1

   loop:
    iload 0
    ifeq exit
    new A
    invokespecial A <init> ()V
    iload 0
    iconst 1
    isub
    istore 0
    goto loop
   exit:
    return

    .proof_annotation loop "java.lang.NullPointerException * !A"
  .end code
.end method
