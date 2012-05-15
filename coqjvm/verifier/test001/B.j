.class public super B

.super A

.linkinfo instance_special_method A <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instantiable_class A

.proof "java.lang.NullPointerException" "java.lang.NullPointerException & java.lang.NullPointerException" "x & x"

.proof "java.lang.NullPointerException * A" "A * java.lang.NullPointerException" "let e*a be x in a * e end"

.proof "java.lang.NullPointerException * A * A" "java.lang.NullPointerException * A" "let ea*a be x in ea end"
.proof "TT" "TT" "tt"
.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"

.method public <init> ()V
  .requires "java.lang.NullPointerException"
  .ensures "TT"
  .exsures "TT"
  .code
    .max_stack 1
    .locals 1
    
    aload 0
    invokespecial A <init> ()V
    return
  .end code
.end method

.method public test ()V
  .requires "java.lang.NullPointerException * A"
  .ensures "java.lang.NullPointerException"
  .exsures "TT"

  .code
    .max_stack 1
    .locals 1
    
    new A
    dup
    invokespecial A <init> ()V
    pop
    return
  .end code
.end method
