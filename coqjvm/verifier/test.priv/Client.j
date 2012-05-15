.bytecode 50.0
.class public super Client
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method Integer <init> (I)V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method Client <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method Trusted <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_method Trusted nextPlease ()I "NoMore*java.lang.NullPointerException" "NoMore*java.lang.NullPointerException*Integer" "TT"
.linkinfo instantiable_class Client
.linkinfo instantiable_class Trusted
.linkinfo instantiable_class Integer

.proof "java.lang.NullPointerException" "java.lang.NullPointerException" "x"
.proof "NoMore * !java.lang.NullPointerException * java.lang.AbstractMethodError" "NoMore * java.lang.NullPointerException * ((NoMore * java.lang.NullPointerException * Integer) -o (Integer * (java.lang.NullPointerException * (java.lang.NullPointerException -o (NoMore * !java.lang.NullPointerException * java.lang.AbstractMethodError) & !java.lang.NullPointerException) & java.lang.NullPointerException * !java.lang.NullPointerException)) & !java.lang.NullPointerException) & (java.lang.NullPointerException * !java.lang.NullPointerException & java.lang.AbstractMethodError * !java.lang.NullPointerException)" "let nmbnp*am be x in let nm*bnp be nmbnp in let !np be bnp in nm * np * ((@nmnpi:NoMore * java.lang.NullPointerException * Integer . let nmnp*i be nmnpi in let nm2*np2 be nmnp in i * (np2 * ((@np3:java.lang.NullPointerException . nm2*!np*am) &!np) & np * !np) end end) & !np) & (np*!np&am*!np) end end end"
.proof "Trusted * NoMore * !java.lang.NullPointerException * java.lang.AbstractMethodError" "Trusted * (java.lang.NullPointerException * java.lang.NullPointerException -o (NoMore * !java.lang.NullPointerException * java.lang.AbstractMethodError) & java.lang.NullPointerException)" "let tnmbnp*am be x in let tnm*bnp be tnmbnp in let !np be bnp in let t*nm be tnm in t * (np * (@np2:java.lang.NullPointerException . nm*!np*am) & np) end end end end"

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

.method public static test (I)I
  .requires "Trusted*NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError"
  .ensures  "!java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 3
    .locals 3

    .catch NoMore from label1 to label0 using label0
   label2:
    new Trusted
    dup
    invokespecial Trusted <init> ()V
    astore 1
   label1:
    aload 1
    invokevirtual Trusted nextPlease ()I
    istore 2
   label3:
    new Integer
    dup
    iload 2
    invokespecial Integer <init> (I)V
    pop
   label4:
    goto label1
   label6:
   label0:
    astore 2
   label5:
    iconst 0
    return

  .proof_annotation label1 "NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError"
  .end code
.end method
