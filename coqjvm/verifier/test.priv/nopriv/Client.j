.bytecode 50.0
.class public super Client
.super java/lang/Object

.linkinfo instance_special_method java/lang/Object <init> ()V "TT" "TT" "TT"
.linkinfo instance_special_method Integer <init> (I)V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method Client <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_special_method Trusted <init> ()V "java.lang.NullPointerException" "java.lang.NullPointerException" "TT"
.linkinfo instance_method Trusted nextPlease ()I "NoMore*java.lang.NullPointerException" "NoMore*java.lang.NullPointerException" "TT"
.linkinfo instantiable_class Client
.linkinfo instantiable_class Trusted
.linkinfo instantiable_class Integer

.proof "java.lang.NullPointerException" "(TT*((TT-ojava.lang.NullPointerException)&(TT-oTT))) & (java.lang.NullPointerException*TT)" "(tt * ((@ y : TT . x) & (@ x : TT . x))) & (x * tt)"

.proof "Trusted*!Integer*NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError" "Trusted*((java.lang.NullPointerException*((java.lang.NullPointerException -o((((!Integer)*NoMore)*!java.lang.NullPointerException)*java.lang.AbstractMethodError))&(TT -o TT)))&(java.lang.NullPointerException*TT))" "let r1 * ae be x in let r2 * bnl be r1 in let r3 * nm be r2 in let t * i be r3 in let !nl be bnl in t*((nl*((@nl2:java.lang.NullPointerException . (((i*nm)*!nl)*ae))&(@t:TT . t)))&(nl*tt)) end end end end end"

.proof "!Integer*NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError" "(((NoMore)*(java.lang.NullPointerException))*((((NoMore)*(java.lang.NullPointerException))-o((Integer)*(((java.lang.NullPointerException)*(((java.lang.NullPointerException)-o((((!(Integer))*(NoMore))*(!(java.lang.NullPointerException)))*(java.lang.AbstractMethodError)))&((TT)-o((!(java.lang.NullPointerException))&(TT)))))&((java.lang.NullPointerException)*((!(java.lang.NullPointerException))&(TT))))))&((TT)-o((!(java.lang.NullPointerException))&(TT)))))&(((java.lang.NullPointerException)*((!(java.lang.NullPointerException))&(TT)))&((java.lang.AbstractMethodError)*((!(java.lang.NullPointerException))&(TT))))" "let r1 * ae be x in let r2 * bnl be r1 in let bi * nm be r2 in let !i be bi in let !nl be bnl in ((nm*nl)*((@nmnl:(NoMore*java.lang.NullPointerException) . let nm2 * nl2 be nmnl in (i*((nl*((@nl3:java.lang.NullPointerException . (((!i*nm2)*!nl)*ae))&(@t:TT . (!nl&tt))))&(nl*(!nl&tt))))end)&(@t3:TT . (!nl&tt))))&((nl*(!nl&tt))&(ae*(!nl&tt))) end end end end end"


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
  .requires "Trusted*!Integer*NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError"
  .ensures  "!java.lang.NullPointerException"
  .exsures  "TT"
  .code
    .max_stack 3
    .locals 3

    .catch NoMore from label1 to label0 using label0
   label2:
    new Trusted
    dup
hacklabel:
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

  .proof_annotation hacklabel "!Integer*NoMore*!java.lang.NullPointerException*java.lang.AbstractMethodError"
  .end code
.end method
