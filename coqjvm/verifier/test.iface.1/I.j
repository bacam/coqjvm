.bytecode 50.0
.source "I.java"
.interface public abstract I
.super java/lang/Object

.method public abstract maythrow (Z)V
  .throws E
  .requires "java.lang.NullPointerException*E"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
.end method
