.bytecode 50.0
.interface public abstract Iface
.super java/lang/Object

.method public abstract foo ()Ljava/lang/Object;
  .requires "java.lang.NullPointerException"
  .ensures  "java.lang.NullPointerException"
  .exsures  "TT"
.end method
