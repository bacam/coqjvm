package io;

@ProofTable({"TT TT;x",
             "io.Descriptor io.Descriptor;x"})

public class File {
    Descriptor d;
    @Spec("io.Descriptor TT TT")
    public File(int fileno) throws java.lang.Exception {
        int d = nativeopen(fileno);
        if (d == 0) throw new java.lang.Exception();
        this.d = new Descriptor(d);
    }

    public int read() { return nativeread(d.d); }

    @Spec("TT io.Descriptor TT")
    @Grants("io.Descriptor")
    public void close() {
	if (!nativeclose(d.d))
	    throw new java.lang.Exception();
    }

    @Spec("TT TT TT")    
    private static native int nativeopen(int fileno);
    @Spec("TT TT TT")    
    private static native int nativeread(int descriptor);
    @Spec("TT TT TT")    
    private static native boolean nativeclose(int descriptor);
}
