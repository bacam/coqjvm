@ProofTable({"TT TT;x",
             "io.Descriptor io.Descriptor;x",
             "io.Descriptor * io.Descriptor io.Descriptor * io.Descriptor;x",
             "io.Descriptor io.Descriptor -o (io.Descriptor * io.Descriptor) & io.Descriptor;(@y:io.Descriptor . (x*y))&x"})

public class ReadLots {
    @Spec("io.Descriptor io.Descriptor TT")
    public static int addfile(int fno) {
        io.File f = new io.File(fno);
        int i;
        int acc = 0;
        i = f.read();
        @Inv("TT")
        while (i != 0) {
            acc = acc + i;
            i = f.read();
        }
        f.close();
        return acc;
    }

    @Spec("io.Descriptor*io.Descriptor io.Descriptor*io.Descriptor TT")
    public static int addfiles(int fno) {
        io.File f = new io.File(fno);
        int acc = 0;
        int i = f.read();
        @Inv("io.Descriptor")
        while (i != 0) {
            acc = acc + addfile(i);
            i = f.read();
        }
        f.close();
        return acc;
    }
}
