package io;

@ProofTable({"TT TT;x"})

class Descriptor {
    int d;
    @Spec("TT TT TT")
    Descriptor(int d1) {
        d = d1;
    }
}