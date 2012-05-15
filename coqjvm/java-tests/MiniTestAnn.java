@ProofTable("TT&((java.lang.NullPointerException)*(TT)) (TT)&((java.lang.NullPointerException)*(TT));x;TT TT&TT;x&x;TT TT;x")

class MiniTestAnn {
    int var;

    @Spec("TT&((java.lang.NullPointerException)*(TT)) TT TT") int testvar1 () {
	return var;
    }

    int testvar (int i) {
	var = i;
	return testvar1 ();
    }

    int foo (int i, int j) {
	return bar (i,j);
    }

    int bar (int i, int j) {
	return i - j;
	//return n;
    }

    int baz () {
	int n = 1;
	return n;
    }

    int foo2 (int i, int j) {
	return i - j;
    }

    int add (int i) {
	int j = 0;
	@Inv("TT") while (i != 0) {
	    j = j + 1;
	    i = i - 1;
	}
	return j;
    }

    static int factorial (int i) {
	int ret = 1;
	@Inv("TT") while (i != 0) {
	    ret = ret * i;
	    i = i - 1;
	}
	return ret;
    }

    int factorial2 (int i) {
	if (i == 0) return 1;
	else return i * factorial2 (i-1);
    }
}
