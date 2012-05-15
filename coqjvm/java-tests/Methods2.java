public class Methods2 extends Methods {
    public Methods2(int i) {
	super (i);
    }

    public int f () {
	return super.f() * 2;
    }

    public static int test (int i) {
	Methods m = new Methods2 (i);
	if (m instanceof Methods2) {
	    return m.f();
	} else {
	    return 0;
	}
    }

    public static int test2 () {
	Methods m = new Methods (10);
	if (m instanceof Methods2) {
	    return 1;
	} else {
	    return 0;
	}
    }

    public static int test3 () {
	Methods m = null;
	try {
	    m.f ();
	    return 0;
	} catch (NullPointerException e) {
	    return 1;
	}
    }

    public static int test4 () {
	Methods m = new Methods (10);
	return ((Methods2)m).f ();
    }

    public static int test5 () {
	Methods m = new Methods2 (10);
	return ((Methods2)m).f ();
    }

    public static int test6 () {
	Methods m = new Methods (10);
	return ((Methods)m).f ();
    }

    public static int test7 () {
	Methods2 m = new Methods2 (10);
	return ((Methods)m).f ();
    }
}
