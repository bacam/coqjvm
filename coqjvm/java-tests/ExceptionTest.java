public class ExceptionTest {
    public static int test (int i) {
	try {
	    if (i == 0)
		throw new Exception ();

	    return 0;
	} catch (Throwable e) {
	    return 1;
	}
    }

    public static int test2 () throws Exception {
	try {
	    test3 ();

	    return 0;
	} catch (NullPointerException e) {
	    return 1;
	}
    }

    public static int test3 () throws Exception {
	throw new Exception ();
    }

    public static int test4 (int i) throws Exception {
	try {
	    if (i == 0) {}
	    //	throw new Exception ();

	    return i;
	} catch (Exception e) {
	    i = 2;
	} finally {
	    i = 1;
	}

	return i;
    }

    public static int test5 () throws Exception {
	int i;
	try {
	    throw null; //new Exception ();
	} finally {
	    i = 1;
	}
    }
}
