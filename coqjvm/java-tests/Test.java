public class Test {
    static int var;

    public static int testvar1 () {
	return var;
    }

    public static int testvar (int i) {
	var = i;
	return testvar1 ();
    }

    public static int foo (int i, int j) {
	return bar (i,j);
    }

    public static int bar (int i, int j) {
	return i - j;
	//return n;
    }

    public static int baz () {
	int n = 1;
	return n;
    }

    public static int foo2 (int i, int j) {
	return i - j;
    }

    public static int add (int i) {
	int j = 0;
	while (i != 0) {
	    j = j + 1;
	    i = i - 1;
	}
	return j;
    }

    public static int factorial (int i) {
	int ret = 1;
	while (i != 0) {
	    ret = ret * i;
	    i = i - 1;
	}
	return ret;
    }

    public static int factorial2 (int i) {
	if (i == 0) return 1;
	else return i * factorial2 (i-1);
    }

    public static int mkObj () {
	new Object ();
	return 1;
    }

    public static int mkObj2 () {
	Object o = new Object ();
	return 1;
    }

    public static void test3 () {
	int i= 0;
	do {
	    i++;
	} while (i > 0);
    }
}
