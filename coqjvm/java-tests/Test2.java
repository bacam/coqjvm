public class Test2 {
    int i;

    public int fof () {
	return i;
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
}
