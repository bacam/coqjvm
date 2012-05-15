public class Methods {
    int v;

    public Methods (int i) {
	 v = i * 2;
    }

    public int f () {
	 return v;
    }

    public static int test (int i) {
	Methods m = new Methods (i);
	return m.f ();
    }
}
