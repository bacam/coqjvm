public class Fields {
    int a;
    Fields f;

    public Fields (int i) {
	a = i * 2;
	f = this;
    }

    public static int foo (int i) {
	Fields f = new Fields (i);
	Fields f2 = new Fields (i-1);
	return f.a + f.f.a + f2.a;
    }
}
