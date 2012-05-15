public class C2 extends C1 {
    public static int foo (int i) {
	return i+1;
    }

    public static int bar (int i) {
	return C2.foo (i) + C1.foo (i-1) + foo (i-2);
    }
}
