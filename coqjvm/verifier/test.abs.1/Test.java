public class Test {
    public static void main(String args[]) {
	A a = new B();
	if (a.foo() == 2 && a.bar() == 1)
	    System.out.println("OK");
	else
	    System.out.println("Not OK");
    }
}
	