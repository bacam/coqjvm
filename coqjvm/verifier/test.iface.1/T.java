/* Note: at the time of writing the class file resulting from this
         will confuse resverifier, because it loads all the class
         files in the directory, but doesn't understand constant pool
         classrefs of arrays. */

public class T {
    public static void main(String args[]) {
	C c = new C();
	I i = c;

	try {
	    i.maythrow(false);
	} catch (E e) {
	    System.out.println("caught unexpected E");
	}
	try {
	    i.maythrow(true);
	} catch (E e) {
	    System.out.println("caught expected E");
	}
    }
}