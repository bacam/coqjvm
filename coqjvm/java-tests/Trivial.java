/* The method here is Object.<init>, needed for the constructor. */
@ConstantPoolAdditional
    (
     instance_special_methods = { @CPAE_method(key=1, pre="java.lang.NullPointerException", ensures="TT", ex_ensures="TT") }
     )
@ResProofTable
    ({
	"java.lang.NullPointerException (java.lang.NullPointerException*((TT -o TT)/\\(TT -o TT)))/\\(java.lang.NullPointerException*TT) (x* ((\\y:TT .y)/\\(\\y:TT .y))) /\\(x*tt)",
	"A*A A*A x"
	    })
public class Trivial {
    @ResMethodSpec(pre="java.lang.NullPointerException", ensures="TT", ex_ensures="TT")
    public Trivial() {}

    @ResMethodSpec(pre="A*A", ensures="A*A", ex_ensures="A*A")
    public void trivial() {}
}
