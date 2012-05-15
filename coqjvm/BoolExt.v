Lemma bool_dec : forall b, b = true \/ b = false.
intros. destruct b; [left|right];trivial.
Save.

Definition bool_informative : forall b, {b=true}+{b=false}.
destruct b; intuition.
Defined.
