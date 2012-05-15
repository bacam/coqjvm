Ltac decide_equality_fixed :=
  first [ decide equality; decide_equality_fixed
        | match goal with |- {?x=?y}+{?x<>?y} => generalize x y; decide equality end; decide_equality_fixed
        | idtac ].
