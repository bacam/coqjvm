Inductive twosig (A:Type) (B:Type) (P:A -> B -> Prop) : Type :=
| pack2 : forall (x:A) (y:B), P x y -> twosig A B P.

Arguments Scope twosig [type_scope type_scope type_scope].

Notation "{ x : A , y : B | P }" := (twosig A B (fun (x:A) (y:B)=> P)) (at level 0, x at level 99, y at level 99) : type_scope.

Implicit Arguments pack2 [A B].