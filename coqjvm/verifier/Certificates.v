Require Import StoreIface.
Require Import OptionExt.
Require Import Store.
Require Import OrderedTypeEx.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Omega.

Module Type CERTIFICATE.

Parameter asn : Set.

Declare Module Cert : STORE with Definition key := nat with Definition Key.eq := @eq nat with Definition object := asn.

Parameter cert_incl : Cert.t -> Cert.t -> Prop.

Axiom cert_incl_refl : forall c, cert_incl c c.
Axiom cert_incl_trans : forall c1 c2 c3, cert_incl c1 c2 -> cert_incl c2 c3 -> cert_incl c1 c3.
Axiom cert_incl_update : forall c n a, Cert.lookup c n = None -> cert_incl c (Cert.update c n a).
Axiom cert_incl_lookup : forall c1 c2 n a, Cert.lookup c1 n = Some a -> cert_incl c1 c2 -> Cert.lookup c2 n = Some a.

Parameter clean_cert : Cert.t -> nat -> Cert.t.

Axiom clean_ok : forall cert limit n, n >= limit -> Cert.lookup (clean_cert cert limit) n = None.
Axiom clean_contra : forall c limit,
  (forall n, n >= limit -> Cert.lookup c n = None) ->
  (forall n x, Cert.lookup c n = Some x -> n < limit).

End CERTIFICATE.

Module Type FORMULA.
Parameter formula : Set.
End FORMULA.

Module MkILLCert (F : FORMULA)
               : CERTIFICATE with Definition asn := F.formula.

Definition asn := F.formula.

Module Assertion.
Definition t:= asn.
End Assertion.
Module Cert := Store.MkStore Nat_as_OT Assertion.

Definition cert_incl :=
   fun c1 c2 => forall n, option_incl (Cert.lookup c1 n) (Cert.lookup c2 n).

Lemma cert_incl_refl : forall c, cert_incl c c.
unfold cert_incl. intros. apply option_incl_refl.
Save.

Lemma cert_incl_trans : forall c1 c2 c3, cert_incl c1 c2 -> cert_incl c2 c3 -> cert_incl c1 c3.
unfold cert_incl. intros. eapply option_incl_trans; eauto.
Save.

Lemma cert_incl_update : forall c n a, Cert.lookup c n = None -> cert_incl c (Cert.update c n a).
unfold cert_incl. intros c n a loopup_None n0.
destruct (eq_nat_dec n n0) as [n_eq_n0 | n_neq_n0].
 subst. rewrite loopup_None. rewrite Cert.lookup_update. apply o_inc_2.
 rewrite Cert.indep_lookup; [|apply n_neq_n0]. apply option_incl_refl.
Save.

Lemma cert_incl_lookup : forall c1 c2 n a, Cert.lookup c1 n = Some a -> cert_incl c1 c2 -> Cert.lookup c2 n = Some a.
intros. unfold cert_incl in H0. 
set (H1:=H0 n). rewrite H in H1. inversion H1. trivial.
Save.

Definition clean_cert : Cert.t -> nat -> Cert.t :=
  fun cert limit =>
    Cert.remove_by (fun n => if le_lt_dec limit n then true else false) cert.

Lemma clean_ok : forall cert limit n, n >= limit -> Cert.lookup (clean_cert cert limit) n = None.
intros. unfold clean_cert. apply Cert.remove_by_lookup.
intros. unfold Nat_as_OT.eq in H0. rewrite H0. reflexivity.
destruct (le_lt_dec limit n) as [limit_le_n | n_lt_limit].
 reflexivity.
 elimtype False. omega.
Save.

Lemma clean_contra : forall c limit, (forall n, n >= limit -> Cert.lookup c n = None) ->
  (forall n x, Cert.lookup c n = Some x -> n < limit).
intros.
destruct (dec_lt n limit) as [n_lt_limit|not_n_lt_limit].
 assumption.
 assert (n >= limit). omega. rewrite (H n H1) in H0. discriminate.
Save.

End MkILLCert.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)
