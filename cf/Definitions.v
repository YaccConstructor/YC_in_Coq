Require Export Lists.

(** * Definitions of grammars *)

Ltac dupapply H1 lemma H2 := pose (H2:= H1) ; apply lemma in H2.

Inductive ter : Type :=
| T : nat -> ter.

Inductive var : Type :=
| V : nat -> var.

Inductive symbol : Type :=
| Ts : ter -> symbol
| Vs : var -> symbol.

Definition phrase := list symbol.

Inductive rule : Type :=
| R : var -> phrase -> rule.

Definition grammar := list rule.

(** * Decidability instances *)

Instance var_eq_dec : eq_dec var.
Proof. intros A B. unfold dec. repeat decide equality. Defined.

Instance rule_eq_dec : eq_dec rule.
Proof.  intros A B. unfold dec. repeat decide equality. Defined.

Instance symbol_eq_dec : eq_dec symbol.
Proof. intros A B. unfold dec. repeat decide equality. Defined.

Instance exists_rule_dec G p {D : forall A u, dec (p A u)} : dec (exists A u, R A u el G /\ p A u).
Proof.
  induction G as [| [A u] Gr IHGr].
  - right. intros [A [u [H0 H1]]]. destruct H0.
  - destruct IHGr as [IH | IH].
    + left. destruct IH as [A' [u' [H0 H1]]].
      exists A', u'. auto.
    + destruct (D A u) as [D' | D'].
      * left. exists A, u. auto.
      * right. intros [A' [u' [H0 H1]]].
        destruct H0 ; try now inv H.
        apply IH. exists A', u'. auto.
Defined.

Instance exists_phrase_dec G A p : (forall x, dec (p x)) -> dec (exists u , R A u el G /\ p u).
Proof with (intros H1 ; destruct H1 as [u [[H1 | H1] H2]] ; [inv H1 |] ; firstorder).
  intros H.
  induction G as [| [B v] Gr IHGr] ; try (now right ; intros [u [H0 H1]] ; destruct H0).
  destruct IHGr as [IHGr | IHGr] ; try now (left ; firstorder).
  decide (A = B) as [D | D] ; subst.
  - decide (p v) as [D0 | D0].
    + left. exists v. split ; auto.
    + right...
  - right...
Defined.

Instance symbol_ter_dec : forall s, dec (exists a, s = Ts a).
Proof.
  intros [s|s] ; [ left ; now exists s | right ; intros [a H] ; inv H].
Defined.

Instance phrase_var_dec u : dec (exists A, u = [Vs A]).
Proof with (try now (right ; intros [? H] ; inv H)).
  destruct u as [| [t | A] ur]...
  destruct ur as [| s ur]...
  left. now (exists A).
Defined.

Instance phrase_char_dec u : dec (exists a, u = [Ts a]).
Proof.
  destruct u as [| [a | A] [| s u]] ; try now (right ; intros [b H] ; inv H).
  left. exists a. auto.
Qed.

Instance filter_rule_dec (p : phrase -> Prop) {D : forall u, dec (p u)} : forall r, (dec ((fun r => match r with R A u => p u end) r)).
Proof.
  destruct r ; auto.
Defined.


