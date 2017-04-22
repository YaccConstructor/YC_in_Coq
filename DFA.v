Require Import List Ensembles.

Require Import Fin.


Inductive ter : Type :=
| T : nat -> ter.


(** The type of deterministic finite automata. ***)
Record dfa : Type := mkDfa {
  states_n: nat;
  start: t states_n;
  final: Ensemble (t states_n);
  next: (t states_n) -> ter -> (t states_n);
}.


Definition word := list ter.

Definition language := word -> Prop.


Fixpoint accepts (d : dfa) (s: t (states_n d)) (w: word) : Prop :=
  match w with
     | nil => In (t (states_n d)) (final d) s
     | h :: t => accepts d (next d s h) t 
  end.

Definition dfa_language (d : dfa) := (accepts d (start d)).

Definition language_union (l1 l2 : language) := fun w => (l1 w) \/ (l2 w).

Definition language_intersection (l1 l2 : language) := fun w => (l1 w) /\ (l2 w).

Definition language_eq (l1  l2 : language) := forall w : word, l1 w <-> l2 w. 


Theorem th1 : forall l1 l2 l3 : language, language_eq (language_intersection l1 (language_union l2 l3)) (language_union (language_intersection l1 l2) (language_intersection l1 l3)).
Proof.
  intros.
  unfold language_eq.    
  intros.
  split.
  intro.
  unfold language_intersection in H.
  destruct H.
  unfold language_union in H0.
  unfold language_union.
  destruct H0.
  left.
  unfold language_intersection.
  intuition.
  right.
  unfold language_intersection.
  intuition.

  intros.
  unfold language_union in H.
  destruct H.
  unfold language_intersection in H.
  destruct H.
  unfold language_intersection.
  split.
  exact H.
  unfold language_union.
  left.
  exact H0.
  unfold language_intersection in H.
  unfold language_intersection.
  destruct H.
  split.
  
  exact H.
  unfold language_union.
  right.
  exact H0.
Qed.


Fixpoint language_list_union (l : list language) := fun w =>
   match l with
     | nil => False
     | h :: t => (h w) \/ language_list_union t w
   end.


Lemma distr : forall (a b c : Prop), (a /\ c) -> a /\ (b \/ c).
Proof.
  intros.
  destruct H.
  split.
  exact H.
  right.
  exact H0.
Qed.
  
Theorem th2 : forall (l2 : language) (ls : list language),
    language_eq (language_intersection l2 (language_list_union ls))
                 (language_list_union (map (language_intersection l2) ls)).
Proof.
  intros l2 ls.
  unfold language_eq.
  intros w.
  split.
  elim ls.
  intros H0.
  unfold language_intersection in H0.
  destruct H0.
  simpl in H0.
  elim H0.
  intros a tail.
  intro HR.
  intro LI.
  
  simpl.

  unfold language_intersection in LI.
  simpl language_list_union in LI.

  destruct LI as [l2_w H1].

  elim H1.

  intro.

  left.

  unfold language_intersection.

  apply (conj l2_w H).

  intro.
  
  right.

  apply HR.

  unfold language_intersection.

  apply (conj l2_w H).

  elim ls.

  simpl.

  intros F; case F.

  clear ls.
  
  intros LA ls H0 LU.

  simpl language_list_union in LU.

  case LU.

  intro H1.

  unfold language_intersection.

  unfold language_intersection in H1.

  destruct H1.

  split.

  exact H.

  simpl language_list_union.

  left; exact H1.

  intro.

  apply H0 in H.

  unfold language_intersection.
  simpl language_list_union.

  apply distr.
  unfold language_intersection in H.
  exact H.
Qed.