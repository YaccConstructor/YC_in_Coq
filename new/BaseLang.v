Require Import Definitions.
Require Import Derivation.
Require Import List.

Definition base_language :=
  forall (v : phrase), terminal v -> Prop.

Definition language_union (l1 l2 : base_language) :=
  fun v (t : terminal v) => (l1 v t) \/ (l2 v t).

Definition language_intersection (l1 l2 : base_language) :=
  fun v (t : terminal v) => (l1 v t) /\ (l2 v t).

Definition language_eq (l1  l2 : base_language) :=
  forall v (t : terminal v), l1 v t <-> l2 v t. 

Notation "l1 [\/] l2" := (language_union l1 l2) (at level 85).
Notation "l1 [/\] l2" := (language_intersection l1 l2) (at level 80).
Notation "l1 [==] l2" := (language_eq l1 l2) (at level 90).

Lemma mk_laguage_eq :
  forall (l1 l2 : base_language),
    (forall v (t : terminal v), l1 v t -> l2 v t) ->
    (forall v (t : terminal v), l2 v t -> l1 v t) -> l1 [==] l2. 
Proof.
  intros l1 l2 H1 H2.
  unfold language_eq.
  intro w.
  split.
  apply (H1 w).
  apply (H2 w).
Qed.
 
Theorem lang_distr : forall l1 l2 l3 : base_language,
    l1 [/\] (l2 [\/] l3) [==] (l1 [/\] l2) [\/] (l1 [/\] l3).
Proof.
  intros.
  apply mk_laguage_eq.
  intros v t H.   
  unfold language_intersection in H.
  destruct H.
  unfold language_union in *.
  destruct H0.
  left.
  unfold language_intersection.
  intuition.
  right.
  unfold language_intersection.
  intuition.
  intros v t H.
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


Fixpoint language_list_union (l : list base_language) := fun v (t : terminal v) =>
   match l with
     | nil => False
     | head :: tail => (head v t) \/ language_list_union tail v t
   end.

Theorem lang_distr_2 : forall (l2 : base_language) (ls : list base_language),
    (l2 [/\] (language_list_union ls)) [==]
                 (language_list_union (map (fun l => l2 [/\] l) ls)).
Proof.
  intros l2 ls.
  unfold language_eq.
  intros v.
  split.
  elim ls.
  intros H0.
  unfold language_intersection in H0.
  destruct H0.
  auto.
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
  assert(distr : forall (a b c : Prop), (a /\ c) -> a /\ (b \/ c)).
  intros.
  destruct H1.
  auto.
  apply distr.
  unfold language_intersection in H.
  exact H.
Qed.