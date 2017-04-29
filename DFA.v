Require Import List.

Require Import Fin.


Inductive ter : Type :=
| T : nat -> ter.

Definition word := list ter.

Definition language := word -> Prop.

(** The type of deterministic finite automata. ***)
Record dfa { n : nat }: Type := mkDfa {
  start: t n;
  final: list (t n);
  next: (t n) -> ter -> (t n);
}.

Fixpoint final_state {n : nat} (d : dfa) (s: t n) (w: word) : t n :=
   match w with
     | nil => s
     | h :: t => final_state d (next d s h) t
  end.

Definition accepts (n : nat) (d : dfa) (s: t n) (w: word) : Prop :=
  In (final_state d s w) (final d).


(** The type of deterministic finite automata. ***)
Record s_dfa { n : nat }: Type := s_mkDfa {
  s_start: t n;
  s_final: t n;
  s_next: (t n) -> ter -> (t n);
}.

Fixpoint s_final_state {n : nat} (d : s_dfa) (s: t n) (w: word) : t n :=
   match w with
     | nil => s
     | h :: t => s_final_state d (s_next d s h) t
  end.

Definition s_accepts {n : nat} (d : s_dfa (n:=n)) (s: t n) (w: word) : Prop :=
  (s_final_state d s w) = (s_final d).

Definition dfa_language {n : nat} (d : dfa (n:=n)) := (accepts n d (start d)).

Definition s_dfa_language {n : nat} (d : s_dfa (n:=n)) := (s_accepts d (s_start d)).

Definition create_s_dfa {n : nat} (d : dfa (n:=n)) (h : t n) := s_mkDfa n (start d) h (next d).

Fixpoint split_dfa_list {n : nat} (d : dfa) (f_list : list (t n))
   : list s_dfa :=
  match f_list with
     | nil => nil
     | h :: t =>  create_s_dfa d h :: split_dfa_list d t
  end.

Definition split_dfa {n : nat} (d: dfa (n:=n)) := split_dfa_list d (final d).

Definition language_union (l1 l2 : language) := fun w => (l1 w) \/ (l2 w).

Definition language_intersection (l1 l2 : language) := fun w => (l1 w) /\ (l2 w).

Definition language_eq (l1  l2 : language) := forall w : word, l1 w <-> l2 w.

Lemma mk_laguage_eq : forall (l1 l2 : language), (forall w : word, l1 w -> l2 w) -> (forall w : word, l2 w -> l1 w) -> language_eq l1 l2.
Proof.
  intros l1 l2 H1 H2.
  unfold language_eq.
  intro w.
  split.
  apply (H1 w).
  apply (H2 w).
Qed.


Theorem th1 : forall l1 l2 l3 : language, language_eq (language_intersection l1 (language_union l2 l3)) (language_union (language_intersection l1 l2) (language_intersection l1 l3)).
Proof.
  intros.
  apply mk_laguage_eq.
  intros w H.
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

  intros w H.
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
  auto.
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

  apply distr.
  unfold language_intersection in H.
  exact H.
Qed.

Theorem T0: forall (n:nat) (d: dfa (n:=n)) (st : t n) (e : t n) (w: word),
  (final_state d st w) =
  (s_final_state (create_s_dfa d e) st w).
Proof.
  intros n d st e w.
  revert st.
  destruct d.
  simpl.
  unfold create_s_dfa. simpl.
  induction w.
  simpl.
  reflexivity.
  simpl.
  intro st.
  apply IHw.
Qed.

Theorem T21: forall d : dfa, language_eq (dfa_language d) (language_list_union (map (s_dfa_language) (split_dfa d))).
Proof.
  intros.
  apply mk_laguage_eq.
  intros w H1.
  unfold dfa_language in H1.
  unfold accepts in H1.
  unfold split_dfa.