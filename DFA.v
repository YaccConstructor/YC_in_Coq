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

Fixpoint final_state {n : nat} (next_d : (t n) -> ter -> (t n)) (s: t n) (w: word) : t n :=
   match w with
     | nil => s
     | h :: t => final_state next_d (next_d s h) t
  end.

Definition accepts (n : nat) (d : dfa) (s: t n) (w: word) : Prop :=
  In (final_state (next d) s w) (final d).


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

Definition create_s_dfa (n : nat) (st_d : t n) (next_d : (t n) -> ter -> (t n)) (h : t n) := s_mkDfa n st_d h next_d.

Fixpoint split_dfa_list {n : nat}  (st_d : t n) (next_d : (t n) -> ter -> (t n)) (f_list : list (t n))
   : list s_dfa :=
  match f_list with
     | nil => nil
     | h :: t =>  create_s_dfa n st_d next_d h :: split_dfa_list st_d next_d t
  end.

Definition split_dfa {n : nat} (d: dfa (n:=n)) := split_dfa_list (start d) (next d) (final d).

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


Theorem T0: forall (n:nat) (start0: t n) (final0 : list (t n)) (next0 : t n -> ter -> t n) (st : t n) (e : t n) (w: word),
  (final_state next0 st w) =
  (s_final_state (create_s_dfa n start0 next0 e) st w).
Proof.
  intros.
  revert st.
  simpl.
  unfold create_s_dfa.
  induction w.
  simpl.
  reflexivity.
  simpl.
  intro st.
  apply IHw.
Qed.


Theorem T21_1: forall (n : nat) (d : dfa (n:=n)) (w : word),
    dfa_language d w -> language_list_union (map s_dfa_language (split_dfa d)) w.
Proof.
  intros n d w.
  destruct d.
  set (d := {| start := start0; final := final0; next := next0 |}).
  intro H1.
  unfold split_dfa.
  simpl.
  unfold dfa_language in H1.
  simpl in H1.
  unfold accepts in H1.
  simpl in H1.
  induction final0.
  simpl in H1.
  elim H1.
  simpl in H1.
  destruct H1.
  simpl.
  left.
  unfold s_dfa_language.
  simpl.
  unfold s_accepts.
  simpl.
  rewrite <- T0.
  auto.
  auto.
  simpl.
  right.
  apply IHfinal0.
  auto.
Qed.


Theorem T21_2: forall (n : nat) (d : dfa (n:=n)) (w : word),
    language_list_union (map s_dfa_language (split_dfa d)) w -> dfa_language d w.
Proof.
  intros n d w.
  destruct d.
  set (d := {| start := start0; final := final0; next := next0 |}).
  unfold split_dfa.
  simpl.
  unfold dfa_language.
  simpl.
  unfold accepts.
  simpl.
  intro H1.
  induction final0.
  auto.
  simpl in H1.
  simpl.
  destruct H1.
  left.
  unfold s_dfa_language in H.
  simpl in H.
  unfold s_accepts in H.
  simpl in H.
  rewrite T0 with (start0:=start0) (e:=a).
  auto.
  auto.
  right.
  apply IHfinal0.
  auto.
Qed.


Theorem T21:  forall (n : nat) (d : dfa (n:=n)), language_eq (dfa_language d) (language_list_union (map (s_dfa_language) (split_dfa d))).
Proof.
  intros.
  apply mk_laguage_eq.
  apply T21_1.
  apply T21_2.
Qed.