Require Import List.

Require Import Fin.


Inductive ter : Type :=
| T : nat -> ter.

Definition word := list ter.

Definition language := word -> Prop.

(** The type of deterministic finite automata. ***)
Record dfa : Type := mkDfa {
  states_n: nat;
  start: t states_n;
  final: list (t states_n);
  next: (t states_n) -> ter -> (t states_n);
}.

Fixpoint final_state (d : dfa) (s: t (states_n d)) (w: word) : t (states_n d) :=
   match w with
     | nil => s 
     | h :: t => final_state d (next d s h) t 
  end.

Definition accepts (d : dfa) (s: t (states_n d)) (w: word) : Prop :=
  In (final_state d s w) (final d). 
    

(** The type of deterministic finite automata. ***)
Record s_dfa: Type := s_mkDfa {
  s_states_n: nat;
  s_start: t s_states_n;
  s_final: t s_states_n;
  s_next: (t s_states_n) -> ter -> (t s_states_n);
}.

Fixpoint s_final_state (d : s_dfa) (s: t (s_states_n d)) (w: word) : t (s_states_n d) :=
   match w with
     | nil => s 
     | h :: t => s_final_state d (s_next d s h) t 
  end.

Definition s_accepts (d : s_dfa) (s: t (s_states_n d)) (w: word) : Prop :=
  (s_final_state d s w) = (s_final d).

Definition dfa_language (d : dfa) := (accepts d (start d)).

Definition s_dfa_language (d : s_dfa) := (s_accepts d (s_start d)).



Fixpoint split_dfa_list (d : dfa) (f_list : list (t (states_n d)))
   : list s_dfa :=
  match f_list with
     | nil => nil
     | h :: t => s_mkDfa (states_n d) (start d) h (next d) :: split_dfa_list d t
  end.

Definition split_dfa (d: dfa) := split_dfa_list d (final d).
  
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

Theorem T21: forall d : dfa, language_eq (dfa_language d) (language_list_union (map (s_dfa_language) (split_dfa d))).
Proof.
  intros.
  apply mk_laguage_eq.
  intros w H1.
  unfold dfa_language in H1.
  unfold accepts in H1.
  unfold split_dfa.