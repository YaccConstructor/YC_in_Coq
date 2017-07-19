Require Import List.
Require Import Fin.
Require Import BaseLang.
Require Import Definitions.
Require Import Derivation.


Record dfa (n : nat): Type := mkDfa {
  start: t n;
  final: list (t n);
  next: (t n) -> ter -> (t n);
}.

Definition word := list ter.


Lemma tail_term : forall (h : symbol) (t : phrase) (is_t : terminal (h :: t)), terminal t.
Proof.
  intros.
  unfold terminal.
  intros.
  auto.
Qed.

Lemma f_to_ter: False -> ter.
Proof.
  intro.
  contradiction.
Qed.

Lemma head_of_term : forall (h : var) (t : phrase) (is_t : terminal ((Vs h) :: t)), False.
Proof.
  unfold terminal.
  intros.
  assert (exists t : ter, Vs h = Ts t).
  apply is_t.
  auto.
  elim H.
  intros.
  discriminate.
Qed.

Fixpoint symbol_to_terminal (h : symbol) (t : phrase) : terminal (h :: t) -> ter :=
   match h with
   | Ts tr => fun _ => tr
   | Vs v => fun is_t => f_to_ter (head_of_term is_t)
   end.


Fixpoint phrase_to_word (v : phrase) : terminal v -> word :=
  match v return (terminal v -> word) with
  | nil => fun v => nil
  | v_head :: v_tail => fun is_t => (phrase_to_word (tail_term is_t))
  end.

Fixpoint final_state {n : nat} (next_d : (t n) -> ter -> (t n)) (s: t n) (w: word) : t n :=
  match w with
     | nil => s
     | h :: t => final_state next_d (next_d s h) t
  end.

Definition accepts (n : nat) (d : dfa n) (s: t n) (w: word) : Prop :=
  In (final_state (next d) s w) (final d).

Record s_dfa (n : nat): Type := s_mkDfa {
  s_start: t n;
  s_final: t n;
  s_next: (t n) -> ter -> (t n);
}.


Definition s_accepts {n : nat} (d : s_dfa n) (s: t n) (w: word) : Prop :=
  (final_state (s_next d) s w) = (s_final d).

(**

Definition dfa_language (n : nat) (d : dfa n) := (accepts d (start d)).

Definition s_dfa_language {n : nat} (d : s_dfa n) := (s_accepts d (s_start d)).

Fixpoint split_dfa_list {n : nat}  (st_d : t n) (next_d : (t n) -> ter -> (t n)) (f_list : list (t n))
   : list (s_dfa n) :=
  match f_list with
     | nil => nil
     | h :: t => (s_mkDfa st_d h next_d) :: split_dfa_list st_d next_d t
  end.

Definition split_dfa {n : nat} (d: dfa n) := split_dfa_list (start d) (next d) (final d).

Theorem lemma2_3_1: forall (n : nat) (d : dfa n) (w : word),
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
  auto.
  auto.
  simpl.
  right.
  apply IHfinal0.
  auto.
Qed.




Theorem lemma2_3_2: forall (n : nat) (d : dfa n) (w : word),
    language_list_union (map s_dfa_language (split_dfa d)) w -> dfa_language n d w.
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
  auto.
  auto.
Qed.


Theorem lemma2_3:  forall (n : nat) (d : dfa n), (dfa_language n d) [==] (language_list_union (map (s_dfa_language) (split_dfa d))).
Proof.
  intros.
  apply mk_laguage_eq.
  apply lemma2_3_1.
  apply lemma2_3_2.
Qed. **)

