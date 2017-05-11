Require Import List.
Require Import Coq.Arith.Le.
Require Import Coq.Logic.FinFun.

Require Import Fin.

Inductive ter : Type :=
| T : nat -> ter.

Definition word := list ter.

Definition language := word -> Prop.

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
Record s_dfa (n : nat): Type := s_mkDfa {
  s_start: t n;
  s_final: t n;
  s_next: (t n) -> ter -> (t n);
}.


Definition s_accepts {n : nat} (d : s_dfa n) (s: t n) (w: word) : Prop :=
  (final_state (s_next n d) s w) = (s_final n d).

Definition dfa_language {n : nat} (d : dfa (n:=n)) := (accepts n d (start d)).

Definition s_dfa_language {n : nat} (d : s_dfa n) := (s_accepts d (s_start n d)).

Definition create_s_dfa (n : nat) (st_d : t n) (next_d : (t n) -> ter -> (t n)) (h : t n) := s_mkDfa n st_d h next_d.

Fixpoint split_dfa_list {n : nat}  (st_d : t n) (next_d : (t n) -> ter -> (t n)) (f_list : list (t n))
   : list (s_dfa n) :=
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

(*
Theorem T0: forall (n:nat) (start0: t n) (final0 : list (t n)) (next0 : t n -> ter -> t n) (st : t n) (e : t n) (w: word),
  (final_state next0 st w) =
  (s_final_state next0 st w).
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
*)


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
  auto.
  auto.
Qed.


Theorem T21:  forall (n : nat) (d : dfa (n:=n)), language_eq (dfa_language d) (language_list_union (map (s_dfa_language) (split_dfa d))).
Proof.
  intros.
  apply mk_laguage_eq.
  apply T21_1.
  apply T21_2.
Qed.


Inductive chomsky_rule (U: Type): Type :=
  |   nonterm_rule : U -> U -> U -> chomsky_rule U
  |   terminal_rule : U -> ter -> chomsky_rule U.


Record chomsky_grammar (U: Type): Type :=
  make_chomsky_grammar {
      grammar_start : U;
      grammar_rules : list (chomsky_rule U)
    }.


Inductive grr (U: Type) (rules: list (chomsky_rule U)) (r: U): word -> Prop :=
  | nonterm_rule_app : forall
                     (r1 : U) (w1 : word)
                     (r2 : U) (w2 : word),
                     (grr U rules r1 w1) -> (grr U rules r2 w2) -> grr U rules r (w1 ++ w2)
  | terminal_rule_app : forall (t : ter), grr U rules r (t :: nil).

Definition chomsky_language (U: Type) (g: chomsky_grammar U) (w : word) : Prop :=
  grr U (grammar_rules U g) (grammar_start U g) w.


Inductive triple (U : Type) (n : nat) :=
    | make_triple : (t n) -> U -> (t n) -> triple U n.


Theorem lt_Sn_lt (m : nat) (n : nat) (prop : S m < n): m < n.
Proof.
  induction prop.
  auto.
  auto.
Qed.


Fixpoint values_list (n : nat) : list (t n) :=
  match  n with
  | O => nil
  | S n' => F1 :: (map FS (values_list n'))
  end.

Theorem map_f : forall (U : Type) (U2 : Type) (v : U) (l : list U) (f : U -> U2),
    In v l -> In (f v) (map f l).
Proof.
  intros.
  induction l.
  simpl in H.
  auto.
  simpl.
  simpl in H.
  destruct H.
  left.
  exact (f_equal f H).
  right.
  exact (IHl H).
Qed.


Theorem all_values_in_list : forall (n : nat) (f : t n), In f (values_list n).
Proof.
  intros n f.
  induction f.
  simpl.
  auto.
  simpl.
  right.
  apply map_f.
  exact IHf.
Qed.



Fixpoint convert_nonterm_rule
         (U : Type) (n : nat)
         (r: U) (r1: U) (r2: U) : list (chomsky_rule (triple U n)) :=
  flat_map
    (fun s1 =>
       flat_map
         (fun s2 =>
            map
              (fun s3 =>
                 nonterm_rule (triple U n)
                   (make_triple U n s1 r s3)
                   (make_triple U n s1 r1 s2)
                   (make_triple U n s2 r2 s3)

              ) (values_list n)
         ) (values_list n)
    ) (values_list n).


Fixpoint convert_terminal_rule
         (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
         (r: U) (t: ter): list (chomsky_rule (triple U n)) :=
 map (fun s1 =>
       terminal_rule (triple U n)
                     (make_triple U n s1 r (next s1 t))
                     t
     ) (values_list n).


Definition convert_rule (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
           (r : chomsky_rule U): list (chomsky_rule (triple U n)) :=
  match r with
  |   nonterm_rule _ r r1 r2 => convert_nonterm_rule U n r r1 r2
  |   terminal_rule _ r t => convert_terminal_rule U n next r t
  end.


Definition convert_rules
           (U : Type) (n : nat) (next : (t n) -> ter -> (t n))
           (g : list (chomsky_rule U)): list (chomsky_rule (triple U n)) :=
    (flat_map (convert_rule U n next) g).

Definition convert_grammar
           (U : Type) (n : nat) (d : s_dfa n)
           (g : chomsky_grammar U): (chomsky_grammar (triple U n)) :=
  make_chomsky_grammar (triple U n)
    (make_triple U n (s_start n d) (grammar_start U g) (s_final n d))
    (convert_rules U n (s_next n d) (grammar_rules U g)).

Theorem test0: forall (n : nat)
                      (w1 w2 : word)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n))
                      (H0 : final_state next from (w1 ++ w2) = to),
     final_state next (final_state next from w1) w2 = to.
Proof.
  intros n w1 w2 next.
  induction w1.
  simpl.
  auto.
  simpl.
  intros from to.
  apply IHw1.
Qed.


Theorem test1: forall (U : Type)
                      (n : nat)
                      (w : word)
                      (rules : list (chomsky_rule U))
                      (r : U)
                      (gr : grr U rules r w)
                      (next : (t n) -> ter -> (t n))
                      (from to: (t n))
                      (H0 : (final_state next from w = to)),
    grr (triple U n) (convert_rules U n next rules) (make_triple U n from r to) w.
Proof.
  intros U n w rules r gr next.
  set (new_rules := convert_rules U n next rules).
  induction gr.
  intros from0 to0 H0.
  set (m := final_state next from0 w1).
  assert (new_gr1 : grr (triple U n) new_rules (make_triple U n from0 r1 m) w1).
  apply IHgr1.
  auto.
  assert (new_gr2 : grr (triple U n) new_rules (make_triple U n m r2 to0) w2).
  apply IHgr2.
  auto.
  apply test0.
  exact H0.
  exact (nonterm_rule_app (triple U n) new_rules (make_triple U n from0 r to0)
                          (make_triple U n from0 r1 m) w1
                          (make_triple U n m r2 to0) w2
                          new_gr1 new_gr2).
  simpl.


Theorem main_forward: forall (U : Type) (n : nat)
                     (d : s_dfa n) (g : chomsky_grammar U) (w : word),
    (s_dfa_language d) w /\ (chomsky_language U g) w ->
                (chomsky_language (triple U n) (convert_grammar U n d g) w).
Proof.
  intros.
  destruct H as [H1 H2].
  unfold chomsky_language in H2.
  unfold s_dfa_language in H1.
  unfold s_accepts in H1.


(*
Theorem main: forall (U : Type) (n : nat)
                     (d : s_dfa n) (g : chomsky_grammar U),
    language_eq (language_intersection (s_dfa_language d) (chomsky_language U g))
                (chomsky_language (triple U n) (convert_grammar U n d g)).
Proof.
  intros.
  apply mk_laguage_eq.

*)