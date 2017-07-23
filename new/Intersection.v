Require Import BaseLang.
Require Import List.
Require Import Fin.
Require Import DFA.
Require Import Definitions.
Require Import Chomsky.
Require Import Coq.Arith.Le. 


Inductive chomsky_rule: Type :=
  |   nonterm_rule : var -> var -> var -> chomsky_rule 
  |   terminal_rule : var -> ter -> chomsky_rule
  |   err.


Definition convert_unit_rule (v0 : var) (s : symbol) : chomsky_rule :=
   match s with
   |  Ts t => terminal_rule v0 t
   |  Vs v => err
   end.

Definition convert_double_rule (v0 : var) (s1 : symbol) (s2 : symbol) : chomsky_rule :=
   match s1, s2 with
   |  Ts t1, Ts t2 => err
   |  Ts t1, Vs v2 => err
   |  Vs v1, Ts t2 => err
   |  Vs v1, Vs v2 => nonterm_rule v0 v1 v2
   end.

Definition convert_rule_to_chomsky (r : rule) : chomsky_rule :=
  match r with
    (R v p) => match p with
               |  [] => err
               |  a :: [] => convert_unit_rule v a
               |  a :: b :: [] => convert_double_rule v a b
               |  a :: b :: c :: r => err
               end
  end.


Lemma l_eq_2: forall n, S (S (S (n))) <= 2 -> False.
Proof.
  intros.
  assert (0 = (S n)).
  apply le_n_0_eq.
  apply le_S_n.
  apply le_S_n.
  exact H.
  discriminate.
Qed.

Lemma no_err : forall (r : rule) (g : grammar) (is_ch: chomsky g) (is_in : In r g),
    ((convert_rule_to_chomsky r) <> err).
Proof.
  intros.
  destruct is_ch as [is_e is_ch].
  destruct is_ch as [is_un is_ch].
  destruct is_ch as [is_b is_u]. 
  destruct r.
  destruct p.
  pose ( H1 := is_e v [] is_in).
  assert False.
  apply H1.
  auto.
  contradiction.
  destruct p.
  simpl.
  destruct s.
  simpl.
  intro.
  congruence.
  assert False.
  apply (is_u v) .
  exists v0.
  apply is_in.
  contradiction.
  destruct p.
  destruct s.
  assert ([Ts t; s0] = [Ts t]).
  apply (is_un v [Ts t; s0]).
  apply is_in.
  auto.
  congruence.
  destruct s0.
  assert ([Vs v0; Ts t] = [Ts t]).
  apply (is_un v).
  apply is_in.
  auto.
  congruence.
  simpl.
  intro.
  congruence.
  assert ((|s :: s0 :: s1 :: p|) <= 2).
  apply (is_b v).
  exact is_in.
  simpl in H.
  assert False.
  apply l_eq_2 with (n := (| p |)).
  exact H.
  contradiction.
Qed.

Definition triple_to_var (n : nat) (from : t n) (v : var) (to : t n)  : var :=
  match v with
    V val => V (val * n * n + (proj1_sig (to_nat from)) * n + (proj1_sig (to_nat to)))
  end.

Fixpoint values_list (n : nat) : list (t n) :=
  match  n with
  | O => nil
  | S n' => F1 :: (map FS (values_list n'))
  end.    

Definition convert_terminal_2 (n : nat) (d : s_dfa n)
           (v : var) (te : ter) (from : t n) : rule :=
  R (triple_to_var from v (s_next d from te)) [Ts te].

Definition convert_terminal (n : nat) (d : s_dfa n)
           (v : var) (t : ter) : list rule :=
    map (convert_terminal_2 d v t) (values_list n).

Definition convert_nonterminal_2 (n : nat) (d : s_dfa n)
           (v : var) (v1 v2 : var) (s1 s2 s3: t n): rule :=
  R (triple_to_var s1 v s3) [Vs (triple_to_var s1 v1 s2); Vs (triple_to_var s2 v2 s3)].
  
Definition convert_nonterminal (n : nat) (d : s_dfa n)
           (v : var) (v1 v2 : var) : list rule :=
  flat_map (fun s1 =>
         flat_map (fun s2 =>
                map (fun s3 =>
                       convert_nonterminal_2 d v v1 v2 s1 s2 s3
                    ) (values_list n)
             ) (values_list n)
      ) (values_list n).


Definition convert_rule (n : nat) (d : s_dfa n)
           (r : rule) (g : grammar) (is_ch: chomsky g) (is_in : In r g) : list rule :=
  match (convert_rule_to_chomsky r) with
  |   nonterm_rule v v1 v2 => nil
  |   terminal_rule v t => convert_terminal d v t
  |   err => nil
  end.

Fixpoint in_flat_map (A B: Set)
         (sub_list : list A)
         (l : list A)   
         (f : forall (v : A), (In v l) -> list B) :
         (forall v : A, In v sub_list -> In v l) -> list B :=
  match sub_list with
  | [] => fun _ => []
  | h :: t  => fun is_in =>
               (f h (is_in h (in_eq h t))) ++ (in_flat_map f (fun v (i : In v t) => (is_in v (in_cons h v t i))))
  end.

Definition convert_grammar (n : nat) (d : s_dfa n)
            (g : grammar) (is_ch: chomsky g): grammar :=
  in_flat_map (fun r (is_in : In r g) => convert_rule d is_ch is_in)
              (fun v => id).

Definition g_language (G : grammar) (A : var) (u : phrase) (is_t : terminal u) : Prop :=
  der G A u.

Definition convert_start (n : nat) (d : s_dfa n) (v : var) : var :=
  triple_to_var (s_start d) v (s_final d).

Theorem main: forall n 
    (d : s_dfa n) (g : grammar) (is_ch: chomsky g) (v : var),
    ((s_dfa_language d) [/\] (g_language g v)) [==]
    (g_language (convert_grammar d is_ch) v).
Proof.
  intros. 
  apply mk_laguage_eq.
  apply main_forward.
  apply main_backward.
Qed.


