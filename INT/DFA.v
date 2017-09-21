Require Import List.
Require Import Fin.


Add LoadPath "../". 

Require Import CFG.Definitions.
Require Import INT.Base.

Module DFA.

  Import Base Definitions.
  
  Section Definitions. 

    Context {State T: Type}.

    Definition dfa_rule := State -> (@ter T) -> State.

    Record dfa: Type :=
      mkDfa {
          start: State;
          final: list State;
          next: dfa_rule;
        }.

    Fixpoint final_state (next_d: dfa_rule) (s: State) (w: word): State :=
      match w with
        | nil => s 
        | h :: t => final_state next_d (next_d s h) t 
      end.

    Definition accepts (d : dfa) (s: State) (w: word) : Prop :=
      In (final_state (next d) s w) (final d). 

    Definition dfa_language (d : dfa) := (accepts d (start d)).

    
    Record s_dfa : Type :=
      s_mkDfa {
          s_start: State;
          s_final: State;
          s_next: dfa_rule;
        }.

    Definition s_accepts (d : s_dfa) (s: State) (w: word) : Prop :=
      (final_state (s_next d) s w) = (s_final d).

    Definition s_dfa_language (d : s_dfa) := (s_accepts d (s_start d)).

    Fixpoint split_dfa_list (st_d : State) (next_d : dfa_rule) (f_list : list State): list (s_dfa) :=
      match f_list with
        | nil => nil
        | h :: t => (s_mkDfa st_d h next_d) :: split_dfa_list st_d next_d t
      end.

    Definition split_dfa (d: dfa) := split_dfa_list (start d) (next d) (final d).

  End Definitions.
 
  Section Lemmas.

    Context {State T: Type}.

        
    Theorem test0:
      forall (w1 w2: @word T)
        (next: dfa_rule)
        (from to: State),
        final_state next from (w1 ++ w2) = to ->
        final_state next (final_state next from w1) w2 = to.
    Proof.
      intros w1 w2 nex.
      induction w1; eauto.
    Qed.
    
    Theorem test0_1:
      forall (w1 w2 : word)
        (next : dfa_rule)
        (from to: _),
        final_state next (final_state next from w1) w2 = to ->
        @final_state State T next from (w1 ++ w2) = to.
    Proof.
      intros w1 w2 next.
      induction w1; simpl; eauto.
    Qed.


    Theorem lemma2_3_1:
      forall (d : dfa)  (w : word),
        dfa_language d w ->
        language_list_union (map (@s_dfa_language State T) (split_dfa d)) w.
    Proof.
      intros d w.
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

    Theorem lemma2_3_2:
      forall (d : dfa ) (w : word),
        language_list_union (map s_dfa_language (split_dfa d)) w ->
        @dfa_language State T d w.
    Proof.
      intros d w.
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
 
(* 
    Theorem lemma2_3:
      forall (d : dfa),
        (dfa_language d T) [==] (language_list_union (map (@s_dfa_language State) (split_dfa d))).
    Proof.
      intros.
      apply mk_laguage_eq.
      apply lemma2_3_1.
      apply lemma2_3_2.
    Qed. *)

  End Lemmas.

<<<<<<< HEAD
End DFA.
=======
End DFA.
>>>>>>> 244d90840f1758459030ac37d374c9b056446e48
