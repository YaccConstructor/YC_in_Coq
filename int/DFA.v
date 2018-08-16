Require Import List.
Require Import Fin.

Require Import fl.cfg.Definitions.
Require Import fl.int.Base2.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop fingraph finfun finset.

Module DFA.

  Import Base Base2 Definitions.
  
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

        
    Example test0:
      forall (w1 w2: @word T)
        (next: dfa_rule)
        (from to: State),
        final_state next from (w1 ++ w2) = to ->
        final_state next (final_state next from w1) w2 = to.
    Proof.
      intros w1 w2 nex.
      induction w1; eauto.
    Qed.
    
    Example test0_1:
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
      forall (d : @DFA.dfa State T)  (w : word),
        dfa_language d w ->
        exists sdfa : s_dfa,
          In sdfa (split_dfa d) /\ s_dfa_language sdfa w.
    Proof.
      intros dfa word LANG.
      destruct dfa; unfold split_dfa; simpl.
      unfold dfa_language, accepts in LANG; simpl in LANG.
      induction final0.
      { simpl in LANG; elim LANG. }
      { simpl in LANG.
        destruct LANG; [subst a | ].
        { exists ({|
                     s_start := start0;
                     s_final := final_state next0 start0 word;
                     s_next := next0 |}).
            by simpl; split; [left | ].
        }
        { 
          apply IHfinal0 in H; clear IHfinal0.
          move: H => [s_dfa [IN sLANG]].
          unfold s_dfa_language, s_accepts; simpl.
          exists s_dfa.
            by split; [right | ].
        }
      }
    Qed.    

    Theorem lemma2_3_2:
      forall (d : @dfa State T) (w : word),
      (exists sdfa : s_dfa,
          In sdfa (split_dfa d) /\ s_dfa_language sdfa w) ->
      @dfa_language State T d w.
    Proof.
      move => dfa word [s_dfa [IN sLANG]].
      unfold dfa_language, accepts.
      destruct dfa; unfold split_dfa in *; simpl in *.
      induction final0; first by done.
      simpl in IN; move: IN => [EQ|IN]; [subst; clear IHfinal0 | ].
      { by left; unfold s_dfa_language, s_accepts in sLANG; simpl in sLANG. }
      { apply IHfinal0 in IN; clear IHfinal0; rename IN into IH.
          by simpl; right. } 
    Qed.
    
  
    (* TODO: del *)
    (* Feed tactic -- exploit with multiple arguments.
       (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013) *)
    Ltac feed H :=
      match type of H with
        | ?foo -> _ =>
          let FOO := fresh in
          assert foo as FOO; [|specialize (H FOO); clear FOO]
      end.
    
    Lemma correct_split:
      forall dfa w,
        @dfa_language State T dfa w <->
        exists sdfa, In sdfa (split_dfa dfa) /\ s_dfa_language sdfa w.
    Proof.
      intros dfa w.
      split; intros H. 
      - by apply lemma2_3_1. 
      - by apply lemma2_3_2. 
    Qed.

  End Lemmas.

End DFA.