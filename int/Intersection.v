Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop fingraph finfun finset.

Require Import fl.cfg.Base fl.cfg.Definitions fl.cfg.Dec_Empty fl.cfg.Binarize fl.cfg.Chomsky.
Require Import (* fl.int.Base2 *) (* INT.DFA*) fl.int.ChomskyInduction .
Require Import Fin.
Require Import fl.int.DFA fl.int.Union.


Module Intersection.

  Import ListNotations Dec_Empty Base Symbols DFA Base2.Base
         ChomskyInduction Definitions Derivation Chomsky.

  (* Feed tactic -- exploit with multiple arguments.
     (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013) *)
  Ltac feed H :=
    match type of H with
      | ?foo -> _ =>
        let FOO := fresh in
        assert foo as FOO; [|specialize (H FOO); clear FOO]
    end.

  Ltac feed_n n H :=
    match constr:n with
      | O => idtac
      | (S ?m) => feed H ; [| feed_n m H]
    end.
  
  (** * Util *)
  (** In this section we prove a few useful facts. *)      
  Section Util.
 
    Section Projections.
      
      Context {A B C: Type}.
      
      Definition fst3 (t: A * B * C): A := let '(from, _, _) := t in from.
      Definition snd3 (t: A * B * C): B := let '(_, r,_) := t in r.
      Definition thi3 (t: A * B * C): C := let '(_, _, to) := t in to.
      
    End Projections.
    
    Section Packing.

      Definition unVar {Vt: Type} (v: @var Vt) := let '(V e) := v in e.

      Section ToWordFunction.
        
        Context {T V: Type}.

        Fixpoint to_word (phrase: @phrase T V): list ter :=
          match phrase with
            | Ts x :: sx => x :: to_word sx
            | _ => []
          end.

        Lemma to_word_to_phraseK:
          forall word, to_word (to_phrase word) = word.
        Proof.
          intros w.
          induction w; auto.
          simpl; rewrite IHw; reflexivity.
        Qed.

      End ToWordFunction.

      Section EqSection.

        Context {T V1 V2: Type}.

        Variable F: V1 -> V2.
        
        Definition trans_var v :=
          V (F (unVar v)).
        
        Definition trans_symb symb: @symbol T V2 :=
          match symb with
            | Ts t => Ts t
            | Vs v => Vs (trans_var v)
          end.
        
        Definition trans_phrase p: @phrase T V2 :=
          map trans_symb p.

      End EqSection.
      
    End Packing.

    Section TerminalProp.

      Context {T V: Type}.
      
      Variable word word1 word2: @phrase T V.
      
      Lemma word_remains_terminal:
        forall word, terminal (@to_phrase T V word).
      Proof.
        intros w.
        induction w.
        - intros s IN; inversion IN.
        - intros s IN.
          inversion IN; auto.
          subst s; exists a; auto.
      Qed.       

      Lemma to_word_cat:
        terminal word1 ->
        terminal word2 ->
        to_word (word1 ++ word2) = to_word word1 ++ to_word word2.
      Proof.
        intros.
        induction word1 as [|a w]; auto.
        destruct a as [t|v]; simpl in *.
        rewrite IHw; [reflexivity|].
        intros s EL.
        apply H; right; exact EL.
        exfalso.
        unfold terminal in *.
        assert(EL: In (Vs v) (Vs v :: w)); auto.
        destruct  (H _ EL).
        inversion H1.
      Qed.

    End TerminalProp.

    Section Normalize.
      
      Context {Tt Vt: eqType}.

      Hypothesis H_T_eq_dec: eq_dec Tt.
      Hypothesis H_V_eq_dec: eq_dec Vt. 

      Variable TToNat: Tt -> nat.
      Variable UToNat: Vt -> nat.
      Variable NatToU: nat -> Vt.
      
      Hypothesis bijection: forall x : nat, UToNat (NatToU x) = x.

      (* Consider an arbitrary grammar  *)
      Variable G: @grammar Tt Vt.
      Variable S: @var Vt.
      Hypothesis H_S_el_of_G: Vs S el dom G.

      Let normalize G := @normalize Tt Vt _ _ TToNat UToNat NatToU bijection G. 
      
      Lemma epsilon_is_not_derivable_in_normalized_grammar:
        ~ language (normalize G) S [].
      Proof.
        intros NLANG.
        move: NLANG => [DER TER].
        apply empty_is_not_derivable in DER.
        - by done.
        - by apply chomsky_normalform.
      Qed.

    End Normalize.

    Section EpsilonGrammar.

      Context {Tt Vt: Type}.

      Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible.      

      (* Grammar which has only one epsilon rule. *)
      Variable var: @var Vt.
      Let epsilon_grammar: @grammar Tt Vt := [R var []].
      
      Lemma non_epsilon_is_not_derivable_in_epsilon_grammar:
        forall ter word,
          ~ der epsilon_grammar var (Ts ter :: to_phrase word).
      Proof.
        unfold syntactic_analysis_is_possible in *.
        intros ? ? ?.
        apply H_syntactic_analysis in H.
        move: H => [H | H].
        - by inversion H.
        - move: H => [rhs [EQ DER]].
          inversion EQ; inversion H; subst; clear H EQ.
          apply derivability_from_empty in DER.
            by inversion DER.
      Qed.
      
    End EpsilonGrammar.
    
  End Util.

  (** * Definitions and lemmas *)
  (** In this section we define a function that creates a intersection-grammar and prove the necessary lemmas. *)
  Section Lemmas. 
    
    Variable Tt Vt: Type.

    (* In this section we define a function which generates a list of states. 
       This list of states represents a set of states of a dfa. *)
    Section DFAListOfStates.
      
      Fixpoint values_list_gen number_of_states: list (t number_of_states) :=
        match number_of_states with
          | O => nil
          | S n' => F1 :: (map FS (values_list_gen n'))
        end.     

      Theorem all_values_in_list:
        forall (number_of_states: nat) (state: t number_of_states),
          state el values_list_gen number_of_states.
      Proof.
        intros.
        induction state; first by left.
          by right; apply in_map.
      Qed.

    End DFAListOfStates.

    (* Consider some list of dfa states. The dfa itself we will use later in this file. *)
    Variable number_of_states: nat.
    Let DfaState: Type := t number_of_states.
    Let list_of_states: list DfaState := values_list_gen number_of_states.

    (** In this section we define a function that creates a intersection-grammar out of a list of grammars and DFA.  *)
    Section Conversion.

      Context {T1 T2: Type}.
      
      Let TripleRule := @rule T1 (DfaState * @var T2 * DfaState).
      
      Definition convert_nonterm_rule_2 (r r1 r2: _) (s1 s2 : _): seq TripleRule :=
        map (fun s3 => R (V (s1, r, s3)) [Vs (V (s1, r1, s2)); Vs (V (s2, r2, s3))]) list_of_states.

      Definition convert_nonterm_rule_1  (r r1 r2: _) (s1 : _) :=
        flat_map (convert_nonterm_rule_2 r r1 r2 s1) list_of_states.

      Definition convert_nonterm_rule (r r1 r2: _) :=
        flat_map (convert_nonterm_rule_1 r r1 r2) list_of_states.

      Definition convert_terminal_rule (next: _) (r: _) (t: _): list TripleRule :=
        map (fun s1 => R (V (s1, r, next s1 t)) [Ts t]) list_of_states.

      Definition convert_rule (next: _) (r: _ ) :=
        match r with
          | R r [Vs r1; Vs r2] => convert_nonterm_rule r r1 r2
          | R r [Ts t] => convert_terminal_rule next r t 
          | _  => []
        end.
      
      Definition convert_rules (rules: list rule) (next: _): list rule :=
        flat_map (convert_rule next) rules.
      
      Definition convert_grammar (g: grammar) (s_dfa: s_dfa): @grammar _ (_ * _ * _):=
        convert_rules g (s_next s_dfa). 

    End Conversion.

    (** Next, we prove a few useful lemmas about the conversion function. *)    
    (* In this section we prove that if an initial grammar contains some terminal rule, 
       then the triple grammar contains the corresponding triple rule. We can simply get
       the triple rule using application of the "convert_rule" function. *)
    Section ForwardTerminalRuleInclusion.
      
      Variable G: @grammar Tt Vt. 

      (* We prove the lemma using the induction by the grammar (list of rules). 
         (1) "Base" case is trivial (G = []).
         (2) "Step" case splits into two subcases (G ~> a::G):
           a) R r [Ts te] = a: We just unfold definition convert_rules, 
               after some evaluation we will get the identity.
           b) R r [Ts te] el G: We use induction hypothesis. *)
      Lemma forward_terminal_rule_inclusion:
        forall (r: var) (te: ter) (next: _) (from to: DfaState),
          R r [Ts te] el G ->  
          next from te = to ->
          R (V (from, r, to)) [Ts te] el convert_rules G next.
      Proof. 
        intros r te next from to EL STEP.
        induction G; first by done.
        destruct EL as [EQ | EL].
        - clear IHg. subst a.
          apply in_or_app; left; simpl.
          apply in_map_iff.
          exists from; split.
          + by rewrite STEP.
          + by apply all_values_in_list.
        - by simpl; apply in_or_app; right; auto.
      Qed.

    End ForwardTerminalRuleInclusion.

    (* In this section we prove that if an initial grammar contains some nonterminal rule, 
       then the triple grammar contains the corresponding triple rule. We can simply get
       the triple rule using application of the "convert_rule" function. *)      
    Section ForwardNonterminalRuleInclusion.

      Variable G: @grammar Tt Vt.
      Variable next: @dfa_rule DfaState Tt.

      Variable from mid to: DfaState.
      Variable r r1 r2: @var Vt.

      Let R := @R Tt.
      
      Lemma forward_nonterminal_rule_inclusion'':
        R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
          convert_nonterm_rule_2 r r1 r2 from mid.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_2.
        set (vals := list_of_states).
        assert (H2: to el vals).
        apply all_values_in_list.  
        induction vals.
        simpl in H2.
        contradiction.
        simpl.  
        simpl in H2.
        destruct H2.
        left.
        rewrite H.
        auto.
        right.
        apply IHvals.
        exact H.
      Qed.

      Lemma forward_nonterminal_rule_inclusion':
        R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
          convert_nonterm_rule_1 r r1 r2 from.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_1.
        set (vals := list_of_states).
        assert (H2: mid el vals).
        apply all_values_in_list.
        induction vals.
        simpl in H2.
        contradiction.
        simpl.  
        simpl in H2.
        apply in_or_app. 
        destruct H2.
        left.
        rewrite H. 
        apply forward_nonterminal_rule_inclusion''.  
        right. 
        apply IHvals.
        apply H.
      Qed.

      (* We can prove this lemma simply by induction by grammar 
         (as in the case of the lemma forward_terminal_rule_inclusion) *)
      Lemma forward_nonterminal_rule_inclusion:
        R r [Vs r1; Vs r2] el G ->
        R (V (from, r, to)) [Vs (V (from, r1, mid)); Vs (V (mid, r2, to))] el convert_rules G next.
      Proof.
        intros EL.
        induction G; first by done.
        destruct EL as [ | EL]; subst.
        { clear IHg.
          apply in_or_app; left; simpl.
          set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
          unfold convert_nonterm_rule.
          set (vl := list_of_states).
          assert (EL: from el vl).
          apply all_values_in_list.
          apply in_flat_map.
          exists from.
          split; [exact EL | apply forward_nonterminal_rule_inclusion']. }  
        { apply in_app_iff; right.
          apply IHg.
          exact EL. }
      Qed.

    End ForwardNonterminalRuleInclusion. 

    (* In this section we prove that if a triple grammar contains some rule, 
       then the initial grammar contains corresponding "single" rule. *)
    Section BackwardRuleInclusion.

      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: @dfa_rule DfaState Tt.

      (* For simplicity, let's define a local name. *)
      Let projection (s: @symbol Tt (DfaState * var * DfaState)): @symbol Tt Vt :=
        match s with
          | Vs (V (_, r, _)) => Vs r
          | Ts (T r) => Ts (T r)
        end.

      (* We prove that we can simply project a triple rule into an initial one. *)
      Lemma backward_rule_inclusion:
        forall rhs lhs, 
          R rhs lhs el convert_rules G next ->
          R (snd3 (unVar rhs)) (map projection lhs) el G.
      Proof. 
        intros.
        destruct rhs as [[[from r] to]]; simpl in *.
        unfold convert_rules in *.
        apply in_flat_map in H.
        destruct H as [[r' rhs'] [RIN EL]].
        unfold convert_rule in *.
        destruct rhs' as [ | [[t1]|v1] ].
        - inversion EL.
        - destruct rhs'.
          + unfold convert_terminal_rule in *.
            apply in_map_iff in EL.
            destruct EL as [s [EQ EL]].
            inversion EQ; subst; exact RIN.
          + inversion EL.
        - destruct rhs' as [ | [ | ]]; try inversion EL.
          destruct rhs'; try inversion EL.
          unfold convert_nonterm_rule in EL.
          apply in_flat_map in EL.
          destruct EL as [st [_ EL]].
          unfold convert_nonterm_rule_1 in EL.
          apply in_flat_map in EL.
          destruct EL as [st' [_ EL]].
          unfold convert_nonterm_rule_2 in EL.
          apply in_map_iff in EL.
          destruct EL as [st'' [EQ _]].
          inversion EQ.      
            by subst; simpl.
      Qed.
      
      Corollary backward_terminal_rule_inclusion:
        forall from r to t, 
          R (V (from, r, to)) [Ts t] el convert_rules G next ->
          R r [Ts t] el G.
      Proof.
        intros; destruct t as [t].
        apply backward_rule_inclusion in H; simpl in *; exact H.
      Qed.

      Corollary backward_nonterminal_rule_inclusion:
        forall from from1 from2 r r1 r2 to to1 to2, 
          R (V (from, r, to)) [Vs (V (from1, r1, to1)); Vs (V (from2, r2, to2))]
            el convert_rules G next ->
          R r [Vs r1; Vs r2] el G.
      Proof.
          by intros; apply backward_rule_inclusion in H.
      Qed.

    End BackwardRuleInclusion.

    (* In this section, we prove that after transformation grammar remains in chomsky normal form. *)
    Section RemainsInChomskyNormalForm.

      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: @dfa_rule DfaState Tt.      

      (* Note that the initial grammar is in chomsky normal form. 
         After the transformation:
         1) There are no (new) epsilon rules
         2) The terminal rules remain terminal and uniform 
             (see the definition of grammar to be in chomsky normal form)
         3) Rules remain in binarize form
         4) And unitfree. *)
      Lemma remains_chomsky:
        chomsky (convert_rules G next).
      Proof.
        destruct H_G_in_chomsky_normal_form as [EF [UN [BIN UF]]].
        repeat split.
        { intros v rhs EL CONTR; subst rhs.
          destruct v as [[[from r] to]].
          apply backward_rule_inclusion in EL; simpl in *.
            by apply EF in EL.
        }
        { unfold Separate.uniform.
          intros v rhs EL t TEL.
          destruct t as [t].
          unfold Separate.uniform in UN.
          destruct v as [[[from v] to]].
          apply backward_rule_inclusion in EL; simpl in *.
          apply UN with (a := T t) in EL.
          destruct rhs as [ | [[t'] | []]]; simpl in *.
          + by inversion TEL.
          + inversion EL; apply map_eq_nil in H1.
              by subst; auto.
          + inversion EL; apply map_eq_nil in H1.
            subst.
              by destruct TEL as [TEL | TEL]; inversion TEL.
          + apply in_map_iff.
              by exists (Ts (T t)); split; auto. }
        { unfold Binarize.binary.
          intros v phs EL.
          destruct v as [[[from v] to]].
          apply backward_rule_inclusion in EL.
          apply BIN in EL.
            by rewrite map_length in EL.
        }
        { unfold ElimU.unitfree. intros v CONTR.
          destruct v as [[[from r] to]].
          destruct CONTR as [[[[from' r'] to']] EL].
          apply backward_rule_inclusion in EL; simpl in *.
          unfold ElimU.unitfree in *.
          eapply UF.
            by exists r'; eauto. }
      Qed.

    End RemainsInChomskyNormalForm.  

    (* In this section, we prove that the triple-rules have certain consistent structure. *)
    Section ConsistensyOfTripleRules.

      Variable G: @grammar Tt Vt.
      Variable next: @dfa_rule DfaState Tt.

      Lemma consistensy_of_triple_nonterm_rules:
        forall from from1 from2 r r1 r2 to to1 to2,
          R (V (from, r, to)) [Vs (V (from1, r1, to1)); Vs (V (from2, r2, to2))]
            el convert_rules G next ->
          from = from1 /\ to1 = from2 /\ to = to2.
      Proof.
        intros r r1 r2 from from1 from2 to to1 to2 EL.
        unfold convert_rules in EL.
        apply in_flat_map in EL.
        destruct EL as [rule [_ EL]].
        destruct rule as [v rhs].
        destruct rhs; simpl in *; first by done.
        destruct s; simpl in *.
        { destruct rhs; [| inversion EL].
          unfold convert_terminal_rule in *.
            by apply in_map_iff in EL; destruct EL as [st [EQ _]]. }
        { destruct rhs; [inversion EL | ].
          destruct s; [ inversion EL | ].
          destruct rhs; [ | inversion EL].
          unfold convert_nonterm_rule in EL.
          unfold convert_nonterm_rule_1 in EL.
          unfold convert_nonterm_rule_2 in EL.
          apply in_flat_map in EL. destruct EL as [st1 [_ EL]].
          apply in_flat_map in EL; destruct EL as [st2 [_ EL]].
          apply in_map_iff in EL; destruct EL as [st3 [EQ _]].
            by inversion EQ. }
      Qed.

      Lemma consistensy_of_triple_term_rules:
        forall from r to te,
          R (V (from, r, to)) [Ts te] el convert_rules G next ->
          next from te = to.
      Proof.
        intros r from to te EL.
        unfold convert_rules in EL.
        apply in_flat_map in EL.
        destruct EL as [rule [_ EL]].
        destruct rule as [v rhs].
        destruct rhs; first by done.
        destruct s; simpl in *.
        { destruct rhs; [| inversion EL].
          unfold convert_terminal_rule in *.
          apply in_map_iff in EL; destruct EL as [st [EQ _]].
            by inversion EQ. }
        { destruct rhs; [inversion EL | ].
          destruct s; [ inversion EL | ].
          destruct rhs; [ | inversion EL].
          unfold convert_nonterm_rule in EL.
          unfold convert_nonterm_rule_1 in EL.
          unfold convert_nonterm_rule_2 in EL.
          apply in_flat_map in EL. destruct EL as [st1 [_ EL]].
          apply in_flat_map in EL; destruct EL as [st2 [_ EL]].
          apply in_map_iff in EL; destruct EL as [st3 [EQ _]].
            by inversion EQ. }
      Qed.
      
      Corollary consistensy_of_triple_nonterm_rules':
        forall r r1 r2,
          R (V r) [Vs (V r1); Vs (V r2)] el convert_rules G next ->
          fst3 r = fst3 r1 /\ thi3 r1 = fst3 r2 /\ thi3 r = thi3 r2.
      Proof.
        intros.
        destruct r as [[from r] to].
        destruct r1 as [[from1 r1] to1].
        destruct r2 as [[from2 r2] to2].
        simpl in *.
        eapply consistensy_of_triple_nonterm_rules; eauto.
      Qed.
      
      Corollary consistensy_of_triple_term_rules':
        forall (r : _) (te : ter),
          R (V r) [Ts te] el (convert_rules G next) ->
          next (fst3 r) te = thi3 r.
      Proof.
        intros r te H0.
        destruct r as [[from0 r0] to0].
        simpl in *.
        eapply consistensy_of_triple_term_rules; eauto.
      Qed.
      
    End ConsistensyOfTripleRules.

    (** * Main implications *)
    (** In this section we prove two main lemmas. Derivability in an initial grammar 
        and a dfa implies a derivability in the triple (intersection) grammar. And the other way
        around a derivability in a triple grammar implies a derivability in the initial grammar 
        and the dfa. *)
    Section MainImplications.

      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.
      Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 

      (* We need two fictive functions for changing types. *)
      Hypothesis F1: DfaState * @var Vt * DfaState -> Vt. 
      Hypothesis F2: Vt -> DfaState * @var Vt * DfaState. 

      (* It this section we prove that derivability in an initial grammar 
         and a dfa implies a derivability in the triple grammar. *)
      Section MainForward.

        (* Note that we cannot use simple induction by derivation in grammar G, in this 
           case we will get a phrase (list of terminals and nonterminals) instead of a word. 
           Therefore we should use another way to use induction. For grammar in chomsky 
           normal form it is possible (see the file chomsky_induction). Briefly, we can 
           split the word into two subwords, each of which can be derived from some nonterminal. *)
        Theorem der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar:
          forall (next: dfa_rule) (r: var) (from to: DfaState) (word: _),
            der G r (to_phrase word) ->
            final_state next from word = to ->
            der (convert_rules G next) (V (from, r, to)) (to_phrase word).
        Proof.
          intros next r from to w DER FIN.          
          rewrite <- (@to_word_to_phraseK Tt Vt w) in FIN.
          set (wp1 := to_phrase (T:=Tt) (V:= _ * @var Vt * _) w) in *.
          set (wp2 := trans_phrase F2 (to_phrase w)) in *.
          assert (D: wp1 = wp2).
          { clear; induction w; simpl in *.
            reflexivity.
            unfold wp1, wp2.
            rewrite <- IHw; auto. }
          rewrite D; clear D.
          generalize dependent FIN. 
          generalize dependent from.
          generalize dependent to.
          generalize dependent next.
          apply chomsky_derivability_induction with 
          (P := fun r phr =>
                  forall (next : dfa_rule) (from to : DfaState),
                    final_state next from (to_word phr) = to ->
                    der (convert_rules G next) (V (from, r, to)) (trans_phrase F2 phr)) in DER; auto.
          { intros r0 t IN next from to FIN; simpl in *.
              by apply rDer, forward_terminal_rule_inclusion; auto. }
          { intros r0 r1 r2 w1 w2 IN Ind1 Ind2 TER1 TER2 DER1 DER2 next from to FIN0.
            set (newG := convert_rules G next).
            set (m := final_state next from (to_word w1)).
            assert (H1: der newG (V (from, r1, m)) (trans_phrase F2 w1)); eauto.
            assert (H2: der newG (V (m, r2, to)) (trans_phrase F2 w2)).
            { apply Ind2, test0.
              rewrite <- to_word_cat; auto. }
            assert (in_H: In (R (V (from, r0, to)) [Vs (V(from, r1, m)); Vs (V (m, r2, to))]) newG).
            { apply forward_nonterminal_rule_inclusion; auto. }
            unfold trans_phrase.
            rewrite map_cat.
              by eapply derivability_step; eauto. }
          { by apply word_remains_terminal. }
        Qed.

        (* We use the lemma above to prove this lemma. *)
        Theorem main_forward:
          forall sdfa var word,
            s_dfa_language sdfa word /\ language G var (to_phrase word) ->
            language (convert_grammar G sdfa) (V (s_start sdfa, var, s_final sdfa)) (to_phrase word).
        Proof.
          intros ? ? ? INT.
          destruct INT as [DFA [DER TER]].
            by split; [apply der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar | apply word_remains_terminal].
        Qed.
        
      End MainForward.

      (* In this section we prove that derivability in a triple grammar 
         implies derivability in the initial grammar and the dfa. *)
      Section MainBackward.

        Section DerivabilityInTripleGrammarImpliesAcceptanceInDFA.

          Variable next: @dfa_rule DfaState Tt.
          Variable from to: DfaState.

          (* Here we also should use "chomsky_induction". Proof is quite similar to the proof 
             of the der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar lemma. *)
          Lemma der_in_triple_grammar_implies_dfa_accepts':
            forall var word,           
              der (convert_rules G next) (V (from, var, to)) (to_phrase word) ->     
              final_state next (fst3 (from, var, to)) word = thi3 (from, var, to).
          Proof. 
            intros r w H.
            assert (EQ: w = to_word (to_phrase(T:=Tt) (V:=DfaState * @var Vt * DfaState) w)).
            { clear.
              induction w; simpl.
              - reflexivity.
              - rewrite <- IHw; reflexivity.
            } rewrite EQ; clear EQ.
            assert (P1: fst3 (from, r, to) = fst3 (unVar (V (from, r, to)))). simpl; reflexivity.
            assert (P2: thi3 (from, r, to) = thi3 (unVar (V (from, r, to)))). simpl; reflexivity.
            rewrite P1; rewrite P2; clear P1 P2.
            apply chomsky_derivability_induction
            with (w0 := to_phrase w) (r0 := V (from, r, to)) (G0 := convert_rules G next); auto; simpl.
            { apply remains_chomsky; auto. }
            { clear H r.
              intros. 
              eapply consistensy_of_triple_term_rules'.
              destruct r; eauto. }
            { clear H r from to. 
              intros r r1 r2 w1 w2 IN FIN1 FIN2 TER1 TER2 DER1 DER2.
              rewrite to_word_cat; auto.
              apply test0_1.
              destruct r as [[[fr r] to]].
              destruct r1 as [[[fr1 r1] to1]].
              destruct r2 as [[[fr2 r2] to2]].
              simpl in *.      
              assert (EQ:= @consistensy_of_triple_nonterm_rules' G next (fr, r, to) (fr1, r1, to1) (fr2, r2, to2) IN).
              destruct EQ as [EQ1 [EQ2 EQ3]]; simpl in *.
              subst fr to1 to2.
                by rewrite EQ2 EQ3. }
            { by apply word_remains_terminal. }
          Qed.

          Lemma der_in_triple_grammar_implies_dfa_accepts:
            forall var word,
              der (convert_rules G next) (V (from, var , to)) (to_phrase word) ->
              final_state next from word = to.
          Proof.
            intros w r DER. 
            set (rule := (from, r, to)) in *.
            assert (H1: from = fst3 rule); auto.
            assert (H2: to = thi3 rule); auto.
            rewrite H1 H2.
            eapply der_in_triple_grammar_implies_dfa_accepts'; eauto 1.
          Qed.
          
        End DerivabilityInTripleGrammarImpliesAcceptanceInDFA.

        Section DerivabilityInTripleGrammarImpliesDerivabilityInInitialGrammar.

          Variable next: @dfa_rule DfaState Tt.
          
          Lemma der_in_triple_gr_implies_der_in_initial_gr':
            forall (r: var) word,
              der (convert_rules G next) r (to_phrase word) ->
              der G (snd3 (unVar r)) (to_phrase word). 
          Proof.
            intros r w H.
            assert (EQ: trans_phrase F1 (to_phrase  w) = to_phrase w).
            { clear.
              induction w; simpl.
              - reflexivity.
              - rewrite IHw. reflexivity. }
            rewrite <- EQ.
            apply chomsky_derivability_induction with (G0 := convert_rules G next) (r0 := r) (w0 := to_phrase w); auto.
            { apply remains_chomsky; auto. }
            { intros r' t IN.
              destruct r' as [[[from r'] to]]; simpl in *.
              apply rDer; apply backward_terminal_rule_inclusion in IN; auto. }
            { intros r' r1 r2 w1 w2 IN DER1 DER2 TER1 TER2 DER3 DER4.
              destruct r' as [[[from r'] to]].
              destruct r1 as [[[from1 r1] to1]].
              destruct r2 as [[[from2 r2] to2]]; simpl in *.
              unfold trans_phrase.
              rewrite map_cat.
              apply @derivability_step with (r1 := r1) (r2 := r2) (T := Tt) (V := Vt); auto.
                by apply backward_nonterminal_rule_inclusion in IN. }
            { by apply word_remains_terminal. }
          Qed.

          Lemma der_in_triple_gr_implies_der_in_initial_gr:
            forall (s_start s_final: DfaState) (grammar_start: _) (word: word),  
              der (convert_rules G next) (V (s_start, grammar_start, s_final)) (to_phrase word) ->
              der G grammar_start (to_phrase word).
          Proof.
            intros start final g_start w.
            set (s := (start, g_start, final)).
            assert (g_start = snd3 s); auto.
            rewrite H.
            eapply der_in_triple_gr_implies_der_in_initial_gr'.  
          Qed.  

        End DerivabilityInTripleGrammarImpliesDerivabilityInInitialGrammar.

        (* Now we can split the conclusion of the lemma and use the lemmas above to finish the proof. *)
        Theorem main_backward:
          forall sdfa var word,
            language (convert_grammar G sdfa) (V (s_start sdfa, var, s_final sdfa)) (to_phrase word) ->
            s_dfa_language sdfa word /\ language G var (to_phrase word).
        Proof. 
          intros ? ? ? TR.
          destruct TR as [DER TER]. 
          unfold convert_grammar in DER.
          destruct sdfa; simpl in *.
          split.
          unfold s_dfa_language, s_accepts; simpl.
          eapply der_in_triple_grammar_implies_dfa_accepts; eauto 1.
          split.
          - by eapply der_in_triple_gr_implies_der_in_initial_gr; eauto 1.
          - by apply word_remains_terminal.
        Qed.

      End MainBackward. 
      
    End MainImplications.

  End Lemmas.
  
  (** * Main Theorem *)
  (** In this section we prove the main theorem about existence of grammar of intersection. *)  
  Section Main.
    
    Context {Terminal Nonterminal: eqType}.
    Hypothesis H_T_eq_dec: eq_dec Terminal.
    Hypothesis H_V_eq_dec: eq_dec Nonterminal.

    Variables (TToNat: Terminal -> nat) (UToNat: Nonterminal -> nat) (NatToU: nat -> Nonterminal).
    Hypothesis bijection: forall x : nat, UToNat (NatToU x) = x.

    Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible.
    
    Variable number_of_states: nat.
    Let DfaState: Type := t number_of_states.
    Let list_of_states: list DfaState := values_list_gen number_of_states.

    (* Consider an arbitrary dfa with n states. *)
    Variable dfa: @dfa DfaState Terminal. 

    (* Consider an arbitrary grammar G with start symbol S. *)
    Variable G: @grammar Terminal Nonterminal.
    Variable S: @var Nonterminal.
    Hypothesis H_S_el_of_G: Vs S el dom G.

    (* We prove that there exists grammar intersection. *)
    Theorem grammar_of_intersection_exists:
      exists (NewNonterminal: Type) (IntersectionGrammar: @grammar Terminal NewNonterminal) St,
        forall word,
          dfa_language dfa word /\ language G S (to_phrase word) <->
          language IntersectionGrammar St (to_phrase word).
    Proof.
      have Alt: forall n, n == 0 \/ n > 0.
      { by move => m; case m; [left|right]. }
      move: (Alt number_of_states) => [/eqP ZERO | POS]; clear Alt.
      { exfalso; subst number_of_states.
        destruct dfa.
        have C0 := case0 (fun _ => false).
          by apply C0 in start0.
      } 
      intros.
      set (NG := @normalize Terminal Nonterminal _ _ TToNat UToNat NatToU bijection G).
      set (SDFAS := split_dfa dfa).
      set (TRS :=
             map (fun s_dfa =>
                    (V (s_start s_dfa, S, s_final s_dfa), @convert_grammar _ _ _ NG s_dfa)) SDFAS).
      set (I := (V (Union.start (t number_of_states * @var Nonterminal * t number_of_states)), Union.grammar_union TRS)).
      set (I1 := fst I).
      set (I2 := snd I).
      have ALT:
        (@dfa_language DfaState Terminal dfa [] /\ language G S []) \/
        (~ @dfa_language DfaState Terminal dfa [] \/ ~ language G S []).
      { have DECDFA: {dfa_language dfa []} + {~ dfa_language dfa []}.
        { apply list_in_dec.
          unfold DfaState.
          intros x y.
          unfold dec.
          apply Fin.eq_dec.
        } 
        have DECLANG: {language G S []} + {~ language G S []}.
        { intros. have DER := @Dec_Word.der_dec _ _ H_T_eq_dec H_V_eq_dec G S [].
          move: DER => [DER|DER].
          - by left; split.
          - right; intros CONTR; apply: DER.
              by move: CONTR => [DER _].
        } 
        move: DECDFA DECLANG => [H1|H1] [H2|H2]; [left|right|right|right].
        - by done.
        - by right.
        - by left.
        - by left.
      }
      move: ALT => [EPS|EPS].
      { set (II :=
               (V (Union.start (Union.labeled_Vt (t number_of_states * @var Nonterminal * t number_of_states))),
                @Union.grammar_union Terminal (Union.labeled_Vt (t number_of_states * var * t number_of_states))
                                     [:: (I1, [R I1 []]); (I1, I2)])).
        set (II1 := fst II).
        set (II2 := snd II).       
        exists ((Union.labeled_Vt (Union.labeled_Vt (t number_of_states * @var Nonterminal * t number_of_states)))), II2, II1.
        intros w.
        case: w => [|].
        { split; intros.
          - apply Union.correct_union_2.
            exists (I1, [R I1 []]); simpl; split.
            + split; last by done.
                by apply rDer.
            + by left.
          - by simpl.
        }
        {   
          intros a w.
          split; [move => [DL GL]| move => IL].
          apply Union.correct_union_2. 
          exists (I1, I2).
          split; last by right.
          { apply H_correct_split in DL.
            move: DL => [s_dfa [EL LANG]].
            have MF := @main_forward Terminal Nonterminal number_of_states NG _ _ _ s_dfa S (a::w).
            feed_n 4 MF; try done.
            { by apply chomsky_normalform. }
            { intros; repeat split.
              - destruct number_of_states; [by done | by apply F1].
              - by done.
              - destruct number_of_states; [by done | by apply F1].
            }
            { by split; last apply language_normalform. }
            eapply Union.correct_union_2.
            exists ((V (s_start s_dfa, S, s_final s_dfa)), convert_grammar NG s_dfa); simpl.
            split.
            - by done.
            - unfold TRS.
              apply in_map_iff.
              exists s_dfa; split; by done.
          }
          {  
            intros.
            unfold I2, I1, I in IL.
            eapply Union.correct_union_2 in IL.
            move: IL => [[gr v] [LANG EL]]; simpl in *.
            unfold TRS in EL.
            move: EL => [EL | [EL| EL ]].
            { exfalso.
              inversion EL; subst gr; subst v; clear EL.
              move: LANG => [DER _].
                by apply non_epsilon_is_not_derivable_in_epsilon_grammar in DER. }
            { inversion EL; subst gr; subst v; clear EL.
              have CORRECT := Union.correct_union_2 _ (a::w).
              apply CORRECT in LANG.
              move: LANG => [[v gr] [LANG EL]].
              unfold I2, I in EL.
              unfold TRS in EL; apply in_map_iff in EL.
              move: EL => [s_dfa [EQ EL]].
              inversion EQ; subst gr; subst v; clear EQ.
              have MB := @main_backward Terminal Nonterminal number_of_states NG _ _ _ s_dfa S (a::w).
              feed_n 4 MB; try done.
              { by apply chomsky_normalform. }
              { by intros; apply NatToU. }
              clear LANG.
              move: MB => [SDFA LANG].
              split.
              - unfold SDFAS in EL.
                apply H_correct_split.
                exists s_dfa; split; by done.
              - eapply (@language_normalform) with (Id3 := bijection) (TtToNat := TToNat); eauto 2.
                intros CONTR; inversion CONTR. 
            }
            { by done. }
          }  
        } 
      }
      {
        exists (((Union.labeled_Vt (t number_of_states * @var Nonterminal * t number_of_states)))), I2, I1.
        intros w.
        case: w => [ | ].
        { 
          split; intros.
          - exfalso.
            move: H => [H1 H2].
              by move: EPS => [H|H]; apply: H.
          - clear EPS; exfalso; simpl in H.
            unfold I2, I1, I in H.
            have CORRECT := Union.correct_union_2 _ []. 
            apply CORRECT in H.
            move: H => [[v gr] [LANG EL]]; simpl in LANG.
            unfold TRS in EL; apply in_map_iff in EL.
            move: EL => [s_dfa [EQ EL]].
            inversion EQ; subst v; subst gr; clear EQ.
            have MB := @main_backward Terminal Nonterminal number_of_states NG _ _ _ s_dfa S ([]).
            feed_n 4 MB; try done.
            { by apply chomsky_normalform. }
            { by intros; apply NatToU. }
            clear LANG.
            move: MB => [DLANG LANG].
            simpl in LANG.
            unfold NG in LANG.
              by apply epsilon_is_not_derivable_in_normalized_grammar in LANG.
        }
        { 
          intros a w.
          split; [move => [DL GL]| move => IL].
          { apply H_correct_split in DL.
            move: DL => [s_dfa [EL LANG]].
            have MF := @main_forward Terminal Nonterminal number_of_states NG _ _ _ s_dfa S (a::w).
            feed_n 4 MF; try done.
            { by apply chomsky_normalform. }
            { intros; repeat split.
              - destruct number_of_states; [by done | by apply F1].
              - by done.
              - destruct number_of_states; [by done | by apply F1].
            }
            { by split; last apply language_normalform. }
            eapply Union.correct_union_2.
            exists ((V (s_start s_dfa, S, s_final s_dfa)), convert_grammar NG s_dfa); simpl.
            split.
            - by done.
            - unfold TRS.
              apply in_map_iff.
              exists s_dfa; split; by done.
          }
          { intros.
            unfold I2, I1, I in IL.
            eapply Union.correct_union_2 in IL.
            move: IL => [[gr v] [LANG EL]]; simpl in *.
            unfold TRS in EL.
            apply in_map_iff in EL.
            move: EL => [s_dfa [EQ EL]].
            inversion EQ; subst gr; subst v; clear EQ.
            have MB := @main_backward Terminal Nonterminal number_of_states NG _ _ _ s_dfa S (a::w).
            feed_n 4 MB; try done.
            { by apply chomsky_normalform. }
            { by intros; apply NatToU. }
            clear LANG.
            move: MB => [SDFA LANG].
            split.
            - unfold SDFAS in EL.
              apply H_correct_split.
              exists s_dfa; split; by done.
            - eapply (@language_normalform) with (Id3 := bijection) (TtToNat := TToNat); eauto 2.
              intros CONTR; inversion CONTR.
          }
        }
      } 
    Qed. 
    
  End Main.
  
End Intersection.
