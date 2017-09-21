Require Import List.
Require Import Fin.

Add LoadPath "../".

Require Import CFG.Base CFG.Definitions CFG.Binarize CFG.Chomsky.
Require Import INT.Base INT.DFA INT.ChomskyInduction.

Module Intersection.

  Import ListNotations INT.Base.Base CFG.Base.Base Symbols DFA ChomskyInduction Definitions Derivation Chomsky.

  Section Util.

    Section Proections.
      
      Context {A B C: Type}.
      
      Definition fst3 (t: A * B * C): A := let '(from, _, _) := t in from.
      Definition snd3 (t: A * B * C): B := let '(_, r,_) := t in r.
      Definition thi3 (t: A * B * C): C := let '(_, _, to) := t in to.
      
    End Proections.
    
    Section Packing.
      
      Section SEction100.
        
        Context {Tt Vt: Type}.
        
        Definition unTer (t: ter): Tt := let '(T e) := t in e.
        Definition unVar (v: var): Vt := let '(V e) := v in e.

      End SEction100.

      Section Sec.
        
        Context {T V: Type}.

        Fixpoint to_phrase (w: word): @phrase T V :=
          match w with
            | s::sx => Ts s :: to_phrase sx
            | _ => []
          end.
        
        Fixpoint to_word (p: @phrase T V): list ter :=
          match p with
            | Ts x :: sx => x :: to_word sx
            | _ => []
          end.


        Lemma lemma2: forall (w: word), terminal (to_phrase w).
        Proof.
          intros w.
          induction w.
          - intros s IN; inversion IN.
          - intros s IN.
            inversion IN; auto.
            subst s; exists a; auto.
        Qed.

        Lemma lemma3: forall (w: word), to_word (to_phrase w) = w.
        Proof.
          intros w.
          induction w; auto.
          simpl; rewrite IHw; reflexivity.
        Qed.

      End Sec.

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

    Section Terminal.

      Context {T V: Type}.

      Variable w1 w2: @phrase T V.
      
      Lemma lemma23:
        terminal w1 ->
        terminal w2 ->
        to_word (w1 ++ w2) = to_word w1 ++ to_word w2.
      Proof.
        intros.
        induction w1 as [|a w]; auto.
        destruct a as [t|v]; simpl in *.
        rewrite IHw; [reflexivity|].
        intros s EL.
        apply H; right; exact EL.
        exfalso.
        unfold terminal in *.
        assert(EL: Vs v el Vs v :: w); auto.
        destruct  (H _ EL).
        inversion H1.
      Qed.
      
    End Terminal.

    Section DFAListValues.
      
      Fixpoint values_list_gen n: list (t n) :=
        match n with
          | O => nil
          | S n' => F1 :: (map FS (values_list_gen n'))
        end.     
      
      Theorem all_values_in_list:
        forall (n: nat) (f: t n), f el values_list_gen n.
      Proof.
        intros; induction f; [left | right].
        reflexivity.
        apply in_map; exact IHf.
      Qed.

    End DFAListValues.
    
  End Util.


  Section SomeSection.
    
    (* TODO: comment *)
    Variable n: nat.
    Let DfaState: Type := t n.
    Let values_list: list DfaState := values_list_gen n.
    
    (* TODO: comment *)
    Variable Tt Vt: Type.

    Section Conversion.

      Context {T1 T2: Type}.

      Section ToTriple.

        Let TripleRule := @rule T1 (DfaState * @var T2 * DfaState).

        Definition convert_nonterm_rule_2 (r r1 r2: _) (s1 s2 : _): list TripleRule :=
          map (fun s3 => R (V (s1, r, s3)) [Vs (V (s1, r1, s2)); Vs (V (s2, r2, s3))]) values_list.

        Definition convert_nonterm_rule_1  (r r1 r2: _) (s1 : _) :=
          flat_map (convert_nonterm_rule_2 r r1 r2 s1) values_list.

        Definition convert_nonterm_rule (r r1 r2: _) :=
          flat_map (convert_nonterm_rule_1 r r1 r2) values_list.

        Definition convert_terminal_rule (next: _) (r: _) (t: _): list TripleRule :=
          map (fun s1 => R (V (s1, r, next s1 t)) [Ts t]) values_list.

        Definition convert_rule next r :=
          match r with
            | R r [Vs r1; Vs r2] => convert_nonterm_rule r r1 r2
            | R r [Ts t] => convert_terminal_rule next r t 
            | _  => []
          end.

      End ToTriple.

      Definition convert_rules (rules: list rule) (next : dfa_rule): list rule :=
        flat_map (convert_rule next) rules.
      
      Definition convert_grammar (g: grammar) (d: s_dfa): grammar :=
        convert_rules g (s_next d).

    End Conversion.


    Hint Resolve lemma2.


    Section ForwardTerminalRuleInclusion.
      
      Variable G: @grammar Tt Vt.
      
      Lemma forward_terminal_rule_inclusion:
        forall (r: var) (te: ter) (next: dfa_rule) (from to: DfaState),
          R r [Ts te] el G ->  
          next from te = to ->
          R (V (from, r, to)) [Ts te] el convert_rules G next.
      Proof. 
        intros r te next from to EL STEP.
        induction G; [auto | ].

        destruct EL as [EQ | EL].
        - subst a.
          apply in_or_app; left; simpl.
          apply in_map_iff.
          exists from; subst to.
          split; [reflexivity | apply all_values_in_list].
        - simpl.
          apply in_or_app; right.
          auto.
      Qed.

    End ForwardTerminalRuleInclusion.
    
    Section ForwardNonterminalRuleInclusion.

      Variable G: @grammar Tt Vt.
      Variable next: @dfa_rule DfaState Tt.

      Variable from mid to: DfaState.
      Variable r r1 r2: @var Vt.
      
      Lemma forward_nonterminal_rule_inclusion'':
        @R Tt _ (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
           convert_nonterm_rule_2 r r1 r2 from mid.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_2.
        set (vals := values_list).
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
        @R Tt _ (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
           convert_nonterm_rule_1 r r1 r2 from.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_1.
        set (vals := values_list).
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

      Lemma forward_nonterminal_rule_inclusion:
        R r [Vs r1; Vs r2] el G ->
        R (V (from, r, to)) [Vs (V (from, r1, mid)); Vs (V (mid, r2, to))] el convert_rules G next.
      Proof.
        intros EL.
        induction G; [auto | ].
        destruct EL as [ | EL]; subst.
        { clear IHg.
          apply in_or_app; left; simpl.
          set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
          unfold convert_nonterm_rule.
          set (vl := values_list).
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

    Section BackwardRuleInclusion.

      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: @dfa_rule DfaState Tt.

      Let projection (s: @symbol Tt (DfaState * var * DfaState)) : @symbol Tt Vt :=
        match s with
          | Vs (V (_, r, _)) => Vs r
          | Ts (T r) => Ts (T r)
        end.
      
      Lemma backward_rule_inclusion:
        forall A l, 
          R A l el convert_rules G next ->
          R (snd3 (unVar A)) (map projection l) el G.
      Proof. 
        intros.
        destruct A as [[[from r] to]]; simpl in *.
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
          subst; simpl; exact RIN.
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
        intros.
        apply backward_rule_inclusion in H; simpl in *.
        exact H.
      Qed.

    End BackwardRuleInclusion.

    Section RemainsInChomskyNormalForm.

      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: @dfa_rule DfaState Tt.
      
      Lemma remains_chomsky:
        chomsky (convert_rules G next).
      Proof.
        intros. 
        destruct H_G_in_chomsky_normal_form as [EF [UN [BIN UF]]].
        repeat split.
        { intros v rhs EL CONTR; subst rhs.
          destruct v as [[[from r] to]].
          apply backward_rule_inclusion in EL; simpl in *.
          apply EF in EL.
          auto. }
        { intros v rhs EL t TEL.
          destruct t as [t].
          unfold Separate.uniform in UN.
          destruct v as [[[from v] to]].
          apply backward_rule_inclusion in EL; simpl in *.
          apply UN with (a := T t) in EL.
          destruct rhs as [ | [[t'] | []]]; simpl in *.
          + inversion TEL.
          + inversion EL; apply map_eq_nil in H1.
            subst; auto.
          + inversion EL; apply map_eq_nil in H1.
            subst.
            destruct TEL as [TEL | TEL]; inversion TEL.
          + apply in_map_iff.
            exists (Ts (T t)); split; auto. }
        { intros v phs EL.
          destruct v as [[[from v] to]].
          apply backward_rule_inclusion in EL.
          apply BIN in EL.
          rewrite map_length in EL.
          auto. }
        { intros v CONTR.
          destruct v as [[[from r] to]].
          destruct CONTR as [[[[from' r'] to']] EL].
          apply backward_rule_inclusion in EL; simpl in *.
          unfold ElimU.unitfree in *.
          eapply UF.
          exists r'.
          eauto. }
      Qed.

    End RemainsInChomskyNormalForm.  
    
    Section MiddleLemmas.
      
      Variable G: @grammar Tt Vt.
      Variable next: @dfa_rule DfaState Tt.

      Lemma middle_lemma_nonterm:
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

        destruct rhs; simpl in *. contradiction.
        destruct s; simpl in *.
        { destruct rhs; [| inversion EL].
          unfold convert_terminal_rule in *.
          apply in_map_iff in EL; destruct EL as [st [EQ _]]; inversion EQ. }
        { destruct rhs; [inversion EL | ].
          destruct s; [ inversion EL | ].
          destruct rhs; [ | inversion EL].
          unfold convert_nonterm_rule in EL.
          unfold convert_nonterm_rule_1 in EL.
          unfold convert_nonterm_rule_2 in EL.
          apply in_flat_map in EL. destruct EL as [st1 [_ EL]].
          apply in_flat_map in EL; destruct EL as [st2 [_ EL]].
          apply in_map_iff in EL; destruct EL as [st3 [EQ _]].
          inversion EQ; subst; auto. }
      Qed.

      Lemma middle_lemma_term:
        forall from r to te,
          R (V (from, r, to)) [Ts te] el convert_rules G next ->
          next from te = to.
      Proof.
        intros r from to te EL.
        unfold convert_rules in EL.
        apply in_flat_map in EL.
        destruct EL as [rule [_ EL]].
        destruct rule as [v rhs].
        destruct rhs; simpl in *. contradiction.
        destruct s; simpl in *.
        { destruct rhs; [| inversion EL].
          unfold convert_terminal_rule in *.
          apply in_map_iff in EL; destruct EL as [st [EQ _]]; inversion EQ; auto. }
        { destruct rhs; [inversion EL | ].
          destruct s; [ inversion EL | ].
          destruct rhs; [ | inversion EL].
          unfold convert_nonterm_rule in EL.
          unfold convert_nonterm_rule_1 in EL.
          unfold convert_nonterm_rule_2 in EL.
          apply in_flat_map in EL. destruct EL as [st1 [_ EL]].
          apply in_flat_map in EL; destruct EL as [st2 [_ EL]].
          apply in_map_iff in EL; destruct EL as [st3 [EQ _]].
          inversion EQ; subst; auto. }
      Qed.
      
      Corollary middle_lemma_nonterm':
        forall r r1 r2,
          R (V r) [Vs (V r1); Vs (V r2)] el convert_rules G next ->
          fst3 r = fst3 r1 /\ thi3 r1 = fst3 r2 /\ thi3 r = thi3 r2.
      Proof.
        intros.
        destruct r as [[from r] to].
        destruct r1 as [[from1 r1] to1].
        destruct r2 as [[from2 r2] to2].
        simpl in *.
        eapply middle_lemma_nonterm; eauto.
      Qed.
      
      Corollary middle_lemma_term':
        forall (r : _) (te : ter),
          R (V r) [Ts te] el (convert_rules G next) ->
          next (fst3 r) te = thi3 r.
      Proof.
        intros r te H0.
        destruct r as [[from0 r0] to0].
        simpl in *.
        eapply middle_lemma_term; eauto.
      Qed.

      
    End MiddleLemmas.
    
    Section Main.
      
      Variable G: @grammar Tt Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.
      Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 
      
      Hypothesis F1: DfaState * @var Vt * DfaState -> Vt.
      Hypothesis F2: Vt -> DfaState * @var Vt * DfaState. 
      
      Section MainForward.

        Theorem der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar:
          forall (next: dfa_rule) (r: var) (from to: DfaState) (w: word),
            der G r (to_phrase w) ->
            final_state next from w = to ->
            der (convert_rules G next) (V (from, r, to)) (to_phrase w).
        Proof.
          intros next r from to w DER FIN.          
          rewrite <- (@lemma3 Tt Vt w) in FIN.
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
          (P :=
             fun r phr =>
               forall (next : dfa_rule) (from to : DfaState),
                 final_state next from (to_word phr) = to ->
                 der (convert_rules G next) (V (from, r, to)) (trans_phrase F2 phr)
          ) in DER; auto.
          { intros r0 t IN next from to FIN; simpl in *.
            apply rDer, forward_terminal_rule_inclusion; auto. }
          { intros r0 r1 r2 w1 w2 IN Ind1 Ind2 TER1 TER2 DER1 DER2 next from to FIN0.
            set (newG := convert_rules G next).
            set (m := final_state next from (to_word w1)).
            assert (H1: der newG (V (from, r1, m)) (trans_phrase F2 w1)); eauto.
            assert (H2: der newG (V (m, r2, to)) (trans_phrase F2 w2)).
            { apply Ind2, test0.
              rewrite <- lemma23; auto. }
            assert (in_H: In (R (V (from, r0, to)) [Vs (V(from, r1, m)); Vs (V (m, r2, to))]) newG).
            { apply forward_nonterminal_rule_inclusion; auto. }
            unfold trans_phrase; rewrite map_app.
            eapply derivability_step; eauto. }
        Qed.
        

        Theorem main_forward:
          forall (d : s_dfa) (v: var) (w : word),
            (s_dfa_language d) w /\ language G v (to_phrase w) ->
            (language (convert_grammar G d) (V (s_start d, v, s_final d)) (to_phrase w)).
        Proof.
          intros ? ? ? INT.
          destruct INT as [DFA [DER TER]].
          split; [apply der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar | ]; auto.
        Qed.
        
      End MainForward.
      
      Section MainBackward.
        
        Section SEction1.

          Variable next: @dfa_rule DfaState Tt.
          Variable from to: DfaState.
          
          Lemma der_in_triple_grammar_implies_dfa_accepts':
            forall (r : var) (w : word),           
              der (convert_rules G next) (V (from, r, to)) (to_phrase w) ->     
              final_state next (fst3 (from, r, to)) w = thi3 (from, r, to).
          Proof. 
            intros.
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
              eapply middle_lemma_term'.
              destruct r; eauto. }
            { clear H r from to. 
              intros r r1 r2 w1 w2 IN FIN1 FIN2 TER1 TER2 DER1 DER2.
              rewrite lemma23; auto.
              apply test0_1.
              
              destruct r as [[[fr r] to]].
              destruct r1 as [[[fr1 r1] to1]].
              destruct r2 as [[[fr2 r2] to2]].
              simpl in *.      
              
              assert (EQ:= @middle_lemma_nonterm' G next (fr, r, to) (fr1, r1, to1) (fr2, r2, to2) IN).
              destruct EQ as [EQ1 [EQ2 EQ3]]; simpl in *.
              subst fr to1 to2.
              rewrite EQ2, EQ3; reflexivity. }
          Qed.

          Lemma der_in_triple_grammar_implies_dfa_accepts:
            forall (r: var) (w: word),
              der (convert_rules G next) (V (from, r , to)) (to_phrase w) ->
              final_state next from w = to.
          Proof.
            intros w r DER. 
            set (rule := (from, r, to)) in *.
            assert (H1: from = fst3 rule); auto.
            assert (H2: to = thi3 rule); auto.
            rewrite H1, H2.
            eapply der_in_triple_grammar_implies_dfa_accepts'; eauto 1.
          Qed.

        End SEction1.

        Section Section2.
          
          Variable next: @dfa_rule DfaState Tt.
          
          Lemma der_in_triple_gr_implies_der_in_initial_gr':
            forall (r: var) (w: word),
              der (convert_rules G next) r (to_phrase w) ->
              der G (snd3 (unVar r)) (to_phrase w). 
          Proof.
            intros.
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
              unfold trans_phrase. rewrite map_app.
              apply @derivability_step with (r1 := r1) (r2 := r2) (T := Tt) (V := Vt); auto.
              apply backward_nonterminal_rule_inclusion in IN; auto. }
          Qed.
          
          Lemma der_in_triple_gr_implies_der_in_initial_gr:
            forall (s_start s_final: DfaState)
              (grammar_start : _) 
              (w : word),  
              der (convert_rules G next) (V (s_start, grammar_start, s_final)) (to_phrase w) ->
              der G grammar_start (to_phrase w).
          Proof.
            intros start final g_start w.
            set (s := (start, g_start, final)).
            assert (g_start = snd3 s); auto.
            rewrite H.
            eapply der_in_triple_gr_implies_der_in_initial_gr'.  
          Qed.  

        End Section2.
        
        Theorem main_backward:
          forall (d : s_dfa) (w : word) (v: var),
            language (convert_grammar G d) (V (s_start d, v, s_final d)) (to_phrase w) ->
            s_dfa_language d w /\ language G v (to_phrase w).
        Proof.
          intros ? ? ? TR.
          destruct TR as [DER TER]. 
          unfold convert_grammar in DER.
          destruct d; simpl in *.
          split.
          unfold s_dfa_language, s_accepts; simpl.
          eapply der_in_triple_grammar_implies_dfa_accepts; eauto 1.
          split.
          eapply der_in_triple_gr_implies_der_in_initial_gr; eauto 1.
          auto.
        Qed.

      End MainBackward. 
      
      Theorem main:
        forall (D : s_dfa) (v: var) (w : word),
          (language (convert_grammar G D) (V (s_start D, v, s_final D)) (to_phrase w)) <->
          s_dfa_language D w /\ language G v (to_phrase w).
      Proof.
        intros.
        split. 
        apply main_backward.
        apply main_forward. 
      Qed.
      
    End Main.

  End SomeSection.

  Section Main2.

    
    Context {T U: Type}.
    Hypothesis H_T_eq_dec: eq_dec T.
    Hypothesis H_V_eq_dec: eq_dec U.

    Variable n: nat.
    Hypothesis H_n_is_positive: n > 0.
    Let dfa_state := t n.
    

    Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 
    
    Variable TToNat: T -> nat.
    Variable UToNat: U -> nat.
    Variable NatToU: nat -> U.
    Hypothesis bijection: forall x : nat, UToNat (NatToU x) = x.
    Let normalize G := @normalize T U _ _ TToNat UToNat NatToU bijection G.

    (* Consider an arbitrary grammar without epsilon rules... *)
    Variable G: @grammar T U.
    Hypothesis H_G_eps_free: forall (A: @var U) (u: @phrase T U), Vs A el dom G -> u <> [].

    (* TODO?: ~~> dfa *)
    (* ... and deterministic finite automaton with exactly one final state. *)
    Variable SDFA: @s_dfa dfa_state T.
    
    
    (* We can transform G into an equivalent grammar in Chomsky normal form. *)
    Let normalized_G := normalize G.
    Goal  chomsky normalized_G.
    Proof. apply chomsky_normalform. Qed.
    Goal forall A w, Vs A el dom G -> language G A w <-> language normalized_G A w.
    Proof. intros; eapply language_normalform; eauto. Qed. 

    (* some comment *)
    Theorem final_theorem:
      forall (v: var) (w : word),
        Vs v el dom G -> 
        s_dfa_language SDFA w /\ language G v (to_phrase w) <->
        language (convert_grammar normalized_G SDFA) (V (s_start SDFA, v, s_final SDFA)) (to_phrase w).
    Proof.
      assert (x: t n).
      { clear SDFA dfa_state.
        destruct n.
        - apply Nat.nlt_0_r in H_n_is_positive; inversion H_n_is_positive.
        - apply F1. }
      intros v w EL; split; intros.
      { apply main_forward; auto.
        apply chomsky_normalform.
        destruct H as [DFA GR].
        split; [|eapply language_normalform in GR]; eauto. }
      { apply main_backward in H; auto.
        - destruct H as [DFA GR].
          split; [|eapply language_normalform]; eauto. 
          exact GR.
        - apply chomsky_normalform. }
    Qed.

  End Main2.

End Intersection.

