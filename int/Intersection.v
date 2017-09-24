Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop fingraph finfun finset.

Require Import fl.cfg.Base fl.cfg.Definitions fl.cfg.Dec_Empty fl.cfg.Binarize fl.cfg.Chomsky.
Require Import (* fl.int.Base2 *) (* INT.DFA*) fl.int.ChomskyInduction .
Require Import fl.aut.misc fl.aut.automata.


Module Intersection.

  Import ListNotations  Dec_Empty Base Symbols Misc
         ChomskyInduction Definitions Derivation Chomsky Automata.
  
  Variable char: finType.
  Definition word := seq.seq (@ter char).

  
  Section BigSection.


  
  Notation "x 'el' A" := (In x A) (at level 70).
    

  
  Section Util.

    Section Kek.
      
      Lemma ldl:
        forall (T: eqType) (x: T) A,
          In x A <-> x \in A.
      Proof.
        intros.
        induction A; first by split.
        split; intros.
        { move: H => [H | H].
          - by subst a; rewrite in_cons; apply/orP; left.
          - by rewrite in_cons; apply/orP; right; apply IHA.
        }
        { move: H; rewrite in_cons; move => /orP [/eqP H | H].
          - by subst.
          - by right; apply IHA.
        }
      Qed.

    End Kek.

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
        
        Context { V: Type}.

        Fixpoint to_phrase (w: word ): @phrase _ V :=
          match w with
            | s::sx => Ts s :: (to_phrase sx)
            | _ => []
          end.
        
        Fixpoint to_word (p: @phrase char V): list ter :=
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

      Context { V: Type}.

      Variable w1 w2: @phrase char V.

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
        assert(EL: In (Vs v) (Vs v :: w)); auto.
        destruct  (H _ EL).
        inversion H1.
      Qed.
      
    End Terminal.

    
  End Util.

    Section CanonicalStructureTer.
      
      Section EqTer.
        
        Variable T: eqType.
        
        Fixpoint eqter (t1 t2: @ter T) :=
          match t1, t2 with
            | Definitions.T x1, Definitions.T x2 => x1 == x2
          end.
        
        Lemma eqterP: Equality.axiom eqter.
        Proof.
          move => t1 t2; apply: (iffP idP) => [| <-]; last by elim: t1 => //= t ->.
          intros; destruct t1, t2.
            by inversion H as [H']; move: H' => /eqP H'; subst.
        Defined. 

        Global Definition ter_eqMixin := EqMixin eqterP.
        Canonical ter_eqType := Eval hnf in EqType ter ter_eqMixin.

      End EqTer. 
      
      Section ChoiceTypeTer.

        Variable T: choiceType.
        
        Definition to_ter (x: T) := Definitions.T x.
        Definition from_ter t: T := match t with Definitions.T x => x end.
        
        Lemma hz_of_terK : cancel from_ter to_ter.
        Proof.
            by intros t; destruct t.
        Qed.
        
        Global Definition ter_choiceMixin := CanChoiceMixin hz_of_terK.
        Canonical ter_choiceType := Eval hnf in ChoiceType ter ter_choiceMixin.

      End ChoiceTypeTer.

      Section CountTypeTer.

        Variable T: countType.
        
        Global Definition ter_countMixin := CanCountMixin (@hz_of_terK T).
        Canonical ter_countType := Eval hnf in CountType ter ter_countMixin.
        
      End CountTypeTer.

      Section FinTypeTer.
        
        Variable T: finType.
        
        Definition ter_enum := map (@Definitions.T _) (Finite.enum T).
        
        Lemma ter_enumP: Finite.axiom ter_enum.
        Proof.
          intros x; destruct x as [t].
            by rewrite //= count_map enumP.
        Qed.
        
        Global Definition ter_finMixin := FinMixin ter_enumP.
        Canonical ter_finType := Eval hnf in FinType ter ter_finMixin.
        
      End FinTypeTer.

    End CanonicalStructureTer.


    Definition dfa_with_single_final_state {T: finType} (dfa: @dfa T) final :=  dfa_fin dfa = pred1 final.
    Definition dfa_with_single_final_state_2 {T: finType} (dfa: @dfa T) :=  exists final, dfa_fin dfa = pred1 final.

(*    
    Lemma fkfk:
      forall (T: finType) (dfa: dfa T),
        exists sdfas, 
          forall w, ( dfa_lang dfa w <-> has (fun sdfa => dfa_lang sdfa w) sdfas).
    Proof.
      intros T dfa.
      have DState := dfa_state dfa.
      have DStart := dfa_s dfa.
      have DFinPr := dfa_fin dfa.
      have DRule := dfa_step dfa.

      have F := bigop.index_enum DState.
      unfold pred in DFinPr.
      have L := filter (DFinPr) ([::DStart]). 
      
      dfa.
      
    Admitted.
*)
    

    Variable dfa: dfa [finType of (@ter char)].

    Variable fin: dfa_state dfa.


    Let lel := bigop.index_enum (dfa_state dfa).

    Let ffc := filter (dfa_fin dfa) lel.

    Let lst:seq (Automata.dfa [finType of ter]) :=
      map (fun fin_state =>
             {| dfa_s := (dfa_s dfa);
                dfa_fin := pred1 fin_state;
                dfa_step := dfa_step dfa |}) ffc.

    Definition dfa_to_list_sdfa (T: finType) (dfa: Automata.dfa T): seq (Automata.dfa T) :=
      let final_states := filter (dfa_fin dfa) (bigop.index_enum (dfa_state dfa)) in
      map (fun fin_state =>
             {| dfa_s := (dfa_s dfa);
                dfa_fin := pred1 fin_state;
                dfa_step := dfa_step dfa |}) final_states.

      
(*    Lemma fkfk:
      forall (h : seq.seq _)
             (w0 : seq [finType of (@ter char)]),
        (dfa_lang dfa w <-> exists sdfa, (sdfa \in h) /\ (dfa_lang sdfa w)).
     Proof.
      intros w; split; intros H.
      simpl in H; unfold dfa_lang in H.

      
    Admitted.
*)

    
  Section SomeSection.
    
    (* TODO: comment *)
    Variable Tt Vt: Type.


        
    Section Conversion.


      Variable dfa1: Automata.dfa [finType of (@ter char)].
      Let dfa_state := Automata.dfa_state dfa1.
      Let dfa_rule := @dfa_step [finType of @ter char] dfa1.

      Let fff := bigop.index_enum dfa_state.
      
      
      
      Let TripleRule := @rule ( char) (dfa_state * @var Vt * dfa_state).
      
      Section ToTriple.

        Definition convert_nonterm_rule_2 (r r1 r2: _) (s1 s2 : _): seq.seq TripleRule :=
          map (fun s3 => R (V (s1, r, s3)) [Vs (V (s1, r1, s2)); Vs (V (s2, r2, s3))]) (fff).

        Definition convert_nonterm_rule_1  (r r1 r2: _) (s1 : _) :=
          flat_map (convert_nonterm_rule_2 r r1 r2 s1) fff.

        Definition convert_nonterm_rule (r r1 r2: _) :=
          flat_map (convert_nonterm_rule_1 r r1 r2) fff.

        Definition convert_terminal_rule (next: _) (r: _) (t: _): list TripleRule :=
          map (fun s1 => R (V (s1, r, next s1 t)) [Ts t]) fff.

        Definition convert_rule (next: _) r :=
          match r with
            | R r [Vs r1; Vs r2] => convert_nonterm_rule r r1 r2
            | R r [Ts t] => convert_terminal_rule next r t 
            | _  => []
          end.

      End ToTriple.

      Definition convert_rules (rules: list rule) (next: _): list rule :=
        flat_map (convert_rule next) rules.
      

      Definition convert_grammar (g: @grammar char Vt): @grammar char (dfa_state * @var Vt * dfa_state):=
        convert_rules g (dfa_rule).


    End Conversion.

    
    Let dfa_state := dfa_state dfa.
    Let dfa_rule: dfa -> [finType of @ter char] -> dfa := @dfa_step [finType of @ter char] dfa.
    (* Let dfa_final := dfa_fin dfa.*)
    

    Hint Resolve lemma2.


    Section ForwardTerminalRuleInclusion.
      
      Variable G: @grammar char Vt. 
      
      Lemma forward_terminal_rule_inclusion:
        forall (r: var) (te: ter) (next: _) (from to: dfa_state),
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
          split; [reflexivity | apply ldl; rewrite mem_index_enum //].

        - simpl.
          apply in_or_app; right.
          auto.
      Qed.

    End ForwardTerminalRuleInclusion.
    
    Section ForwardNonterminalRuleInclusion.

      Variable G: @grammar char Vt.
      Variable next: dfa -> [finType of @ter char] -> dfa.

      Variable from mid to: dfa_state.
      Variable r r1 r2: @var Vt.
      
      Lemma forward_nonterminal_rule_inclusion'':
        R  (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
           convert_nonterm_rule_2 r r1 r2 from mid.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_2.
        assert (H2: to el (index_enum dfa)).
        apply ldl. by rewrite mem_index_enum. 

        induction (index_enum dfa).
        simpl in H2.
        contradiction.
        simpl.  
        simpl in H2.
        destruct H2.
        left.
        rewrite H.
        auto.
        right.
        apply IHl. 
        exact H.
      Qed.

      Lemma forward_nonterminal_rule_inclusion':
        @R _ _ (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))] el 
           convert_nonterm_rule_1 r r1 r2 from.
      Proof.
        set (rule := (R (V (from, r, to)) [Vs (V(from, r1, mid)); Vs (V (mid, r2, to))])).
        unfold convert_nonterm_rule_1.
        assert (H2: mid el (index_enum dfa)).
        apply ldl. by rewrite mem_index_enum. 
        induction (index_enum dfa).
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
        apply IHl.
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
          
          assert (EL: from el (index_enum dfa)).
          
          apply ldl. by rewrite mem_index_enum.
          
          apply in_flat_map.
          exists from.
          split; [exact EL | apply forward_nonterminal_rule_inclusion']. }  
        { apply in_app_iff; right.
          apply IHg.
          exact EL. }
      Qed.

    End ForwardNonterminalRuleInclusion. 

    Section BackwardRuleInclusion.

      Variable G: @grammar char Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: dfa -> [finType of @ter char] -> dfa.

      Let projection (s: @symbol char (dfa_state * var * dfa_state)) : @symbol char Vt :=
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

      Variable G: @grammar char Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.

      Variable next: dfa -> [finType of @ter char] -> dfa.
      
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
      
      Variable G: @grammar char Vt.
      Variable next: dfa -> [finType of @ter char] -> dfa. 

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

      
      Variable G: @grammar char Vt.
      Hypothesis H_G_in_chomsky_normal_form: chomsky G.
      Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 
      
      Hypothesis F1: dfa_state * @var Vt * dfa_state -> Vt.
      Hypothesis F2: Vt -> dfa_state * @var Vt * dfa_state. 

      Theorem test0:
        forall (w1 w2: word)
               (from to: dfa_state),
          dfa_final dfa from (w1 ++ w2) = to ->
          dfa_final dfa (dfa_final dfa from w1) w2 = to.
      Proof.
        intros w1 w2.
        induction w1; eauto.
      Qed.
      
      Theorem test0_1:
        forall (w1 w2 : word)
               (from to: _),
          dfa_final dfa (dfa_final dfa from w1) w2 = to ->
          dfa_final dfa from (w1 ++ w2) = to.
      Proof.
        intros w1 w2.
        induction w1; simpl; eauto.
      Qed.

    
      Section MainForward.

        Theorem der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar:
          forall (* next: dfa -> [finType of @ter char] -> dfa *) (r: var) (from to: dfa_state) (w: word),
            der G r (to_phrase w) ->
            dfa_final dfa from w = to ->
            der (convert_rules G dfa_rule) (V (from, r, to)) (to_phrase w).
        Proof.
          intros r from to w DER FIN.          
          rewrite <- (@lemma3 Vt w) in FIN.
          set (wp1 := to_phrase (V:= _ * @var Vt * _) w) in *.
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
          
          apply chomsky_derivability_induction with 
          (P :=
             fun r phr =>
               forall (from to : dfa_state),
                 dfa_final dfa from (to_word phr) = to ->
                 der (convert_rules G dfa_rule) (V (from, r, to)) (trans_phrase F2 phr)
          ) in DER; auto.
          { intros r0 t IN from to FIN; simpl in *.
            apply rDer, forward_terminal_rule_inclusion; auto. }
          { intros r0 r1 r2 w1 w2 IN Ind1 Ind2 TER1 TER2 DER1 DER2 from to FIN0.
            set (newG := convert_rules G dfa_rule).
            set (m := dfa_final dfa from (to_word w1)).
            assert (H1: der newG (V (from, r1, m)) (trans_phrase F2 w1)); eauto.
            assert (H2: der newG (V (m, r2, to)) (trans_phrase F2 w2)).
            { apply Ind2, test0.
              rewrite <- lemma23; auto. }
            assert (in_H: In (R (V (from, r0, to)) [Vs (V(from, r1, m)); Vs (V (m, r2, to))]) newG).
            { apply forward_nonterminal_rule_inclusion; auto. }
            unfold trans_phrase.
            rewrite map_cat.
            eapply derivability_step; eauto. }
        Qed.


        
        Let st := @dfa_s _ dfa.

        Print dfa_s.
        Print st.

        Variable f: dfa_state.
        Hypothesis H: (dfa_fin dfa) = pred1 f.


        Theorem main_forward:
          forall (v: var) (w : word),
            (dfa_lang dfa) w /\ language G v (to_phrase w) ->
            (language (convert_grammar dfa G) (V (st, v, f)) (to_phrase w)).
        Proof.
          intros ? w INT.
          destruct INT as [DFA [DER TER]].
          split; [apply der_in_initial_grammar_and_dfa_implies_der_in_triple_grammar | ]; auto.
          unfold dfa_lang in DFA.
          simpl in DFA.
          
          apply dfa_final_accept in DFA.
          rewrite H in DFA.
          simpl in DFA.
          by apply/eqP.
        Qed.
        
      End MainForward.
      
      Section MainBackward.
        
        Section SEction1.

          Variable from to: dfa_state.
          
          Lemma der_in_triple_grammar_implies_dfa_accepts':
            forall (r : var) (w : word),           
              der (convert_rules G dfa_rule) (V (from, r, to)) (to_phrase w) ->     
              dfa_final dfa (fst3 (from, r, to)) w = thi3 (from, r, to).
          Proof.
            intros.
            assert (EQ: w = to_word (to_phrase (V:= dfa_state * @var Vt * dfa_state) w)).
            { clear.
              induction w; simpl.
              - reflexivity.
              - rewrite <- IHw; reflexivity.
            } rewrite EQ; clear EQ.
            
            assert (P1: fst3 (from, r, to) = fst3 (unVar (V (from, r, to)))). simpl; reflexivity.
            assert (P2: thi3 (from, r, to) = thi3 (unVar (V (from, r, to)))). simpl; reflexivity.
            rewrite P1; rewrite P2; clear P1 P2.
            
            apply chomsky_derivability_induction
            with (w0 := to_phrase w) (r0 := V (from, r, to)) (G0 := convert_rules G dfa_rule); auto; simpl.
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
              
              assert (EQ:= @middle_lemma_nonterm' G dfa_rule (fr, r, to) (fr1, r1, to1) (fr2, r2, to2) IN).
              destruct EQ as [EQ1 [EQ2 EQ3]]; simpl in *.
              subst fr to1 to2.
              rewrite EQ2 EQ3; reflexivity. }
          Qed.
          
          Lemma der_in_triple_grammar_implies_dfa_accepts:
            forall (r: var) (w: word),
              der (convert_rules G dfa_rule) (V (from, r , to)) (to_phrase w) ->
              dfa_final dfa from w = to.
          Proof.
            intros w r DER. 
            set (rule := (from, r, to)) in *.
            assert (H1: from = fst3 rule); auto.
            assert (H2: to = thi3 rule); auto.
            rewrite H1 H2.
            eapply der_in_triple_grammar_implies_dfa_accepts'; eauto 1.
          Qed.

        End SEction1.

        Section Section2.
          
          Lemma der_in_triple_gr_implies_der_in_initial_gr':
            forall (r: var) (w: word),
              der (convert_rules G dfa_rule) r (to_phrase w) ->
              der G (snd3 (unVar r)) (to_phrase w). 
          Proof.
            intros r w.
            assert (EQ: trans_phrase F1 (to_phrase w) = to_phrase w).
            { clear.
              induction w; first by done. 
              - by simpl; rewrite IHw. }
            rewrite <- EQ.
            intros CN.

            have HHH:= @chomsky_derivability_induction _ _ (convert_rules G dfa_rule)
                                                       (fun r w => der G (snd3 (unVar r)) (trans_phrase F1 w)) _ _ _ _ r (to_phrase w).
            apply HHH.
            (*            apply chomsky_derivability_induction with (G0 := convert_rules G dfa_rule) (r0 := r) (w0 := to_phrase w); auto. *)
            
            
            { apply remains_chomsky; auto. }
            { by done. }
            { intros r' t IN.
              destruct r' as [[[from r'] to]]; simpl in *.
              apply rDer; apply backward_terminal_rule_inclusion in IN; auto. }
            { intros r' r1 r2 w1 w2 IN DER1 DER2 TER1 TER2 DER3 DER4.
              destruct r' as [[[from r'] to]].
              destruct r1 as [[[from1 r1] to1]].
              destruct r2 as [[[from2 r2] to2]]; simpl in *.

              have KEK: (trans_phrase F1 (w1 ++ w2)%list) =
                        (trans_phrase F1 (w1)%list) ++ (trans_phrase F1 (w2)%list).
              { clear. by induction w1; simpl; last rewrite IHw1. }
              rewrite KEK.
              apply @derivability_step with (r1 := r1) (r2 := r2); auto.
              apply backward_nonterminal_rule_inclusion in IN; auto. }
            { by done. }
            { by done. }
          Qed.

          Lemma der_in_triple_gr_implies_der_in_initial_gr:
            forall (s_start s_final: dfa_state)
              (grammar_start : _) 
              (w : word),  
              der (convert_rules G dfa_rule) (V (s_start, grammar_start, s_final)) (to_phrase w) ->
              der G grammar_start (to_phrase w).
          Proof.
            intros start final g_start w.
            set (s := (start, g_start, final)).
            assert (g_start = snd3 s); auto.
            rewrite H.
            eapply der_in_triple_gr_implies_der_in_initial_gr'.  
          Qed.  

        End Section2.

        Let st := @dfa_s _ dfa.

        Print dfa_s.
        Print st.

        Variable f: dfa_state.
        Hypothesis H: @dfa_with_single_final_state _ dfa f. 
        

        Theorem main_backward:
          forall (w : word) (v: var),
            language (convert_grammar dfa G) (V (st, v, f)) (to_phrase w) ->
            dfa_lang dfa w /\ language G v (to_phrase w).
        Proof.
          
          intros w ? TR.
          destruct TR as [DER TER]. 
          unfold convert_grammar in DER.
          simpl in *.
          split.
          apply dfa_final_accept.
          rewrite H.
          simpl. apply/eqP.

          eapply der_in_triple_grammar_implies_dfa_accepts; eauto 1.
          split.
          eapply der_in_triple_gr_implies_der_in_initial_gr; eauto 1.
          auto.
        Qed.

      End MainBackward. 

(*      
      Theorem main:
        forall (v: var) (w : word),
          (language (convert_grammar G D) (V (dfa_s dfa, v, s_final D)) (to_phrase w)) <->
          s_dfa_language D w /\ language G v (to_phrase w).
      Proof.
        intros.
        split. 
        apply main_backward.
        apply main_forward. 
      Qed.
*)      
    End Main.

  End SomeSection.

  Section Main2.

(*    
    Context {U: Type}.
    Hypothesis H_T_eq_dec: eq_dec char.
    Hypothesis H_V_eq_dec: eq_dec U. 

    Hypothesis H_nonempty: #| dfa_state | >0.
    
    Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 
    
    Variable TToNat: char -> nat.
    Variable UToNat: U -> nat.
    Variable NatToU: nat -> U.
    Hypothesis bijection: forall x : nat, UToNat (NatToU x) = x.
    Let normalize G := @normalize char U _ _ TToNat UToNat NatToU bijection G. 

    (* TODO: ... *)
    (* Consider an arbitrary grammar  *)
    Variable G: @grammar char U.

    Variable S: @var U.
    Hypothesis H_name: Vs S el dom G.


(*     Lemma fkfk2:
       forall w,
         (language G S (to_phrase w) /\ dfa_lang dfa w) <->
         exists sdfa, dfa_lang sdfa w /\ language G S (to_phrase w) /\ (sdfa \in lst) . 
    Proof.
      intros w; split; intros H.
      simpl in H; unfold dfa_lang in H.
      
    Admitted.
*)
    
    Hypothesis Hss: @dfa_with_single_final_state _ dfa fin.
    
    (* Variable dfa: dfa f. [finType of (@ter char)]. *)
    
    (* TODO?: ~~> dfa *)
    (* ... and deterministic finite automaton with exactly one final state. *)
    (* Variable SDFA: dfa dfa_state T. *)
    
    
    (* We can transform G into an equivalent grammar in Chomsky normal form. *)
    Let normalized_G := normalize G.
    Goal  chomsky normalized_G.
    Proof. apply chomsky_normalform. Qed.
    Goal forall w, w <> [] -> language G S w <-> language normalized_G S w.
    Proof. intros; eapply language_normalform; eauto. Qed. 

    Search _ (finType).
    (* some comment *)
    Theorem final_theorem:
      forall (w : word),
        w <> [] ->
        dfa_lang dfa w /\ language G S (to_phrase w) <->
        language (convert_grammar normalized_G) (V (dfa_s dfa, S, fin)) (to_phrase w).
    Proof.
      intros w NE; split; intros H.
      
(*      assert (x: t n).
      { clear SDFA dfa_state.
        destruct n.
        - apply Nat.nlt_0_r in H_n_is_positive; inversion H_n_is_positive.
        - apply F1. }  *)
      
      { apply main_forward; auto.
        apply chomsky_normalform.
        move: H_nonempty => /card_gt0P St.
        destruct H as [DFA GR].
        split; [|eapply language_normalform in GR]; eauto.
        admit.
      }
      { apply main_backward in H; auto.
        - destruct H as [DFA GR].
          split; [|eapply language_normalform]; eauto.
        - admit.
        - exact GR.
        - apply chomsky_normalform.
        - intros. 
          admit.
      } 
    Admitted.
 *)
    
  End Main2.
  
  End BigSection.

  Section Mod.
  
  Section Main3.


    
    
    Variable dfa: dfa [finType of (@ter char)].
    Variable fin: dfa_state dfa.
    Let dfa_state := dfa_state dfa.

    
    Context {U: Type}.
    Hypothesis H_T_eq_dec: eq_dec char.
    Hypothesis H_V_eq_dec: eq_dec U. 

    Hypothesis H_nonempty: #|dfa_state| > 0.
    
    Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 
    
    Variable TToNat: char -> nat.
    Variable UToNat: U -> nat.
    Variable NatToU: nat -> U.
    Hypothesis bijection: forall x : nat, UToNat (NatToU x) = x.
    Let normalize G := @normalize char U _ _ TToNat UToNat NatToU bijection G. 

    (* TODO: ... *)
    (* Consider an arbitrary grammar  *)
    Variable G: @grammar char U.

    Variable S: @var U.
    Hypothesis H_name: Vs S el dom G.

    Print to_phrase .
    Print word.

    Variable dfa1: Automata.dfa [finType of (@ter char)] .
    Variable dfa2: Automata.dfa [finType of (@ter char)] .
    Variable dfa3: Automata.dfa [finType of (@ter char)] .


(*    Let lst := [@convert_grammar dfa1 U G; @convert_grammar dfa2 U G].
*)
    
(*
    Let fudcn G lst:  seq (@grammar char (dfa_state * @var U * dfa_state)):=
      map (fun (sdfa: Automata.dfa [finType of (@ter char)] ) =>
             (@convert_grammar sdfa U G): @grammar char (dfa_state * @var U * dfa_state)) lst.
  *)  
    Lemma edd:
      exists (Int: @grammar char (dfa_state * @var U * dfa_state)) St,
        forall (w: _),
          dfa_lang dfa w /\ language G S (to_phrase w) <->
          language Int St (to_phrase w).
    Proof.
      intros.

      have EG: forall w, ~ language [] (V (dfa_s dfa, S, fin)) (to_phrase w).
      { admit. }

      
      have Lem : dec (exists u, language G S u).
      admit.
 
      move: Lem => [D|N]; last first.
      { have C: forall u, ~ language G S u.
        { by intros u L; apply N; exists u. }
        exists [::], (V (dfa_s dfa, S, fin)).
        intros w; split; intros H.
        { move: H => [ _ H].
            by apply C in H. }
        { by exfalso; apply EG in H. }
      }

      have Alt: forall n, n == 0 \/ n > 0.
      { by move => n; case n; [left|right]. }
      move: (Alt (#|dfa_fin (dfa_connected dfa)|)) => [E | NE].
      { move: E => /dfa_lang_empty_correct E.
        exists [::], (V (dfa_s dfa, S, fin)).
        intros w; split; intros H.
        { move: H => [H _].
          move: (E w); clear E; rewrite !inE; move => E.
          move: H; rewrite inE; move => H.
            by rewrite E in H.
        } 
        { by exfalso; apply EG in H. }        
      }

      
      
      
      (* Выводится ли тут пустой символ? *)

      
      
      set (NG := normalize G).
      set (TR := convert_grammar dfa NG).
      (* set (SDFAS := @dfa_to_list_sdfa [finType of ter] TR). 
      
      exists TGS.


      
      
      unfold TGS.
      
      unfold TGS.
      exists G. *)
    Admitted.
      

  End Main3.

  End Mod.
End Intersection.

