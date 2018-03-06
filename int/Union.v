Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop fingraph finfun finset.

Require Import fl.cfg.Base fl.cfg.Definitions fl.cfg.Binarize fl.cfg.Chomsky.
Require Import fl.int.Base2 fl.int.DFA fl.int.ChomskyInduction.

Module Union.
  
  Import ListNotations Definitions Derivation Base Base2 ChomskyInduction.

  (** * Definitions *)
  (** In this section we define a function that creates a union-grammar out of a list of grammars. *)
  Section Definitions.
    
    Variables Tt Vt: Type.

    (* TODO: move? *)
    Definition grammar_to_language {Tt Vl : Type} (g : @var Vl * (@grammar Tt Vl)) : language :=
      let '(st, gr) := g in fun word => der gr st (to_phrase word).

    Inductive labeled_Vt : Type :=
    |  start : labeled_Vt
    |  lV : nat -> @var Vt -> labeled_Vt.

    Definition label_var (label: nat) (v: @var Vt): @var labeled_Vt :=
      V (lV label v).
    
    Definition label_symbol (label: nat) (s: @symbol Tt Vt): @symbol Tt labeled_Vt :=
      match s with
        | Ts t => Ts t
        | Vs v => Vs (V (lV label v))
      end.
    
    Definition label_phrase (label: nat) (p: @phrase Tt Vt): @phrase Tt labeled_Vt :=
      map (label_symbol label) p.
    
    Definition label_rule (label: nat) (r : @rule Tt Vt): @rule Tt labeled_Vt :=
      let '(R v p) := r in R (V (lV label v)) (label_phrase label p).
    
    Definition label_grammar (label: nat) (g: @grammar Tt Vt): @grammar Tt labeled_Vt:=
      map (label_rule label) g.
    
    Definition label_grammar_and_add_start_rule (label: nat) (g : @var Vt * (@grammar Tt Vt)):
      @grammar Tt labeled_Vt :=
      let '(st, gr) := g in (R (V start) [Vs (V (lV label st))]) :: label_grammar label gr.        
    
    Fixpoint label_list_of_grammars (grammars : seq (@var Vt * (@grammar Tt Vt))):
      @grammar Tt labeled_Vt :=
      match grammars with
        |  [] => []
        |  ((_,gr)::t) => label_grammar (length t) gr ++ (label_list_of_grammars t)
      end.

    Fixpoint grammar_union (grammars : seq (@var Vt * (@grammar Tt Vt))): @grammar Tt labeled_Vt :=
      match grammars with
        |  [] => []
        |  (g::t) => label_grammar_and_add_start_rule (length t) g ++ (grammar_union t)
      end.

  End Definitions.

  Section Lemmas.

    (** * Util *)
    (** In this section we prove a few useful facts about the union-related functions. *)        
    Section Util.
      
      Context {Tt Vt: Type}.
      
      Lemma word_remains_terminal:
        forall word,
          @terminal Tt Vt (to_phrase word).
      Proof.
        intros w.
        induction w.
        - intros s IN; inversion IN.
        - intros s IN.
          inversion IN; auto.
          subst s; exists a; auto.
      Qed.

      Lemma inner:
        forall (A: Type) (a: A) u v w,
          In a v \/ In a (u ++ w) <->
          In a (u ++ v ++ w).
      Proof.
        intros A a u v w; split; intros IN.
        { destruct IN as [IN|IN].
          { apply in_or_app; right.
              by apply in_or_app; left. }
          { apply in_app_or in IN.
              by destruct IN as [IN|IN]; auto. }
        }
        { apply in_app_or in IN.
          destruct IN as [IN|IN].
          { by right; apply in_or_app; auto. }
          { apply in_app_or in IN.
            destruct IN as [IN|IN].
            { by left. }
            { by right; apply in_or_app; auto. }
          }
        }
      Qed.

      Lemma app_label_phrase:
        forall (lphrase1 lphrase2: @phrase Tt (labeled_Vt Vt)) (label: nat) (phrase: @phrase Tt Vt),
          lphrase1 ++ lphrase2 = label_phrase label phrase ->
          exists phrase1 phrase2,
            phrase1 ++ phrase2 = phrase /\
            lphrase1 = label_phrase label phrase1 /\
            lphrase2 = label_phrase label phrase2.
      Proof.
        intros u v n p EQ.
        revert p EQ.  
        induction u; intros p EQ. 
        { by exists [], p; repeat split. }
        { destruct p; first by done.
          destruct a.
          { destruct s; last by done.
            injection EQ as EQ.
            destruct (IHu p H) as [u0 [v0 [H10 [H1 H2]]]]; clear IHu H.
            exists (Ts t :: u0), v0; repeat split; simpl.
            - by rewrite H10 EQ.
            - by rewrite H1.
            - by done.
          }
          { destruct s; first by done.
            destruct v0, v1.
            injection EQ as EQ.
            destruct (IHu p H) as [u1 [v1 [H10 [H1 H2]]]]; clear IHu H.
            exists ((Vs (V v0)) :: u1), v1; repeat split; simpl.
            - by rewrite H10.
            - by rewrite EQ H1.
            - by done. 
          }
        }
      Qed.
      
      Lemma label_phrase_for_word:
        forall (label: nat) (word: word),
          @to_phrase Tt (labeled_Vt Vt) word = label_phrase label (to_phrase word).
      Proof.
        intros.
        induction word0; first by done.
          by simpl; rewrite IHword0.
      Qed.
      
      Lemma label_symbol_is_injective:
        forall (label: nat) (s1 s2: @symbol Tt Vt),
          label_symbol label s1 = label_symbol label s2 ->
          s1 = s2.                                         
      Proof.
        intros n s1 s2 EQ.
        destruct s1, s2; simpl in *; try done.
        - by injection EQ as EQ; rewrite EQ.
          destruct v; destruct v0.
            by injection EQ as EQ; rewrite EQ.
      Qed.
     
      Lemma label_app:
        forall (label: nat) (p1 p2: @phrase Tt Vt),
          label_phrase label (p1 ++ p2) = label_phrase label p1 ++ label_phrase label p2.
      Proof.
        intros.
        induction p1; first by done.
        simpl; rewrite IHp1; reflexivity.
      Qed.
      
    End Util.

    (** * Forward *)
    (** In this section we prove that derivability in one grammar from the
        list implies derivability in the union-grammar. *)

    (* Let Tt Vt be types of terminals and nonterminals correspondingly. *)
    Variable Tt Vt: Type.

    (* For simplicity, let's define some local names. *)
    Let der := @der Tt.
    Let var := @var Vt.
    Let grammar := @grammar Tt Vt.
    
    Section Forward.

      Lemma grammar_extention:
        forall {V: Type} grammar1 grammar2 var (phrase: @phrase Tt V),
          der grammar2 var phrase ->
          der (grammar1 ++ grammar2) var phrase.
      Proof.
        intros V ? ? ? ? DER.
        induction DER.
        { by apply vDer. }
        { by apply rDer, in_or_app; right. }
        { by apply (replN (B := B)); [apply IHDER1 | apply IHDER2]. }
      Qed.

      Lemma der_in_grammar_implies_der_in_union_grammar_1:
        forall st grammar var grammars phrase,
          der grammar var phrase ->
          der (grammar_union ((st, grammar) :: grammars))
              (label_var (length grammars) var)
              (@label_phrase Tt Vt (length grammars) phrase). 
      Proof.
        intros ? G ? ? ? DER.
        induction DER.
        { by destruct A; apply vDer. }
        { apply rDer; right.
          apply in_or_app; left.
          induction G; first by  done.
          move: H => [H|H].
          { by left; rewrite H; destruct A. }
          { by right; eapply IHG. }
        }
        { rewrite label_app label_app.
          eapply replN; last first.
          { by apply IHDER2. }
          { have EQ: [Vs (label_var (length grammars) B)] = (@label_phrase Tt Vt (length grammars) [Vs B]); first by done.
            rewrite EQ.
            rewrite <- label_app.
            rewrite <- label_app.
              by apply IHDER1.
          }
        }
      Qed.

      Lemma der_in_grammar_implies_der_in_union_grammar_2:
        forall var grammar grammars word,
          grammar_to_language (var, grammar) word ->
          grammar_to_language (V (start Vt), grammar_union (Tt:=Tt) ((var, grammar) :: grammars)) word.
      Proof.
        intros st g gs word DER.
        unfold grammar_to_language; unfold grammar_to_language in DER.
        rewrite (label_phrase_for_word (length gs)).  
        rewrite -[label_phrase (Tt:=Tt) (Vt:=Vt) _ _]cats0 -[_ ++ []]cat0s.
        apply (replN (B := (V (lV (length gs) st)))).
        { by apply rDer; left. }
        { by apply der_in_grammar_implies_der_in_union_grammar_1. }
      Qed.

      (* Now we can use two lemmas above to get the proof.
         (1) We use induction by (list of) grammars.
         (2) "Base" case is trivial.
         (3) "Step" case splits into two subcases:
           a) Case where we can use der_in_grammar_implies_der_in_union_grammar_2 lemma
           b) Case where we can just use inductive hypothesis. *)      
      Lemma same_union_forward:
        forall (grammars: seq (var * grammar)) word,
          language_list_union (map grammar_to_language grammars) word ->
          grammar_to_language (V (start Vt), grammar_union grammars) word.
      Proof.
        intros grammars word UNION.
        induction grammars as [ |g gs]; first by done.
        destruct UNION as [DER | UNION].
        - destruct g as [st g].
            by apply der_in_grammar_implies_der_in_union_grammar_2.
        - by apply grammar_extention, IHgs.            
      Qed.

    End Forward.

    
    (** * Backward *)
    (** In this section we prove that derivability in the union-grammar implies 
        derivability in one of the grammar from the list. *)
    Section Backward.

      (* In this section we prove several obvious properties of the updated grammar. *)
      Section GeneralFacts.
        
        Variable grammars: seq (var * grammar).
        
        Lemma der_in_union_simpl_grammar_implies_der_in_union_grammar:
          forall var phrase,
            der (label_list_of_grammars grammars) var phrase ->
            der (grammar_union grammars) var phrase. 
        Proof.
          intros v p DER.
          unfold label_list_of_grammars in *.
          induction DER.
          { by intros; apply vDer. }
          { apply rDer.
            induction grammars; first by done.
            destruct a.
            apply in_app_or in H.
            destruct H as [H|H].
            { apply in_or_app; left.
                by right. }
            { apply in_or_app; right.
                by apply IHl0. } }
          { by intros; apply (replN (B := B)); [apply IHDER1 | apply IHDER2]. }
        Qed.              

        Lemma updated_derivation_doesnot_contain_start_symbol:
          forall label var phrase,
            der (grammar_union grammars) (V (lV label var)) phrase ->
            ~ In (Vs (V (start Vt))) phrase.
        Proof.
          intros n v ? H.
          remember (V (lV n v)) as st.
          revert n v Heqst.
          induction H.
          { intros ? ? EQ IN.
            rewrite EQ in IN.
              by destruct IN. }
          { intros ? ? Heqst IN.
            induction grammars; first by done.
            apply in_app_or in H.  
            destruct H; last by done.
            destruct a as [v0 g].
            destruct H as [H|H]; first by rewrite Heqst in H.
            induction g; first by done.
            destruct H; last by apply (IHg H).
            destruct a as [[v1] p].
            injection H as H.
            rewrite -H0 in IN; clear H0.
            induction p; first by done.
            destruct IN; last by done.
              by destruct a.
          }
          { intros n v0 ? ?. 
            apply inner in H1.
            destruct H1.
            - destruct B as [[]].
              + by eapply IHder1, inner; eauto.
              + by eapply IHder2. 
            - by eapply IHder1, inner; eauto.
          }
        Qed.   
        
        Lemma derivability_without_start_rules:
          forall var phrase,
            var <> V (start Vt) -> 
            der (grammar_union grammars) var phrase ->
            der (label_list_of_grammars grammars) var phrase.
        Proof.
          intros ? p NEQ DER.
          destruct var0 as [[ |n a]]; first by done.
          remember (V (lV n a)) as st. 
          revert n a NEQ Heqst. 
          induction DER.
          { by intros; apply vDer. }
          { intros.
            apply rDer.
            induction grammars; first by done.
            apply in_app_or in H.
            destruct H.
            { destruct a0; clear IHl0.
              apply in_or_app; left.
                by destruct H; [rewrite Heqst in H | ]. }
            { by destruct a0; apply in_or_app; right; apply IHl0. } } 
          { intros.
            apply (replN (B := B)).
            { by apply (IHDER1 n a NEQ Heqst). }
            { destruct B.
              destruct l; last by apply (IHDER2 n0 v0).
              exfalso.
              rewrite Heqst in DER1.
              eapply updated_derivation_doesnot_contain_start_symbol; eauto 2.
                by apply inner; eauto 2.
            }
          }
        Qed. 

        Lemma simpl_updated_derivation_doesnot_contain_start_symbol:
          forall label var phrase,
            der (label_list_of_grammars grammars) (V (lV label var)) phrase ->
            ~ In (Vs (V (start Vt))) phrase.
        Proof.
          intros ? ? ? DER IN.
          apply der_in_union_simpl_grammar_implies_der_in_union_grammar in DER.
            by eapply updated_derivation_doesnot_contain_start_symbol; eauto 2.
        Qed.
        
      End GeneralFacts.

      (* In this section we prove that the derivability of a word in some _labeled_ grammar
         implies that the word belongs to the union-language *)
      Section DerivabilityInUnionGrammar.
        
        Lemma start_nonterminal_is_not_derivable_in_labeled_grammar:
          forall grammar label1 label2 var word1 word2,
            ~ der (label_grammar label1 grammar)
              (V (lV label2 var)) (word1 ++ [Vs (V (start Vt))] ++ word2).
        Proof.
          have no_start_in_der_abdtract:
            forall G n0 v0 p,
              (forall lhs rhs, In (R lhs rhs) G -> ~ In (Vs (V (start Vt))) rhs) ->
              der G (V (lV n0 v0)) p ->
              ~ In (Vs (V (start Vt))) p.
          { intros ? ? ? ? no_start_rule ? ?.
            remember (V (lV n0 v0)) as st.
            revert n0 v0 Heqst.
            induction H.
            - intros.
              rewrite Heqst in H0.
              destruct H0.
              discriminate.
              contradiction.
            - intros.
              apply (no_start_rule A l H).
              exact H0.
            - intros.
              apply inner in H0.
              destruct H0.
              destruct B.
              destruct l.
              apply IHder1 with (n0:=n0) (v0:=v0).
              apply inner.
              auto.
              exact Heqst.
              apply IHder2 with (n0:=n) (v0:=v1).
              exact H0.
              reflexivity.
              apply IHder1 with (n0:=n0) (v0:=v0).
              apply inner.
              right.
              exact H0.
              exact Heqst.
          }
          intros G ? ? ? word1 word2 DER.
          eapply no_start_in_der_abdtract with (p := (word1 ++ [Vs (V (start Vt))] ++ word2)); eauto; last first.
          intros ? l IN1 IN2; clear DER.
          induction G; first by done.
          destruct IN1; last by eapply IHG; eauto 2.
          destruct a as [[v0] p].
          injection H as H1 H2.
          rewrite <- H2 in IN2.
          clear IHG H1 H2.
          induction p; first by done.
          destruct IN2; last by eapply IHp; eauto 2.
            by destruct a.
        Qed.             

        Lemma labels_in_derivation_are_consistent:
          forall (grammar: grammar) label var phrase,
            der (label_grammar label grammar) (V (lV label var)) phrase ->
            forall label' var', In (Vs (V (lV label' var'))) phrase -> label = label'.
        Proof.
          intros GS label v0.
          have der_n_is_n_abstract :
            forall (g0: Definitions.grammar)
              (p: phrase),
              der g0 (V (lV label v0)) p ->
              (forall n0 v0 n v l, In (R (V (lV n0 v0)) l) g0 -> In (Vs (V (lV n v))) l -> n = n0) ->
              (forall n0 v0 u w, ~ der g0 (V (lV n0 v0)) (u ++ [Vs (V (start Vt))] ++ w)) ->
              forall v n, In (Vs (V (lV n v))) p -> n = label.
          {
            intros g0 p H H_g0 H_st v n.
            remember (V (lV label v0)) as st.
            revert label v0 n v Heqst.
            induction H.
            { intros n0 v0 n v EQ IN.
              rewrite EQ in IN.
                by destruct IN as [IN | IN]; [inversion IN |  done]. 
            }
            { intros n0 v0 n v EQ IN.
              rewrite EQ in H; clear EQ.
                by eapply H_g0; eauto 2. 
            }
            { intros n0 v0 n v1 EQ IN.
              apply inner in IN.
              destruct IN.
              { destruct B.
                destruct l.
                { exfalso.
                  apply H_st with (n0 := n0) (v0 := v0) (u := u) (w := w).
                  rewrite -EQ.
                  exact H. 
                }
                {
                  assert (n = n1).
                  apply (IHder2 n1 v2 n v1).
                  reflexivity.
                  exact H1.
                  assert (n1 = n0).
                  apply (IHder1 n0 v0 n1 v2).
                  exact EQ.
                  apply inner.
                  auto.
                  rewrite <- H3.
                  exact H2.
                }
              }
              { apply (IHder1 n0 v0 n v1); first by done.
                  by apply inner; eauto. }
            }
          }
          intros p ? n v ?.
          apply Logic.eq_sym, der_n_is_n_abstract with (g0 := (label_grammar label GS)) (p := p) (v := v); try done.
          { intros.
            clear v H0 p H. 
            induction GS.
            contradiction.
            destruct H1.
            destruct a.
            destruct v0.
            injection H as H.
            rewrite <- H1 in H2.
            rewrite H in H2.
            clear H H1 IHGS.
            induction p.
            contradiction.
            destruct H2.
            destruct a.
            discriminate.
            destruct v3.
            injection H as H.
            auto.
            exact (IHp H).
            exact (IHGS H). }
          { intros ? ? ? ? ?.
            remember (V (lV n0 v1)) as A.
            rewrite HeqA in H1.
              by eapply start_nonterminal_is_not_derivable_in_labeled_grammar; eauto 2.
          }
        Qed.
        
        Lemma update_grammar_simpl_is_injective:
          forall (grammar: grammar) var label phrase,
            der (label_grammar label grammar) (V (lV label var)) (label_phrase label phrase) ->
            der grammar var phrase.
        Proof.
          intros grammar0 a n p ?.
          remember (label_phrase n p) as p0.
          remember (V (lV n a)) as A.
          revert a HeqA p Heqp0.
          induction H.
          { intros. 
            rewrite HeqA in Heqp0.
            destruct p.
            discriminate.
            destruct p.
            simpl in Heqp0.
            destruct s.
            discriminate.
            destruct v.
            simpl in Heqp0.
            injection Heqp0 as H.
            rewrite H.
            apply vDer.
            discriminate. }
          { intros.
            apply rDer.
            rewrite Heqp0 in H. simpl in *. 
            induction grammar0; first by done.
            destruct H.
            { left.
              destruct a0.
              rewrite HeqA in H.
              destruct v.
              simpl in H.
              injection H as H.
              rewrite H.
              clear A IHgrammar0 HeqA H.
              clear Heqp0.
              assert (p0 = p).
              revert p H0.
              induction p0.
              + intros.
                destruct p.
                reflexivity.
                discriminate.
              + intros.
                destruct p.
                discriminate.
                injection H0 as H.
                apply label_symbol_is_injective in H.
                rewrite H.
                assert (p0 = p).
                apply IHp0.
                apply H0.
                rewrite H1.
                reflexivity.
              + rewrite H.
                reflexivity.
            } 
            + right.
              apply IHgrammar0.
              exact H. }
          { intros.
            destruct B.
            destruct l.
            exfalso.
            eapply start_nonterminal_is_not_derivable_in_labeled_grammar. rewrite HeqA in H. eauto 2.
            apply app_label_phrase in Heqp0.
            destruct Heqp0 as [u1 H1].
            destruct H1 as [t0 H1].
            destruct H1.
            destruct H2.
            apply app_label_phrase in H3.
            destruct H3 as [v1 H3].
            destruct H3 as [w1 H3].
            destruct H3.
            destruct H4.
            rewrite <- H3 in H1.
            clear H3.
            rewrite <- H1.
            assert (n0 = n).
            { rewrite HeqA in H.
              apply Logic.eq_sym, (labels_in_derivation_are_consistent H) with (var' := v0).
              apply inner.
              auto.
            }
            apply (replN (B := v0)).
            apply IHder1.
            exact HeqA.
            unfold label_phrase.
            rewrite map_cat.
            unfold label_phrase in H2.
            rewrite <- H2.
            simpl.
            unfold label_phrase in H5.
            rewrite <- H5.
            rewrite H3.
            reflexivity.
            apply IHder2.
            rewrite H3; reflexivity.
            exact H4. }
        Qed.        
        
        Lemma derivability_in_grammar_implies_derivability_in_union_grammar:
          forall (grammars: seq (var * grammar)) grammar start label word,           
            In (start, grammar) grammars ->
            der (label_grammar label grammar) (V (lV label start)) (to_phrase word) ->
            language_list_union (map grammar_to_language grammars) word.
        Proof.
          intros.
          induction grammars; first by done. 
          destruct H; [left | right].
          { rewrite H; simpl.
            eapply update_grammar_simpl_is_injective with (var := start0) (label := label).
              by rewrite -label_phrase_for_word. }
          { by auto 2. }
        Qed.

      End DerivabilityInUnionGrammar.

      (* Suppose we have a phrase that we derived in a union-grammar.
         In this section we prove that there are only two options (1) either it is the 
         starting nonterminal, or (2) we can choose a grammar from the union-list in 
         which it is possible to derive this phrase. *)
      Section ChooseGrammarWithCorrectLabel.
        
        Lemma choose_labeled_grammar:
          forall (grammars: seq (var * grammar)) phrase,
            der (grammar_union grammars) (V (start Vt)) phrase ->
            phrase = [Vs (V (start Vt))] \/
            exists grammar var grammars1 grammars2,
              (grammars1 ++ (var, grammar) :: grammars2) = grammars /\
              der (grammar_union grammars) (V (lV (length grammars2) var)) phrase.
        Proof.
          intros ? p ?. 
          remember (V (start Vt)) as st in H.
          induction H.
          { by left; rewrite Heqst. }
          { right.
            induction grammars; first by done.
            apply in_app_or in H.
            destruct H; [clear IHgrammars | ].
            { destruct a as [v G].
              exists G, v, [], grammars; split; first by done.
              rewrite Heqst in H.
              destruct H.
              { injection H as H.
                rewrite <- H.
                  by apply vDer.
              }
              { exfalso.
                induction G; first by done.
                  by destruct H; first destruct a.
              }
            }
            {
              intros. have H1 := IHgrammars H.
              clear H IHgrammars.
              destruct H1 as [G [a1 [u1 [v1 H1]]]].
              exists G, a1, (a::u1), v1.
              destruct H1.
              split.
              rewrite <- app_comm_cons.
              apply f_equal with (f := fun l => a::l).
              auto.
              apply grammar_extention.
              auto.
            }
          }
          {
            assert (H1 := IHder1 Heqst).
            clear IHder1.
            destruct H1.
            assert (B = V (start Vt) /\ u = [] /\ w = []).
            {
              destruct u.
              simpl in H1.
              destruct w.
              injection H1 as H1.
              auto.
              discriminate.
              destruct u.
              discriminate.
              discriminate.
            }
            clear H1.
            destruct H2.
            destruct H2.
            rewrite H2.
            rewrite H3.
            simpl.
            assert ((v ++ [])%list = v).
            apply app_nil_r.
            rewrite H4.
            apply IHder2.
            exact H1.
            destruct H1 as [g H1].
            destruct H1 as [a H1].
            destruct H1 as [u0 H1].
            destruct H1 as [v0 H1].
            right.
            exists g, a, u0, v0.
            destruct H1.
            split.
            exact H1.
            apply (replN H2 H0).
          }
        Qed. 


      End ChooseGrammarWithCorrectLabel.
      
      (* In this section we prove that we can remove all grammars with "wrong" label. In other words, 
         if we have a labeled nonterminal, it is not possible to derive something with different 
         label. So, we can simply remove grammars with different labels. *)
      Section CutGrammars.

        Lemma labels_in_derivation_are_consistent_2:
          forall (grammars: seq (var * grammar)) label var phrase,
            der (label_list_of_grammars grammars) (V (lV label var)) phrase ->
            forall label' var', In (Vs (V (lV label' var'))) phrase -> label = label'.
        Proof.
          intros l n0 v0 p ? v n.
          unfold label_list_of_grammars in *.
          remember (V (lV n0 v0)) as st.
          revert n0 v0 n v Heqst.
          induction H.
          { intros; rewrite Heqst in H.
              by destruct H; [ injection H as H | ]. }
          { intros; rewrite Heqst in H; clear Heqst. 
            induction l; first by done.
            destruct a as [v1 G].
            apply in_app_or in H.
            destruct H; last by auto.
            induction G; first by done.
            destruct H; last by auto.
            destruct a.
            destruct v2.
            simpl in H.
            injection H as H.
            rewrite H in H2.
            rewrite <- H2 in H0.
            clear H IHG IHl H1 H2.
            induction p.
            contradiction.
            destruct H0.
            destruct a.
            discriminate.
            destruct v3.
            injection H as H.
            auto.
            auto. } 
          { intros n0 v0 v1 n ? ?. 
            apply inner in H1.
            destruct H1.
            destruct B.
            destruct l0.
            rewrite Heqst in H.
            eapply simpl_updated_derivation_doesnot_contain_start_symbol in H.
            exfalso.
            apply H.
            eapply inner; eauto 2.
            assert (n = n1).
            apply Logic.eq_sym, (IHder2 n1 v2 v1).
            reflexivity.
            exact H1.
            assert (n1 = n0).
            apply Logic.eq_sym, (IHder1 n0 v0 v2).
            exact Heqst.
            apply inner.
            auto.
            rewrite <- H3.
              by apply Logic.eq_sym. 
              apply (IHder1 n0 v0 v1).
              exact Heqst.
              apply inner.
              auto. }
        Qed.         

        
        Lemma cut_head:
          forall grammar grammars label (var: var) phrase, 
            length grammars <> label ->
            der (label_list_of_grammars (grammar::grammars)) (V (lV label var)) phrase ->
            der (label_list_of_grammars           grammars)  (V (lV label var)) phrase.
        Proof.
          intros a l n0 v0 p NEQ DER.
          remember (V (lV n0 v0)) as st.
          revert n0 v0 NEQ Heqst.
          induction DER.
          { intros.
            apply vDer.
          }
          { intros.
            destruct a.
            apply in_app_or in H.
            destruct H.
            exfalso.
            rewrite Heqst in H.
            clear Heqst.
            induction g.
            contradiction.
            destruct H.
            destruct a.
            destruct v1.
            injection H as H.
            auto.
            auto.
            apply rDer.
            exact H.
          }
          { intros.
            destruct B.
            destruct l0.
            + exfalso.
              rewrite Heqst in DER1.
              apply (simpl_updated_derivation_doesnot_contain_start_symbol DER1).  
              apply inner.
              auto.
            + apply (replN (B := (V (lV n v1)))).
              apply (IHDER1 n0 v0).
              exact NEQ.
              apply Heqst.
              apply (IHDER2 n v1).
              clear IHDER1 IHDER2.
              assert (n = n0).
              rewrite Heqst in DER1. 
              apply Logic.eq_sym, (labels_in_derivation_are_consistent_2 DER1) with (var' := v1) .
              apply inner.
              left.
              auto.
              rewrite H.
              exact NEQ.
              reflexivity.
          }
        Qed.



        Lemma label_is_bounded_by_grammar_union_length: 
          forall (grammars: seq (var * grammar)) label var phrase,
            length grammars <= label ->
            ~ In (R (V (lV label var)) phrase) (label_list_of_grammars grammars).
        Proof.
          intros ? n v l ? ?.
          unfold label_list_of_grammars in *.        
          induction grammars; first by done.
          destruct a as [v1 G].
          apply in_app_or in H0.
          destruct H0.
          - assert (length grammars < n).
            auto.
            clear H.
            destruct v1.
            induction G.
            contradiction.
            simpl in H0.
            destruct H0.
            + destruct a.
              destruct v1.
              simpl in H.
              injection H as H.
              rewrite H in H1.
                by rewrite ltnn in H1.
            + apply (IHG H).
          - apply IHgrammars.
            simpl in H. by apply ltnW.
            exact H0.
        Qed.
        
        Lemma cut_tail:
          forall (grammar: grammar) grammars label var v p,
            length grammars = label ->
            der (label_list_of_grammars ((var, grammar)::grammars)) (V (lV label v)) p ->
            der (label_grammar label grammar) (V (lV label v)) p.
        Proof.
          intros g r; intros. 
          remember (V (lV label v)) as st.
          revert label v H Heqst.
          induction H0.
          { by intros; apply vDer. }
          { intros.
            apply in_app_or in H.
            destruct H.
            rewrite <- H0.
            apply rDer. 
            exact H.
            exfalso.
            have H1 : length r <= label; first by rewrite H0.
            rewrite Heqst in H.
            apply (label_is_bounded_by_grammar_union_length H1 H).
          }
          { intros.
            destruct B.
            destruct l.
            exfalso.
            rewrite Heqst in H0_.
            apply (simpl_updated_derivation_doesnot_contain_start_symbol H0_).  
            apply inner.
            auto. 
            apply (replN (B := (V (lV n v1)))).
            apply (IHder1 label v0).
            exact H.
            exact Heqst.
            apply (IHder2 label v1).
            apply H.
            assert (n = label).
            rewrite Heqst in H0_.
            apply Logic.eq_sym, (labels_in_derivation_are_consistent_2 H0_ (var' :=v1)).
            apply inner.
            auto.
            rewrite H0.
            auto.
          }
        Qed.
        
        Lemma cut_grammar:
          forall (grammar: grammar) grammars1 grammars2 label var phrase, 
            length grammars2 = label ->
            der (label_list_of_grammars (grammars1 ++ [(var,grammar)] ++ grammars2)) (V (lV label var)) phrase ->
            der (label_grammar label grammar) (V (lV label var)) phrase.
        Proof.
          intros grammar0 ? ? ? ? ? ? ?.
          induction grammars1.
          { by rewrite cat0s cat1s in H0; apply cut_tail in H0. }
          { rewrite -cat1s in H0.
            rewrite -!catA in H0.
            rewrite cat1s in H0.
            apply cut_head in H0.
            apply IHgrammars1 in H0; first by done.
            rewrite -H !app_length; simpl.
            apply/eqP; rewrite neq_ltn; apply/orP; right.
              by rewrite -addn1 [X in _ <= X]addnC -addnA leq_add2l.
          }
        Qed.

      End CutGrammars.

      (* Now we can use all the lemmas above to get the proof. 
         (1) We use choose_labeled_grammar lemma to make step into the correct grammar of the union-grammar
         (2) Next, lemma derivability_without_start_rules which states that we can make drop all the 
              rules that lead from the starting nonterminal to the other grammars
         (3) Next, we can use the cut_grammar lemma to get rid of grammars with the wrong label
         (4) And finally, we apply derivability_in_grammar_implies_derivability_in_union_grammar lemma
              to "unlabel" the resulting grammar. *)
      Lemma same_union_backward:
        forall (grammars: seq (var * grammar)) word,
          grammar_to_language (V (start Vt), grammar_union grammars) word ->
          language_list_union (map grammar_to_language grammars) word.
      Proof.
        intros ? word DER.
        have H1 := choose_labeled_grammar DER. 
        destruct H1; first by exfalso; destruct word. 
        clear DER; move: H => [g [a [u [v [H H0]]]]].
        apply derivability_without_start_rules in H0; last by done.
        rewrite -H in H0; apply cut_grammar in H0; last by done.
        rewrite -H. 
        eapply derivability_in_grammar_implies_derivability_in_union_grammar with (label := (length v)); eauto 2.
          by rewrite -cat1s; apply in_or_app; right; apply in_or_app; left. 
      Qed.
      
    End Backward.

    (** * Main Theorem *)
    (** In this section we prove the equivalence in two formulations. *)
    Section MainTheorem1.

      Variable grammars: seq (var * grammar).
      
      Let l1 := language_list_union (map grammar_to_language grammars).
      Let l2 := grammar_to_language (V (start Vt), grammar_union grammars).

      Theorem correct_union_1:
        language_eq l1 l2.
      Proof.
        apply mk_laguage_eq.
        - apply same_union_forward.
        - apply same_union_backward.
      Qed.

    End MainTheorem1.

    Section MainTheorem2.

      Variable grammars: seq (var * grammar).
      
      Theorem correct_union_2:
        forall word, 
          Derivation.language (grammar_union grammars) (V (start Vt)) (to_phrase word) <->
          exists s_l, Derivation.language (snd s_l) (fst s_l) (to_phrase word) /\ In s_l grammars.
      Proof.
        intros.
        have Lem:
          forall ls w,
            language_list_union [seq grammar_to_language (Tt:=Tt) i | i <- ls] w <->
            exists s_g, In s_g ls /\ Derivation.language s_g.2 s_g.1 (to_phrase w).
        { intros T ls w; split; intros H.
          { induction ls; first by done.
            move: H => [DER|H].
            { exists a; split; first by left.
              destruct a; simpl in *.
                by split; last eapply word_remains_terminal. 
            }
            { apply IHls in H; clear IHls.
              move: H => [[s g] [EL [DER TER]]].
                by exists (s,g); split; [right | ].
            }
          }
          { move: H => [[s g] [EL [DER TER]]].
            apply in_split in EL.
            move: EL => [l1 [l2 EQ]].
            rewrite EQ; clear EQ.
              by induction l1; simpl in *; [left | right].
          } 
        }
        intros; split; intros.
        { move: H => [DER TER].
          move: (correct_union_1 grammars word0) => [_ SU].
          apply Lem in SU; last by done.
          move: SU => [s_g [EL LANG]].
            by exists s_g; split.
        }
        { move: H => [s_g [LANG EL]].
          move: (correct_union_1 grammars word0) => [SU1 _].
          have HH: language_list_union [seq grammar_to_language i | i <- grammars] word0.
          { by apply Lem; exists s_g; split. }
          apply SU1 in HH.
          split; first by done.
          move: LANG => [DER TER].
          induction word0; first by done.
            by apply word_remains_terminal.
        }
      Qed.      
      
    End MainTheorem2.

  End Lemmas.
   
End Union.