Require Export Basics Separate Binarize ElimE ElimU.
Local Open Scope program_scope.

Module Chomsky.

  Import Base Lists Definitions Symbols Derivation ElimE Separate Binarize ElimU Inlining.
  
  Section Chomsky.

    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.
    
    Context {TtToNat: Tt -> nat}.
    Context {VtToNat: Vt -> nat}.
    Context {NatToTt: nat -> Tt }.
    Context {NatToVt: nat -> Vt}. 

    Hypothesis Id1: forall x, TtToNat (NatToTt x) = x.
    Hypothesis Id2: forall x, NatToTt (TtToNat x) = x.
    Hypothesis Id3: forall x, VtToNat (NatToVt x) = x.
    Hypothesis Id4: forall x, NatToVt (VtToNat x) = x.

    
    Definition chomsky (G: @grammar Tt Vt) := efree G /\ uniform G /\ binary G /\ unitfree G.
    Definition normalize :=
      elimU
        ∘ elimE
        ∘ (@sep Tt Vt _ _ TtToNat VtToNat NatToVt Id3)
        ∘ (@bin Tt Vt     TtToNat VtToNat NatToVt Id3). 


    (** * Normalization yields Chomsky normal form *)

    Lemma substG_preservesLength (G: @grammar Tt Vt) s s' :
      binary G -> binary (substG G s [s']).
    Proof.
      intros H. induction G as [| [A u] G IHG] ; simpl ; auto.
      intros B v [E | E].
      - inv E. rewrite <- substL_length_unit ; eauto.
      - eapply IHG ; eauto.
        intros B' v' E'. eapply H ; eauto.
    Qed.

    (** ** Preservation of binarity *)

    Lemma binary_sep (G: @grammar Tt Vt) :
      binary G -> binary (@sep Tt Vt _ _ TtToNat _ _ Id3 G).
    Proof.
      intros H.
      unfold sep.
      apply it_ind ; auto.
      intros G' Bi.
      unfold Separate.step.
      destruct (pickCharRule G') as [[a [B [v [H0 [H1 H2]]]]] | H0 ] ; auto.
      destruct (pickFresh _ G') as [C N].
      cut (binary (substG G' (Ts a) [Vs C])) ; auto using substG_preservesLength.
      intros Bin A u E. destruct E ; [inv H3 | ] ; eauto.
    Qed.

    Lemma binary_elimE (G: @grammar Tt Vt) : binary G -> binary (elimE G).
    Proof.
      intros H A u H0. 
      assert (TMP:= @delE_rules Tt Vt _ _ (eclosure G) A u).
      apply TMP in H0; clear TMP.
      assert (TMP:= @closure_slist Tt Vt ).
      apply TMP in H0.
      destruct H0 as [u' [H0 H1]].
      apply slist_length in H1.
      specialize (H A u' H0). omega.
    Qed. 

    Lemma binary_unit (G: @grammar Tt Vt) : binary G -> binary (elimU G).
    Proof.
      intros H A u H0.
      apply rule_ranG, ran_elimU_G, ranG_rule in H0.
      destruct H0 as [B H0].
      apply (H B u H0).
    Qed.

    (** ** Preservation of uniformness *)

    Lemma excluded_free (G: @grammar Tt Vt) : uniform G -> uniform (elimE G).
    Proof.
      intros H A u H0 a E.
      assert (TMP:= @delE_rules Tt Vt _ _ (eclosure G) A u).
      apply TMP in H0; clear TMP.
      assert (TMP:= @closure_slist Tt Vt ).
      apply TMP in H0.
      destruct H0 as [u' [H1 H2]].
      assert (H4 : Ts a el u') by (apply slist_subsumes in H2 ; auto).
      specialize (H A u' H1 a H4).
      subst. inv H2.
      - inv H6. destruct E.
      - now inv H3.
    Qed. 

    Lemma excluded_unit (G: @grammar Tt Vt) : uniform G -> uniform (elimU G).
    Proof.
      intros H A u Ru.
      apply rule_ranG, ran_elimU_G, ranG_rule in Ru.
      destruct Ru as [B H0].
      apply (H B u H0).
    Qed.  

    (** ** Preservation of epsilon-freeness *)

    Lemma efree_unit (G: @grammar Tt Vt) : efree G -> efree (elimU G).
    Proof.
      intros H A u Ru.
      apply rule_ranG, ran_elimU_G, ranG_rule in Ru.
      destruct Ru as [B H0].
      apply (H B u H0).
    Qed.

    Lemma chomsky_normalform (G: @grammar Tt Vt) :
      chomsky (normalize G).
    Proof.
      repeat split.
      - apply efree_unit, efree_elimE.
      - apply excluded_unit, excluded_free, sep_uniform.
      - apply binary_unit, binary_elimE, binary_sep, bin_binary.
      - apply unitfree_elimU.
    Qed. 

    (** * Normalization preserves languages *)

    Lemma bin_dom (G: @grammar Tt Vt):
      dom G <<= dom (@bin Tt Vt TtToNat _ _ Id3 G).
    Proof.
      unfold bin.
      apply it_ind ; auto.
      intros G' H.
      setoid_transitivity (dom G') ; auto.
      apply Binarize.step_dom.
   Qed. 

    Lemma language_normalform G A u :
      Vs A el dom G -> u <> [] -> (language G A u <-> language (normalize G) A u).
    Proof.
      intros Do U.
      unfold normalize.
      rewrite @bin_language with (NatToVt := NatToVt) (Id3 := Id3); auto.
      rewrite @sep_language; eauto; try now apply bin_dom.
      rewrite elimE_language ; auto.
      rewrite unit_language.
      unfold compose; split; eauto.
    Qed. 

  End Chomsky.

End Chomsky.

