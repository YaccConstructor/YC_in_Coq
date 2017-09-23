Require Export Separate.

Module Binarize.

  Import Base Definitions Symbols Derivation Inlining.

  Section Binarize.

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
    
    Fixpoint step G G' :=
      match G' with
          [] => []
        | R A [] :: Gr => R A [] :: step G Gr
        | R A [s0] :: Gr => R A [s0] :: step G Gr
        | R A [s0 ; s1] :: Gr => R A [s0 ; s1] :: step G Gr
        | R A (s0 :: ur) :: Gr =>
          let (B, H) := @pickFresh _ _ TtToNat VtToNat NatToVt Id3 G
          in R A [s0 ; Vs B] :: @R Tt Vt B ur :: Gr
      end.

    Definition step' G := step G G.

    Fixpoint count_bin (G: @grammar Tt Vt) :=
      match G with
          [] => 0
        | R A u :: Gr => if decision ((|u|) <= 2) then count_bin Gr else |u| + count_bin Gr
      end. 

    Definition bin G := it step' (count_bin G) G. 

    Definition binary G := forall A u, @R Tt Vt A u el G -> (|u|) <= 2.

    (** * Binarization yields binary gramar *)

    Lemma count_decr G G' :
      step G' G <> G -> count_bin G > count_bin (step G' G).
    Proof.
      intros H.
      induction G as [| [A u] G IHG] ; simpl in * ; [tauto | ].
      destruct u as [| s0 [| s1 [| s2 u]]] ; try now (simpl ; apply IHG ; intros H0 ; apply H ; f_equal).
      simpl.  decide (S (S (| u |)) <= 2) as [D | D] ; omega.
    Qed.

    Lemma fp_bin G :
      FP step' (bin G).
    Proof.
      apply it_fp. intros n.
      remember (it step' n G) as G'.
      decide (step' G' = G') as [D | D].
      - left. auto.
      - right. simpl. rewrite <- HeqG'.
        apply count_decr in D. unfold step'. omega.
    Qed.

    Lemma fp_binary G :
      FP step' G -> binary G.
    Proof.
      intros Ss A u Ru.
      unfold FP, step' in Ss.
      remember G as G'.
      do 2 rewrite HeqG' in Ss at 2.
      rewrite HeqG' in Ru. clear HeqG'.
      induction G as [| [B v] Gr IHGr] ; simpl in * ; [tauto |].
      destruct Ru as [Ru | Ru].
      - inv Ru. destruct u as [| s0 [| s1 [| s2 u]]] ; simpl ; auto. inv Ss.
      - destruct v as [| s0 [| s1 [| s2 v]]] ; try now (simpl in Ss ; inversion Ss ; apply IHGr ; auto).
    Qed.

    Lemma bin_binary G :
      binary (bin G).
    Proof.
      apply fp_binary, fp_bin.
    Qed.

    (** * Binarization preserves languages *)

    Lemma step_or G G' :
      step G' G = G \/ exists A Gr B u s, G === R A (s :: u) :: Gr /\ step G' G === R A [s ; Vs B] :: R B u :: Gr /\ ~ Vs B el symbs G'.
    Proof.
      induction G as [| [A u] G IHG].
      - simpl. now left.
      - destruct u as [| s0 [| s1 [| s2 u]]] ; unfold step.
        + destruct IHG as [H | [A' [Gr [B' [u' [s [H0 [H1 H2]]]]]]]] ; try now (left ; f_equal).
          right. exists A', (R A [] :: Gr), B', u', s. repeat split ; try rewrite H0 ; auto using Base.equi_swap ; rewrite H1 ; auto 7 using Base.equi_swap.
        + simpl ; destruct IHG as [H | [A' [Gr [B' [u' [s [H0 [H1 H2]]]]]]]] ; try now (left ; f_equal).
          right. exists A', (R A [s0] :: Gr), B', u', s. repeat split ; try rewrite H0 ; auto using Base.equi_swap ; rewrite H1 ; auto 7 using Base.equi_swap.
        + simpl ; destruct IHG as [H | [A' [Gr [B' [u' [s [H0 [H1 H2]]]]]]]] ; try now (left ; f_equal).
          right. exists A', (R A [s0 ; s1] :: Gr), B', u', s. repeat split ; try rewrite H0 ; auto using Base.equi_swap ; rewrite H1 ; auto 7 using Base.equi_swap.
        + destruct (@pickFresh _ _ _ _ _ _ G') as [B N].
          right. exists A, G, B, (s1 :: s2 :: u), s0. repeat split ; auto.
          intros H. specialize (N (Vs B) H). unfold sless' in N. omega.
    Qed. 
    
    Lemma step_der_equiv G A u :
      terminal u -> (Vs A) el dom G -> (der G A u <-> der (step G G) A u).
    Proof.
      intros T Do.
      destruct (step_or G G) as [Ss | Ss].
      - rewrite <- Ss at 1. split ; auto.
      - destruct Ss as [A' [Gr [B [v [s [H0 [H1 H2]]]]]]].
        assert (RL : substG (R A' [s; Vs B] :: Gr) (Vs B) v = R A' (s :: v) :: Gr). {
          simpl. decide (s = Vs B).
          + exfalso. rewrite e in H0.
            apply H2. apply symbs_inv. exists A', (Vs B :: v). rewrite H0. split ; auto.
          + decide (@Vs Tt Vt B = Vs B) ; try tauto. rewrite app_nil_r. f_equal.
            apply substG_skip. intros H. apply H2.
            apply symbs_subset with (G0 := Gr) ; auto. rewrite H0. auto. }
                                                                                    rewrite der_equiv_G with (G1 := step G G) (G2 := R B v :: R A' [s; Vs B] :: Gr) by (rewrite Base.equi_swap ; auto).
        rewrite der_equiv_G with (G2 := R A' (s :: v) :: Gr) ; auto.
        rewrite <- RL. symmetry. eapply der_substG_G_equiv; eauto.
        + intros H. apply symbs_dom in Do. inv H. eauto.
        + simpl. intros [H | H].
          { inv H. apply H2. apply symbs_inv. exists B, (s :: v). rewrite H0. split ; auto. }
          { apply symbs_dom in H. apply H2.
            apply symbs_subset with (G0 := Gr) ; auto. rewrite H0. auto. }
        + intros H. apply H2. apply symbs_inv. exists A', (s :: v). rewrite H0. split ; auto.
        + intros H. destruct (T (Vs B) H) as [t T']. inv T'.
    Qed. 
    

    Lemma step_dom G G' :
      dom G <<= dom (step G' G).
    Proof.
      revert G'.
      induction G as [| [A u] G IHG] ; intros G' ; try destruct u as [| s0 [| s1 [| s2 u]]] ; simpl ; auto.
    Qed.


    Lemma bin_der_equiv G A u :
      terminal u -> (Vs A) el dom G -> (der G A u <-> der (bin G) A u).
    Proof.
      unfold bin. remember (count_bin G) as n. clear Heqn.  
      intros T. revert G.
      induction n as [| n IHn] ; intros G Do ; simpl.
      - split ; auto.
      - rewrite (IHn G Do).
        apply step_der_equiv ; auto.
        apply it_ind ; auto.
        intros r H0. now apply step_dom.
    Qed.

    Lemma bin_language G A u :
      Vs A el dom G -> (language G A u <-> language (bin G) A u).
    Proof.
      intros D.
      split ; intros [L0 L1] ; split ; auto ; [rewrite <- bin_der_equiv | rewrite bin_der_equiv] ; auto.
    Qed.
    
  End Binarize.
  
End Binarize.