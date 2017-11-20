Require Export Inlining.

Module Separate.

  Import Base Lists Definitions Derivation Symbols (* Dec_Empty*) Inlining.
  
  Section Separate.

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
    
    Definition charfree u := forall s, s el u -> exists A, s = @Vs Tt Vt A.
    Definition uniform G := forall A u, R A u el G -> forall a, @Ts Tt Vt a el u -> u = [Ts a].

    Global Instance dec_charfree u : dec (charfree u).
    Proof.
      unfold charfree.
      induction u as [| [a | A] u IHu].
      - left. intros s H. destruct H.
      - right. intros H.
        assert (H0 : Ts a el (Ts a :: u)) by auto.
        destruct (H (Ts a) H0) as [A H']. inv H'.
      - destruct IHu as [IH | IH].
        + left. intros s [H | H] ; [ exists A |] ; auto.
        + right. intros H. apply IH.
          intros s H0. apply H. auto.
    Defined.

    Lemma pickChar u :
      ~ charfree u -> { a | Ts a el u}.
    Proof.
      intros H.
      induction u as [| [a | A] u IHu].
      - exfalso. apply H. intros s H0. destruct H0.
      - exists a. auto.
      - assert (H0 : ~ charfree u). {
          intros H0. apply H.
          intros s H1. destruct H1 as [H1 | H1] ; [exists A| ] ; auto. }
                                    destruct (IHu H0) as [a H1]. exists a. auto.
    Qed.

    Lemma pickCharRule G :
      { a | exists A u, R A u el G /\ (Ts a) el u /\ |u| >= 2} + uniform G.
    Proof.
      induction G as [| [A u] Gr IHGr].
      - right. intros A u [].
      - destruct IHGr as [[a IH] | IH].
        + left. exists a. destruct IH as [A' [u' [H0 [H1 H2]]]].
          exists A', u'. repeat split ; auto.
        + decide (charfree u) as [D | D].
          * right. intros A' u' [H0 | H0] a H1 ; eauto.
            inv H0. destruct (D (Ts a) H1) as [b T]. inv T.
          * { apply pickChar in D. destruct D as [a D].
              destruct u as [| [b | B] [| s u]].
              - exfalso. destruct D as [].
              - right. intros A' u' [H0 | H0] c H1 ; eauto.
                inv H0. destruct H1 as [H1 | H1] ; now inv H1.
              - left. exists a, A, (Ts b :: s :: u). repeat split ; simpl ; auto ; omega.
              - exfalso. destruct D as [D | D] ;  inv D.
              - left. exists a, A, (Vs B :: s :: u). repeat split ; simpl ; auto ; omega. }
    Qed.

    Definition step (G : @grammar Tt Vt) : @grammar Tt Vt.
      destruct (pickCharRule G) as [[a H] | H ].
      - destruct (@pickFresh Tt Vt TtToNat VtToNat NatToVt Id3 G) as [B N].
        exact (R B [Ts a] :: substG G (Ts a) [Vs B]).
      - exact G.
    Defined. 

    Fixpoint count_chars (u: @phrase Tt Vt) :=
      match u with
          [] => 0
        | Vs A :: ur => count_chars ur
        | Ts t :: ur => S (count_chars ur)
      end.

    Fixpoint count_sep G :=
      match G with
          [] => 0
        | R A u :: Gr => if decision (|u| < 2) then count_sep Gr
                        else count_chars u + count_sep Gr
      end.

    Definition sep G := it step (count_sep G) G.

    (** * Separation yields uniform grammar *)

    Lemma count_sep_split G G' :
      count_sep (G ++ G') = count_sep G + count_sep G'.
    Proof.
      induction G as [| [A u] Gr IHGr] ; simpl ; try decide (| u | < 2) ; auto.
      rewrite <- plus_assoc. now f_equal.
    Qed.

    Lemma count_chars_substL u a B :
      count_chars u >= count_chars (substL u (Ts a) [Vs B]).
    Proof.
      induction u as [| [b | A] u] ; simpl ; auto.
      decide (@Ts Tt Vt b = Ts a) ; simpl ; omega.
    Qed.

    Lemma count_sep_substL G a B :
      count_sep G >= count_sep (substG G (Ts a) [Vs B]).
    Proof.
      induction G as [| [A u] Gr IHGr] ; simpl ; auto.
      decide (| u | < 2) as [D | D] ; rewrite substL_length_unit with (x := Ts a) (x' := Vs B) (D := symbol_eq_dec) in D ;
      decide (| substL u (Ts a) [Vs B] | < 2) ; try tauto.
      cut (count_chars u >=  count_chars (substL u (Ts a) [Vs B])) ; try omega.
      apply count_chars_substL.
    Qed.

    Lemma count_chars_split u1 u2 :
      count_chars (u1 ++ u2) = count_chars u1 + count_chars u2.
    Proof.
      induction u1 as [| [a | A] u1] ; simpl ; auto.
    Qed.

    Lemma count_chars_decr B u a :
      Ts a el u -> count_chars u > count_chars (substL u (Ts a) [Vs B]).
    Proof.
      intros H0.
      apply in_split in H0.
      destruct H0 as [u1 [u2 H0]]. rewrite H0.
      replace (u1 ++ Ts a :: u2) with (u1 ++ [Ts a] ++ u2) by auto.
      repeat rewrite substL_split.
      repeat rewrite count_chars_split.
      repeat rewrite plus_assoc.
      cut (count_chars [Ts a] > count_chars (substL [Ts a] (Ts a) [Vs B])).
      - intros H2.
        pose (count_chars_substL u1 a B).
        pose (count_chars_substL u2 a B). omega.
      - simpl. decide (@Ts Tt Vt a = Ts a) ; try tauto. auto.
    Qed.

    Lemma count_sep_decr G A B u a :
      R A u el G -> Ts a el u -> |u| >= 2 -> count_sep G > count_sep (substG G (Ts a) [Vs B]).
    Proof.
      intros H U T.
      apply in_split in H.
      destruct H as [G1 [G2 H]]. rewrite H.
      replace (G1 ++ R A u :: G2) with (G1 ++ [R A u] ++ G2) by auto.
      do 2 rewrite substG_split.
      repeat rewrite count_sep_split.
      repeat rewrite plus_assoc.
      cut (count_sep [R A u] > count_sep (substG [R A u] (Ts a) [Vs B])).
      - intros C. pose (C0 := count_sep_substL G1 a B).
        pose (C1 := count_sep_substL G2 a B). omega.
      - simpl. decide (| u | < 2) as [D | D] ; try omega.
        rewrite substL_length_unit with (x := Ts a) (x' := Vs B) (D := symbol_eq_dec) in D.
        decide (| substL u (Ts a) [Vs B] | < 2) ; try tauto.
        do 2 rewrite <- plus_n_O.
        now apply count_chars_decr.
    Qed.

    Lemma count_decr G :
      step G <> G -> count_sep G > count_sep (step G).
    Proof.
      intros St.
      unfold step in *.
      destruct (pickCharRule G) as [[a [B [v [H0 [H1 H2]]]]] | H ] ; try tauto.
      destruct (pickFresh Id3 G) as [C N].
      simpl. eapply count_sep_decr ; eauto.
    Qed.

    Lemma fp_sep G :
      FP step (sep G).
    Proof.
      apply it_fp. intros n.
      decide (step (it step n G) = (it step n G)).
      - left. auto.
      - right. simpl. now apply count_decr in n0.
    Qed.

    Lemma fp_uniform G :
      FP step G -> uniform G.
    Proof.
      intros Ss.
      unfold step, FP in Ss.
      destruct (pickCharRule G) as [[a [B [v [H0 [H1 H2]]]]] | H ].
      - destruct (pickFresh Id3 G) as [C N].
        destruct G ; inversion Ss.
        exfalso. assert (H5 : Vs C el symbs (r :: G)) by (rewrite <- Ss ; simpl ; auto).
        specialize (N (Vs C) H5). unfold sless' in N. destruct B as [i] ; omega.      
      - intros A' u' Ru'. specialize (H A' u' Ru') ; auto.
    Qed.

    Lemma sep_uniform G :
      uniform (sep G).
    Proof.
      apply fp_uniform, fp_sep.
    Qed.

    (** * Separation preserves languages *)

    Lemma substG_der_equiv G A u B s :
      @fresh Tt Vt TtToNat VtToNat G (Vs B) -> A <> B -> s <> Vs B -> terminal u -> (der (R B [s] :: (substG G s [Vs B])) A u <-> der G A u).
    Proof.
      intros N Do U T.
      split ; intros D.
      - rewrite <- @substG_undo with
        (G := G) (B := B) (s := s) (Tt_eqdec := Tt_eqdec) (Vt_eqdec := Vt_eqdec)
                 (TtToNat := TtToNat) (VtToNat := VtToNat); auto.
        apply der_G_substG ; auto ; intros H.
        + rewrite substG_dom in H. apply symbs_dom in H.
          apply fresh_symbs in N. tauto.
        + destruct H ; tauto.
        + destruct (T (Vs B) H) as [t T']. inv T'.
      - rewrite <- @substG_undo with
        (G := G) (B := B) (s := s) (Tt_eqdec := Tt_eqdec) (Vt_eqdec := Vt_eqdec)
                 (TtToNat := TtToNat) (VtToNat := VtToNat) in D; auto.
        now apply der_substG_G.
    Qed. 

    Lemma step_der_equiv G A u :
      Vs A el dom G -> terminal u -> (der (step G) A u <-> der G A u).
    Proof.
      intros Do T. 
      unfold step.
      destruct (pickCharRule G) as [[a [B [v [H0 [H1 H2]]]]] | H ] ; [| firstorder].
      destruct (pickFresh _ G) as [C N].
      apply substG_der_equiv ; auto.
      - intros H. inv H. apply symbs_dom in Do.
        specialize (N (Vs C) Do). unfold sless' in N. omega.
      - intros H5. inv H5.
    Qed.

    Lemma step_dom G : 
      dom G <<= dom (step G).
    Proof.
      unfold step.
      destruct (pickCharRule G) as [[a [B [v [H0 [H1 H2]]]]] | H ] ; auto.
      destruct (pickFresh _ G) as [C N].
      simpl. rewrite substG_dom. auto.
    Qed.

    Lemma sep_der_equiv G A u :
      Vs A el dom G -> terminal u -> (der (sep G) A u <-> der G A u).
    Proof.
      unfold sep. remember (count_sep G) as n. clear Heqn.
      revert G.
      induction n ; intros G D T ; simpl ; try tauto.
      rewrite step_der_equiv ; auto.
      apply it_ind ; auto.
      intros G' H0. now apply step_dom.
    Qed.

    Lemma sep_language G A u :
      Vs A el dom G -> (language G A u <-> language (sep G) A u).
    Proof.
      intros D.
      split ; intros [L0 L1] ; split ; try eapply sep_der_equiv ; eauto.
    Qed.   

  End Separate.
  
End Separate.