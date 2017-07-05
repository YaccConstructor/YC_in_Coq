Require Export Derivation.

Definition item := prod symbol phrase.
Definition items G u : list item := product pair (symbs G) (segms u).

(** * Computation of item list *)

Section Dec_Word.
  Variable G : grammar.
  Variable u : phrase.

  Definition step (M : list item) i :=
    match i with
      (s, v) => v = [s] \/ match s with
                           Vs A => exists M', M' <<= M /\ R A (fsts M') el G /\ v = concat (snds M')
                         | _ => False
                         end
    end.

  (** ** Decidability of step *)
  Fixpoint fsts_comb X Y (D : eq_dec X) (M : list (X * Y)) (v : list X) : (list (list (X * Y))) :=
    match v with
      [] => [ [] ]
    | s :: v =>
      let
        M' := fsts_comb D M v
      in let
        S := filter (fun e => match e with (s', _) => s = s' end) M
      in
      product (fun s M => s :: M) S M'
    end.
  Arguments fsts_comb {X} {Y} {D} M v.
  
  Lemma fsts_comb_corr1 X Y (D : eq_dec X) (M : list (X * Y)) (v : list X) (l : list (X * Y)) :
    l el fsts_comb M v -> fsts l = v /\ l <<= M.
  Proof.
    revert l.
    induction v as [| s v IHv] ; intros l H ; simpl in *.
    - destruct H ; try tauto.
      rewrite <- H. split ; simpl ; auto.
    - apply prod_corr in H.
      destruct H as [[s' x] [M' [H0 [H1 H2]]]].
      apply in_filter_iff in H1.
      destruct H1 as [H1 H3] ; subst.
      destruct (IHv M' H2) as [H4 H5] ; subst.
      split ; auto.
  Qed.

  Lemma fsts_comb_corr2 X Y (D : eq_dec X) (M : list (X * Y)) (v : list X) (l : list (X * Y)) :
    fsts l = v /\ l <<= M -> l el fsts_comb M v.    
  Proof.
    revert l.
    induction v as [| s v IHv] ; intros l [H0 H1] ; simpl in *.
    - destruct l as [|[s x]] ; auto. inv H0.
    - apply prod_corr.
      destruct l as [|[s' x]] ; simpl in H0 ; inv H0.
      assert (H0 : fsts l = fsts l /\ l <<= M) by firstorder.
      specialize (IHv l H0).
      exists (s, x), l. repeat split ; auto.
      apply in_filter_iff. split ; auto.
  Qed.

  Lemma fsts_comb_corr X Y (D : eq_dec X) (M : list (X * Y)) (v : list X) (l : list (X * Y)) :
    l el fsts_comb M v <-> fsts l = v /\ l <<= M.
  Proof.
    split ; [apply fsts_comb_corr1 | apply fsts_comb_corr2].
  Qed.     

  Instance step_dec' (M : list item) A v :
    dec (exists M', M' <<= M /\ R A (fsts M') el G /\ v = concat (snds M')).
  Proof.
    induction G as [| [B w] Gr IHGr].
    - right. intros [M' [_ [[] _]]].
    - destruct IHGr as [IHG | IHG].
      + left. destruct IHG as [M' [H0 [H1 H2]]].
        exists M'. repeat split ; auto.
      + decide (A = B) as [D | D] ; subst.
        * decide (exists M', M' el (fsts_comb M w) /\ v = concat (snds M')) as [D0 | D0].
          { left. destruct D0 as [M' [H0 H1]].
            exists M'. apply fsts_comb_corr in H0.
            destruct H0 as [H0 H2]. rewrite H0. repeat split ; auto. }
          { right. intros [M' [H0 [H1 H2]]].
            destruct H1.
            - inv H. apply D0.
              exists M'. split ; auto.
              apply fsts_comb_corr. auto.
            - apply IHG. exists M'. split ; auto. }
        * right. intros [M' [H0 [H1 H2]]].
          apply IHG. destruct H1 as [H1 | H1] ; try (inv H1 ; tauto).
          exists M'. repeat split ; auto.
  Defined.

  Instance step_dec M i : dec (step M i).
  Proof.
    destruct i as (s, x).
    simpl. decide (x = [s]) ; try now (left ; auto).
    destruct s ; auto.
  Defined.
  
  Definition DW := FCI.C (step := step) (items G u).

  Lemma items_refl s v :
    s el symbs G -> (s, v) el items G v.
  Proof.
    intros H.
    apply prod_corr.
    exists s, v. repeat split ; auto.
    apply segms_corr, segment_refl. auto.
  Qed.

  (** ** only-if-part *)
  Lemma derf_DW v w :
    (forall s, s el v -> s el symbs G) -> segment u w -> derf G v w -> exists M, v = fsts M
                                                                   /\ w = concat (snds M)
                                                                   /\ M <<= DW.
  Proof.
    intros U Sg.
    induction 1 as [v | A v w' H0 H IHv | s v w' u0 H IH0 H0 IH1].
    - induction v as [| s v IHv].
      + exists []. repeat split ; simpl ; auto.
      + assert (U' : forall s : symbol, s el v -> s el symbs G) by auto.
        assert (Sg' : segment u v). {
          apply segment_trans with (ys := s :: v) ; auto.
          exists [s], []. simpl. now rewrite app_nil_r. }
        destruct (IHv U' Sg') as [M [H0 [H1 H2]]].
        exists ((s, [s]) :: M). repeat split ; simpl ; rewrite H0, H1 in * ; auto.
        intros s0 [H3 | H3].
        * inv H3. apply FCI.closure ; [| now left].
          apply prod_corr. exists s, [s]. repeat split ; auto.
          apply segms_corr. apply segment_trans with (ys := (s :: concat (snds M))) ; auto.
          exists [], (concat (snds M)). auto.
        * now apply H2.
    - exists [(Vs A, w')].
      repeat split ; simpl ; try now rewrite app_nil_r.
      intros s [H1 | H1] ; [ | destruct H1].
      subst. apply FCI.closure.
      + apply prod_corr. exists (Vs A), w'. repeat split ; auto. now apply segms_corr.
      + assert (U' : forall s, s el v -> s el symbs G). {
          intros s E. apply symbs_inv. exists A, v. split ; auto. }
        destruct (IHv U' Sg) as [M [H3 [H4 H5]]].
        right. exists M. repeat split ; rewrite H3 in * ; auto.
    - assert (U' : forall s0 : symbol, s0 el [s] -> s0 el symbs G) by (intros s0 E ; inv E ; now apply U).
      assert (U'' : forall s0 : symbol, s0 el v -> s0 el symbs G) by auto.
      assert (Sg' : segment u w'). {
        apply segment_trans with (ys := w' ++ u0) ; auto.
        exists [], u0. auto. }
      assert (Sg'' : segment u u0). {
        apply segment_trans with (ys := w' ++ u0) ; auto.
        exists w', []. now rewrite app_nil_r. }
      destruct (IH0 U' Sg') as [Ms [Hs0 [Hs1 Hs2]]].
      destruct (IH1 U'' Sg'') as [Mu [Hu0 [Hu1 Hu2]]].
      exists (Ms ++ Mu). repeat split ; auto.
      + now rewrite fsts_split, <- Hs0, Hu0.
      + now rewrite snds_split, concat_split, <- Hu1, <- Hs1.
Qed.

  (** ** if-part *)
  
  Lemma DW_derf' :
    inclp DW (fun i => match i with (s, v) => derf G [s] v end).
  Proof.
    apply FCI.ind.
    intros M [[a | A] v] IH X S ; simpl in S ; destruct S ; try tauto ; try (rewrite H ; constructor).
    destruct H as [M' [H0 [H1 H2]]].
    econstructor 2 ; eauto.
    unfold inclp in IH.
    clear H1 X. revert H2. revert v.
    induction M' as [| [s x] Mr IHM] ; intros v H2 ; rewrite H2 ; simpl in * ; eauto.
    constructor 3 ; firstorder.
    assert (H3 : (s, x) el M) by auto.
    specialize (IH (s, x) H3). auto.
  Qed.
  
  Lemma DW_der_equiv' s v :
    s el symbs G -> ((s,v) el DW <-> derf G [s] v /\ segment u v).
  Proof.
    intros Ss. split ; intros H.
    - dupapply H DW_derf' H'.
      split ; auto.
      pose (H0 :=FCI.incl H).
      apply prod_corr in H0.
      destruct H0 as [? [? [H0 [H1 H2]]]] ; inv H0.
      now apply segms_corr in H2.
    - destruct H as [H0 H1].
      assert (H2 : forall s', s' el [s] -> s' el symbs G) by (intros s' [H2 | []] ; subst ; auto).
      destruct (derf_DW H2 H1 H0) as [M [D0 [D1 D2]]].
      apply D2. subst.
      assert (H3 : M = [(s, concat (snds M))]). {
        destruct M as [| (s', v') M].
        - inv D0.
        - simpl in D0. destruct M as [| (s'', v'') M] ; inv D0.
          simpl. now rewrite app_nil_r. }
      rewrite H3. simpl. rewrite app_nil_r. auto.
  Qed.
         
  Lemma DW_der_equiv A :
    Vs A el symbs G -> (der G A u <-> (Vs A, u) el DW).
  Proof.
    intros Ss. rewrite <- derf_der_equiv.
    split ; intros H ; apply DW_der_equiv' ; try split ; auto using segment_refl.
  Qed.

End Dec_Word.

(** * Decidability of word problem *)

Instance der_dec G A u : dec (der G A u).
Proof.
  decide (Vs A el symbs G).
  - decide ((Vs A, u) el DW G u) as [D | D].
    +  left. now apply DW_der_equiv.
    + right. intros H. apply D. apply DW_der_equiv ; auto.
  - decide (u = [Vs A]) as [D | D].
    + left. rewrite D. constructor.
    + right. intros H0. apply D. eapply symbs_der ; eauto.
Defined.

Instance lang_dec G A u : dec (language G A u).
Proof.
  auto.
Qed.