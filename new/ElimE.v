Require Export Dec_Word.

(** * Nullable Variables *)
Inductive nullable (G : grammar) (s : symbol) : Prop :=
| Null A u : s = Vs A -> R A u el G -> (forall s', s' el u -> nullable G s') -> nullable G s.
Hint Constructors nullable.

Lemma derE_nullable (G : grammar) (A : var) (u : phrase) :
  der G A u -> (forall s, s el u -> nullable G s) -> nullable G (Vs A).
Proof with (apply U, in_or_app ; (try now left) ; (right ; apply in_or_app ; (try now left) ; try now right)).
  intros H U.
  induction H as [| u H | A B u w v H IH0 H0 IH1] ; eauto.
  apply IH0.
  intros s E.
  apply in_app_or in E.
  destruct E as [E | E].
  + auto...
  + destruct E as [E | E].
    * rewrite <- E. apply IH1. intros s' V. auto... 
    * apply in_app_or in E. destruct E as [E | E] ; firstorder. auto...
Qed.

Lemma nullable_derE (G : grammar) (s : symbol) :
  nullable G s -> exists A, s = Vs A /\ der G A [].
Proof.
  induction 1 as [s A u H H0 H1 IH].
  exists A. split ; auto.
  clear H H1 s.
  apply rDer in H0.
  induction u as [|s u IHu] ; auto.
  apply IHu ; auto.
  assert (H3: s el s::u) by auto.
  destruct (IH s H3) as [B [H4 H5]]. rewrite H4 in *.
  replace u with ([] ++ [] ++ u) ; eauto.
Qed.

Lemma nullable_derE_equi (G : grammar) (s : symbol) :
  (exists A, s = Vs A /\ der G A []) <-> nullable G s.
Proof.
  split ; intro H.
  - destruct H as [A [H0 H1]].
    rewrite H0 in *.
    eapply derE_nullable ; eauto. firstorder.
  - now dupapply H nullable_derE H0.
Qed.

Instance nullable_dec G s : dec (nullable G s).
Proof.
  destruct s as [a | A].
  - right. rewrite <- nullable_derE_equi. intros [A [H0 H1]]. inv H0.
  - decide (der G A []) ; [left | right] ; rewrite <- nullable_derE_equi.
    + exists A. split ; auto.
    + intros [A' [H0 H1]]. inv H0. tauto.
Defined.

(** * Epsilon closure *)

Definition efree G := forall A u,  R A u el G -> u <> [].

Fixpoint closure (p : symbol -> Prop) {pdec : forall x, dec (p x)} (G : grammar) :=
  match G with
    [] => []
  | R A u :: Gr =>
    let
      u' := slists p u
    in let
      G' := map (R A) u'
    in G' ++ closure Gr
  end.
Arguments closure p {pdec} G.

Section EClosure.
  Variable G : grammar.
  
  Definition eclosure G:= closure (nullable G) G.
  Definition eclosed G := forall A u, R A u el G -> forall v, slist (nullable G) v u -> R A v el G.

  Lemma closure_slist A v (p : symbol -> Prop) {pdec : forall s, dec (p s)} :
    R A v el closure p G -> exists u, R A u el G /\ slist p v u.
  Proof.
    intros H.
    induction G as [| [B w] Gr IHGr] ; simpl in H ; [tauto|].
    apply in_app_or in H.
    destruct H as [H | H].
    - apply in_map_iff in H.
      destruct H as [x [H0 H1]].
      inv H0. exists w. split ; auto.
      now apply slists_slist.
    - destruct (IHGr H) as [u [H0 H1]]. exists u ; auto.
  Qed.

  Lemma slist_closure A v (p : symbol -> Prop) {pdec : forall s, dec (p s)} :
    (exists u, R A u el G /\ slist p v u) -> R A v el closure p G.
  Proof.
    intros [u [H0 H1]].
    induction G as [| [B w] Gr IHGr] ; simpl in H0 ; auto.
    destruct H0 as [H0 | H0] ; simpl ; apply in_or_app.
    - inv H0. left. apply in_map_iff.
      exists v. split ; auto. now apply slists_slist.
    - right. auto.
  Qed.

  Lemma slist_closure_equiv A v (p : symbol -> Prop) {pdec : forall s, dec (p s)} :
    R A v el closure p G <-> exists u, R A u el G /\ slist p v u.
  Proof.
    split ; [apply closure_slist | apply slist_closure].
  Qed.

  (** ** Epsilon closure is epsilon-closed **)
  Lemma nullable_eclosure s :
    nullable (eclosure G) s <-> nullable G s.
  Proof.
    split ; intros H.
    - induction H as [? ? ? ? H1 ? ?].
      apply slist_closure_equiv in H1.
      destruct H1 as [u' [H3 H4]].
      esplit ; eauto.
      eapply slist_inv ; eauto.
    - induction H as [? ? u ? ? ? ?].
      esplit ; eauto.
      apply slist_closure_equiv.
      exists u. split ; auto. apply slist_id.
  Qed.
  
  Lemma eclosed_eclosure : eclosed (eclosure G).
  Proof.
    intros A u H0 v H1.
    apply slist_closure_equiv in H0.
    apply slist_closure_equiv.
    destruct H0 as [u' [H2 H3]].
    exists u'. split ; auto.
    eapply (slist_equiv_pred nullable_eclosure) in H1.
    eapply slist_trans ; eauto.
  Qed.

  (** ** Epsilon closure preserves languages **)

  Lemma derT_slist u v :
    slist (nullable G) v u -> derT G u v.
  Proof.
    induction 1 as [| ? v u H0 ? ? | s v u ? ?].
    - constructor.
    - apply nullable_derE_equi in H0.
      destruct H0 as [A [H1 H2]].
      apply derT_der_equiv in H2.
      rewrite H1.
      assert (H3 : derT G (Vs A :: u) ([] ++ [Vs A] ++ u)) by constructor.
      apply derT_trans with (v := [] ++ [] ++ u) ; eauto.
    - replace (s :: u) with ([s] ++ u) by auto.
      replace (s :: v) with ([s] ++ v) by auto.
      apply derT_concat ; eauto.
  Qed.

  Lemma eclosure_der u v :
    derT (eclosure G) u v -> derT G u v.
  Proof.
    intros H.
    induction H as [| ? ? H |] ; eauto using derT.
    apply slist_closure_equiv in H.
    destruct H as [u' [H1 H2]].
    apply derTRule in H1.
    apply derT_slist in H2.
    eapply derT_trans ; eauto.
  Qed.
  
  Lemma der_eclosure_equiv u v :
    derT G u v <-> derT (eclosure G) u v.
  Proof.
    split.
    - induction 1 as [| A u |] ; eauto using derT.
      constructor 2.
      apply slist_closure_equiv.
      exists u. split ; auto. apply slist_id.
    - apply eclosure_der.
  Qed.
  
End EClosure.

(** * Deletion of epsilon rules *)

Section DelE.
  Variable G : grammar.
  
  Definition delE G := filter (fun r => match r with R A u => u <> [] end) G.

  (** ** delE is epsilon-free *)
  Lemma delE_efree : efree (delE G).
  Proof.
    intros A u H.
    induction G as [| [B v] Gr] ; simpl in H.
    - tauto.
    - decide (v <> []) ; (try destruct H as [H|H]) ; (try now inv H) ; auto.
  Qed.

  (** ** delE preserves languages (except for epsion) *)

  Lemma delE_preserveG A u :
    R A u el G -> u <> [] -> R A u el delE G.
  Proof.
    intros H1 H2.
    induction G as [| [B v] Gr] ; simpl in H1 ; [tauto|].
    simpl. destruct H1 as [H1 | H1].
    - inv H1. decide (u <> []) ; [auto | contradiction].
    - decide (v <> []) ; [right |] ; auto.
  Qed.

  Lemma delE_rules A u :
    R A u el (delE G) -> R A u el G.
  Proof.
    intros H.
    induction G as [| [B v] Gr] ; simpl in H ; [tauto|].
    decide (v <> []) ; try destruct H ; try (inv H ; now left) ; try (right ; auto).
  Qed.

  Lemma der_G_delE A u v :
    eclosed G -> der G A u -> slist (nullable G) v u -> v <> [] -> der (delE G) A v.
  Proof.
    intros E D Ss U.
    apply derL_der_equiv in D.
    apply derL_der_equiv.
    revert Ss U. revert v.
    induction D as [| B u v w H H0 IHD] ; intros v' Ss U.
    - assert (H0 : v' = [] \/ v' = [Vs A]). {
        inversion Ss as [| ? ? ? H H0 u' | ? u' ? H0] ; subst ; inv H0 ; auto. }
      destruct H0 ; subst ; [ tauto | eauto ].
    - apply slist_split with (xs1 := u) (xs2 := v ++ w) in Ss ; auto.
      destruct Ss as [u1 [hu [Ss0 [Ss1 Ss2]]]].
      apply slist_split with (xs1 := v) (xs2 := w) in Ss1 ; auto.
      destruct Ss1 as [v1 [w1 [Ss3 [Ss4 Ss5]]]].
      rewrite Ss2, Ss5 in *.
      assert (H1 : R B v1 el G) by eauto. 
      decide (v1 = []) as [D0 | D0].
      + rewrite D0 in *.
        assert (H2 : nullable G (Vs B)). {
          apply nullable_derE_equi.
          exists B. split ; eauto. }
        apply IHD ; auto.
        repeat apply slist_append ; auto.
      + constructor 2 with (B := B) ; auto using delE_preserveG.
        assert (H2 : slist (nullable G) (u1 ++ [Vs B] ++ w1) (u ++ [Vs B] ++ w)). {
          repeat apply slist_append ; auto. }
        apply IHD ; auto.
        intros H3. destruct u1 ; inv H3.
  Qed.

  Lemma delE_der_equiv A u :
    eclosed G -> (der G A u /\ u <> [] <-> der (delE G) A u).
  Proof.
    intros E.
    split ; intros H.
    - destruct H as [H U].
      assert (H0 : slist (nullable G) u u) by apply slist_id.
      eapply der_G_delE ; eauto.
    - induction H as [| ? ? H | ? ? u v w H IH1 H0 IH2].
      + split ; [constructor | congruence].
      + split.
        * constructor 2. now apply delE_rules.
        * now apply delE_efree in H.
      + destruct IH1 as [IH11 IH12], IH2 as [IH21 IH22].
        split ; eauto.
        destruct u, v, w ; simpl ; congruence.
  Qed.

End DelE.  

(** * Epsilon elimination *)

Definition elimE G := delE (eclosure G).

(** Epsilon elimination is epsilon-free *)
Lemma efree_elimE G :
  efree (elimE G).
Proof.
  apply delE_efree.
Qed.  

(** Epsilon elimination preserves languages (except for epsilon) *)
Lemma elimE_language G A u :
  u <> [] -> (language G A u <-> language (elimE G) A u).
Proof.
  intros U. split ; intros [H1 H2] ; split ; auto.
  - apply (delE_der_equiv A u (eclosed_eclosure (G := G))).
    split ; auto.
    apply derT_der_equiv. now apply derT_der_equiv, der_eclosure_equiv in H1.
  - apply (delE_der_equiv A u (eclosed_eclosure (G := G))) in H1.
    destruct H1 as [H1 H3].
    apply derT_der_equiv. now apply derT_der_equiv, der_eclosure_equiv in H1.
Qed.
