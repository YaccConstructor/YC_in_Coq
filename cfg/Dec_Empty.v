Require Export Definitions Derivation Symbols.

Module Dec_Empty.

  Import Base Lists Definitions Derivation Symbols.

  Section Dec_Empty.
    
    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.
    
    Variable G : @grammar Tt Vt.  
    Hint Constructors derf.
    
    (** * Productive variables *)
    
    Inductive productive (G : @grammar Tt Vt) : symbol -> Prop :=
    | TProd (a : ter) : productive G (Ts a)
    | VProd A u : R A u el G -> (forall s, s el u -> productive G s) -> productive G (Vs A).
    Hint Constructors productive.
    
    Lemma derf_productive u v :
      derf G u v -> (forall s, s el v -> productive G s) -> forall s, s el u -> productive G s.
    Proof.
      intros D H.
      induction D ; intros s' E ; auto ; destruct E as [E | E] ; try destruct E ; subst ; eauto.
    Qed.
    
    Lemma productive_derf s :
      productive G s -> exists x, derf G [s] x /\ terminal x.
    Proof.
      induction 1 as [a | A u H0 H1 IH].
      - exists [Ts a]. split ; auto.
        intros s [H | H] ; [subst ; exists a ; auto | destruct H].
      -  cut (exists y, derf G u y /\ terminal y).
         + intros [y [H2 H3]]. exists y. split ; eauto.
         + clear H1 H0. induction u as [| s u IHu].
           * exists []. split ; auto. intros s [].
           * assert (H0 : forall s, s el u -> exists x : phrase, derf G [s] x /\ terminal x) by auto.
             destruct (IHu H0) as [y [H1 H2]].
             assert (H3 : s el s :: u) by auto.
             destruct (IH s H3) as [x [IH0 IH1]].
             exists (x ++ y). split ; auto.
             intros s' T. apply in_app_iff in T. destruct T as [T | T] ; auto.
    Qed.

    Lemma productive_derWord_equi A :
      (exists w, der G A w /\ terminal w) <-> productive G (Vs A).
    Proof.
      split ; intro H.
      - destruct H as [w [H1 H2]].
        apply derf_der_equiv in H1.
        eapply derf_productive ; eauto.
        intros s W.
        destruct (H2 s W) as [t H3] ; subst ; auto.
      - apply productive_derf in H.
        destruct H as [w H].
        exists w. now rewrite <- derf_der_equiv.     
    Qed.

    (** ** Compute productive variables *)
    Definition step (M : list (@symbol Tt Vt)) s :=
      (exists a, s = @Ts Tt Vt a) \/
      exists A u, s = Vs A /\
             R A u el G /\
             forall s', s' el u -> s' el M.

    Global Instance step_dec M s : dec (step M s).
    Proof.
      destruct s as [a | A].
      - left. left. exists a. auto.
      - decide (exists u, R A u el G /\ forall s', s' el u -> s' el M) as [D | D].
        + left. right. destruct D as [u [D0 D1]].  exists A, u. repeat split ; auto.
        + right. intros [[a H0] | [A' [u [H0 [H1 H2]]]]] ; inversion H0 as [H3] ; subst.
          apply D. exists u. auto.
    Defined. 

    
    Definition P : list (@symbol Tt Vt) := 
      FCI.C (step := step) (symbs G).

    (** ** Correctness *)
    Lemma productive_P s :
      s el symbs G -> productive G s -> s el P.
    Proof.
      intros E H.
      induction H ; apply FCI.closure ; auto.
      -  left. exists a. auto.
      - right. exists A, u. repeat split ; auto.
        intros s' H2. apply H1 ; auto.
        apply symbs_inv.
        exists A, u. split ; auto.
    Qed.

    Lemma P_productive s :
      s el P -> productive G s.
    Proof.
      apply FCI.ind.
      intros M x H0 H1 H2.
      destruct H2 as [[a H2] | [A [u [H2 [H3 H4]]]]] ; rewrite H2 ; eauto.
    Qed.

    Lemma P_productive_equiv s :
      s el symbs G -> (s el P <-> productive G s).
    Proof.  intros H. split ; [apply P_productive | now apply productive_P]. Qed.

  End Dec_Empty.
 
  (** * Decidability of emptiness *)
  Section DecidabilityOfEmptiness.

    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.

    Global Instance productive_dec : forall (G: @grammar Tt Vt) s, dec (productive G s).
    Proof.
      intros G [a | A].
      - left. constructor.
      - decide (Vs A el (symbs G)) as [D | D].
        + decide ((Vs A) el P G) ; [left | right] ; now rewrite <- P_productive_equiv.
        + right. intros H. inversion H as [| ? u H1 H2] ; subst. apply D, symbs_inv. exists A, u. split ; auto.
    Defined. 
    
    Global Instance exists_dec : forall G A, dec (exists u, @language Tt Vt G A u).
    Proof.
      intros G A.
      decide (productive G (Vs A)) as [P | P] ; rewrite <- productive_derWord_equi in P ; [left | right] ; auto.
    Defined.  
    
  End DecidabilityOfEmptiness.

End Dec_Empty.