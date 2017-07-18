Require Export Lists.
Require Export Symbols.

Module Derivation.

  Import Base Lists Definitions Symbols ListNotations. 

  (** * Derivability and languages *)
  Section DerivabilityAndLanguages.

    Context {Tt Vt: Type}.
    
    Inductive der (G : grammar) (A : var) : list (@symbol Tt Vt) -> Prop :=
    | vDer : der G A [Vs A]
    | rDer l : (R A l) el G -> der G A l
    | replN B u w v : der G A (u ++ [Vs B] ++ w) -> der G B v -> der G A (u ++ v ++ w).
    Hint Constructors der.
    
    Definition terminal (u : (@phrase Tt Vt)) : Prop :=
      forall s, s el u -> exists t, s = Ts t.

    Lemma terminal_split u v :
      terminal (u ++ v) -> terminal u /\ terminal v.
    Proof.
      intros H.
      split ; intros s T ; apply H ; auto.
    Qed.

    Definition language (G : grammar) (A : var) (u : phrase) : Prop :=
      der G A u /\ terminal u.

  (*End DerivabilityAndLanguages.

  (** * Alternative characterizations of derivability *)
  Section AlternativeCharacterizationsOfDerivability. *)

    (* Context {Tt Vt: Type}. *)
    
    Inductive derL (G : grammar) (A : var) : list (@symbol Tt Vt) -> Prop :=
    | sDer : derL G A [Vs A]
    | gDer B u v w : (R B v) el G -> derL G A (u ++ [Vs B] ++ w) -> derL G A (u ++ v ++ w).
    Hint Constructors derL.

    Inductive derT (G : grammar) : list symbol -> list (@symbol Tt Vt) -> Prop :=
    | derTRefl u : derT G u u
    | derTRule A u : R A u el G -> derT G [Vs A] u
    | derTTrans u v w x y  : derT G x (u ++ y ++ w) -> derT G y v -> derT G x (u++v++w).
    Hint Constructors derT.

    Inductive derf (G : grammar) : phrase -> (@phrase Tt Vt) -> Prop :=
    | fRefl u : derf G u u
    | fRule A u v : R A u el G -> derf G u v -> derf G [Vs A] v
    | fCons s u v w : derf G [s] v -> derf G u w -> derf G (s :: u) (v ++ w).
    Hint Constructors derf.

    Inductive derI (G : @grammar Tt Vt) : phrase -> phrase -> Prop :=
    | derIRefl u : derI G u u
    | derIRule A u v w : R A v el G -> derI G (u ++ [Vs A] ++ w) (u ++ v ++ w)
    | derITrans u v w : derI G u v -> derI G v w -> derI G u w.
    Hint Constructors derI.

  (*End AlternativeCharacterizationsOfDerivability.

  (** ** Linear equivalences *)
  Section LinearEquivalences. *)

    (*Context {Tt Vt: Type}. *)
    
    Lemma derL_der_equiv (G : @grammar Tt Vt) (A : var) (u : list symbol) :
      der G A u <-> derL G A u.
    Proof.
      split.
      - induction 1 as [| ? l | A B u w v H IHder1 H0 IHder2] ; eauto.
        + replace l with ([] ++ l ++ []) by apply app_nil_r.
          econstructor 2 ; eauto using derL. 
        + clear H H0.
          induction IHder2 as [| C x y z] ; auto.
          replace (u ++ (x ++ y ++ z) ++ w) with ((u ++ x) ++ y ++ (z ++ w)) by now repeat rewrite app_assoc.
          econstructor 2 ; eauto.
          now replace ((u++x) ++ [Vs C] ++ (z ++ w)) with ((u ++ (x ++ [Vs C] ++ z) ++ w)) by now repeat rewrite app_assoc.
      - induction 1 ; eauto using der.
    Qed.

    Lemma derT_der_equiv (G : grammar) (A : var) (u : list symbol) :
      der G A u <-> derT G [Vs A] u.
    Proof.
      split.
      - induction 1 ; eauto using derT.
      - remember ([Vs A]) as v.
        induction 1 as [ |  | u v w x y H IHderT1 H0 IHderT2] ; try injection Heqv ; try intros He ; subst ; eauto.
        specialize (IHderT1 eq_refl).
        clear H IHderT2.
        revert IHderT1. revert u w.
        induction H0 as [| | u v w x y ? IHderT1 ? IHderT2] ; intros u' w' IH1 ; eauto.
        replace (u' ++ (u ++ v ++ w) ++ w') with ((u' ++ u) ++ v ++ (w ++ w')) by now repeat rewrite app_assoc.
        apply IHderT2.
        replace ((u' ++ u) ++ y ++ w ++ w') with (u' ++ (u ++ y ++ w) ++ w') by now repeat rewrite app_assoc.
        now apply IHderT1.
    Qed.

    (** ** Properties of derivation predicates *)
    Lemma derf_concat G u1 u2 v1 v2 :
      derf G u1 v1 -> derf G u2 v2 -> derf G (u1 ++ u2) (v1 ++ v2).
    Proof.
      intros D0 D1.
      induction D0 as [u | | ] ; simpl ; eauto.
      - induction u as [|s u] ; auto. simpl.
        replace (s :: u ++ v2) with ([s] ++ u ++ v2) ; auto.
      - rewrite <- app_assoc. auto.
    Qed.

    Lemma derf_split G u u1 u2 v :
      derf G u v -> u = u1 ++ u2 -> exists v1 v2, v = v1 ++ v2 /\ derf G u1 v1 /\ derf G u2 v2.
    Proof.
      intros D. revert u1 u2.
      induction D as [ |  | s u v w ? IHD1 ? IHD2] ; intros u1 u2 U.
      - revert U. revert u1 u2. induction u as [| s u]  ; intros u1 u2 U.
        + symmetry in U. apply app_eq_nil in U.
          destruct U as [U1 U2] ; subst.
          exists [], []. repeat split ; auto.
        + destruct u1 ; simpl in U ; subst.
          * destruct (IHu [] u) as [v1 [v2 [IH0 [IH1 IH2]]]] ; auto.
            exists [], (s :: u). repeat split ; auto.
          * inv U. destruct (IHu u1 u2) as [v1 [v2 [IH0 [IH1 IH2]]]] ; auto.
            exists (s0 :: u1), u2. repeat split ; auto.
      - destruct u1 ; simpl in U ; subst.
        + exists [], v. repeat split ; eauto.
        + inversion U as [[H0 H1]] ; subst. symmetry in H1.
          apply app_eq_nil in H1.
          destruct H1 as [H1 H1']. subst.
          exists v, []. repeat split ; eauto using app_nil_r.
      - destruct u1 ; simpl in U ; subst.
        + exists [], (v ++ w). repeat split ; auto.
        + inversion U as [[H0 H1]]. destruct (IHD2 u1 u2 H1) as [v1 [v2 [IH0 [IH1 IH2]]]] ; subst.
          exists (v ++ v1), v2. rewrite <- app_assoc. repeat split ; auto.
    Qed.
    
    Lemma derf_trans G u v w :
      derf G u v -> derf G v w -> derf G u w.
    Proof.
      intros D0. revert w.
      induction D0 as [| | ? ? v w] ; intros w' D1 ; eauto.
      apply derf_split with (u1 := v) (u2 := w) in D1 ; auto.
      destruct D1 as [v1 [v2 [D1 [D2 D3]]]].
      rewrite D1. eauto.
    Qed.

    (** ** Remaining equivalences *)

    Lemma derf_derT G u v :
      derf G u v -> derT G u v.
    Proof.
      induction 1 as [ | A u v | s u v w ? ? ? ?] ; eauto.
      - replace v with ([] ++ v ++ []) by (simpl ; auto using app_nil_r).
        econstructor 3 ; eauto.
        constructor 2. simpl. rewrite app_nil_r. eauto.
      - replace (s :: u) with ([s] ++ u) by auto.
        rewrite <- app_nil_r. rewrite <- app_assoc.
        replace ([s] ++ u) with ([s] ++ u ++ []) by now rewrite app_nil_r.
        econstructor 3 ; eauto.
        repeat rewrite app_nil_r.
        rewrite <- app_nil_l.
        replace ([s] ++ u) with ([] ++ [s] ++ u) by auto using app_nil_l.
        constructor 3 with (y := [s]) ; eauto.
    Qed.

    Lemma derT_derI (G: @grammar Tt Vt) u v :
      derT G u v -> derI G u v.
    Proof.
      induction 1 as [| A u | ? ? ? ? ? H IHderT1 H0 IHderT2] ; eauto.
      - rewrite <- app_nil_r, <- app_nil_l.
        replace [Vs A] with ([] ++ [@Vs Tt Vt A] ++ []) ; eauto.
      - clear H H0.
        induction IHderT2 ; auto.
        repeat rewrite <- app_assoc in *.
        rewrite app_assoc in * ; eauto.
    Qed.

    Lemma derI_derf G u v :
      derI G u v -> derf G u v.
    Proof.
      induction 1 ; eauto using derf_concat, derf_trans.
    Qed.  

    (** ** Inferred equivlaneces and properties *)
    Lemma derf_der_equiv G A u :
      derf G [Vs A] u <-> der G A u.
    Proof.
      split ; intros H.
      - now apply derT_der_equiv, derf_derT.
      - now apply derI_derf, derT_derI, derT_der_equiv.
    Qed.

    Lemma derT_trans (G : grammar) (u v w : list symbol) :
      derT G u v -> derT G v w -> derT G u w.
    Proof.
      intros H1 H2.
      replace w with ([] ++ w ++ []) by now rewrite <- app_nil_r.
      econstructor 3 ; eauto.
      now rewrite app_nil_l, app_nil_r.
    Qed.

    Lemma derT_concat G u u' v v' :
      derT G u v -> derT G u' v' -> derT G (u ++ u') (v ++ v').
    Proof.
      intros H0 H1.
      apply derf_derT.
      apply derT_derI, derI_derf in H0.
      apply derT_derI, derI_derf in H1.
      apply derf_concat ; auto.
    Qed.

    Lemma der_subset G1 G2 A u :
      G1 <<= G2 -> der G1 A u -> der G2 A u.
    Proof.
      induction 2 ; eauto.
    Qed.

    (** ** Further Properties *)

    Lemma der_equiv_G G1 G2 A u :
      G1 === G2 -> (der G1 A u <-> der G2 A u).
    Proof.
      intros H. split ; apply der_subset ; destruct H ; auto.
    Qed.

    Lemma symbs_der G A u :
      ~ Vs A el symbs G -> der G A u -> u = [Vs A].
    Proof.
      intros V D.
      induction D as [ | A l | A B u v w D IHD1 D0 IHD2] ; auto.
      - exfalso. apply V. apply symbs_inv. exists A, l. split ; auto.
      - specialize (IHD1 V).
        symmetry in IHD1.
        apply list_unit in IHD1.
        destruct IHD1 as [H0 [H1 H2]] ; injection H2 ; intros H3 ; subst.
        rewrite app_nil_r, app_nil_l.
        now apply IHD2.
    Qed.

  End DerivabilityAndLanguages.
  
End Derivation.