Require Export Derivation.

Module ElimU.

  Import Base Lists Definitions Symbols Derivation.
  
  Section ElimU.

    Context {Tt Vt: Type}.
    Context {Tt_eqdec: eq_dec Tt}.
    Context {Vt_eqdec: eq_dec Vt}.
    
    (** alternative definiton of Domain, with other type than dom *)
    Fixpoint domV (G: @grammar Tt Vt) : list var :=
      match G with
          [] => []
        | R A u :: Gr => A :: domV Gr
      end.

    Lemma dom_domV (G: @grammar Tt Vt) A :
      A el (domV G) <-> Vs A el (dom G).
    Proof.
      induction G as [| [B u] Gr] ; simpl ; [tauto|].
      rewrite IHGr. split ; intros [H | H] ; try inv H ; auto.
    Qed.

    Lemma rule_domVG G A u :
      R A u el G -> A el domV G.
    Proof.
      rewrite dom_domV.
      apply rule_domG.
    Qed.

    Lemma domVG_rule G A :
      A el (domV G) -> exists u, R A u el G.
    Proof.
      intros H.
      apply dom_domV, domG_rule in H.
      destruct H as [A' [u [H0 H1]]].
      exists u. now inv H0.  
    Qed.

    (** * Elimination of Unit Rules *)

    Definition unitfree (G: @grammar Tt Vt) := forall A, ~ exists B, R A [Vs B] el G.

    Section UnitRules.
      Variable G : @grammar Tt Vt.

      Definition rules (u : list var) (v : list phrase) := product (@R Tt Vt) u v.  
      Definition N : grammar := rules (domV G) (ran G).

      Definition step M s :=
        match s with
            R A u => (~ (exists B, u = [Vs B]) /\ R A u el G)
                    \/ (exists B, R A [Vs B] el G /\ R B u el M)
        end.

      Global Instance step_dec' G' M A u : dec (exists B, (@R Tt Vt) A [Vs B] el G' /\ (@R Tt Vt) B u el M).
      Proof.
        induction M as [| [C w] Mr IHMr].
        - right. intros [B [H0 []]].
        - destruct IHMr as [IH | IH].
          + left. destruct IH as [B [H0 H1]].
            exists B. split ; auto.
          + decide (R A [Vs C] el G' /\ w = u) as [D | D].
            * left. exists C. destruct D as [D0 D1]. rewrite D1. split ; auto.
            * right. intros [B [H0 [H1 | H1]]].
              { apply D. inv H1. auto. }
              { apply IH. exists B. split ; auto. }
      Defined.

      Global Instance step_dec M s : dec (step M s).
      Proof.
        destruct s as [A u].
        simpl. induction G as [| [B v] Gr IHGr].
        - right. intros [[H0 H1] | [B [H1 H2]]] ; try now inv H1.
        - destruct IHGr as [IH | IH].
          + left. destruct IH as [[IH0 IH1] | [C [IH0 IH1]]].
            * left. split ; auto.
            * right. exists C. split ; auto.
          + decide (R A u = R B v /\ ~ (exists C, u = [Vs C])) as [D | D].
            * left. destruct D as [H0 H1].
              left. inv H0. split ; auto.
            * decide (exists B0 : var, R A [Vs B0] el R B v :: Gr /\ R B0 u el M) as [D0 | D0].
              { left. now right. }
              { right. intros [[H0 [H1 | H1]] | H0] ; try inv H1 ; try split ; auto. }
      Defined.

      Definition elimU : grammar :=  FCI.C (step := step) N.

      (** ** elimU is unit-free *)
      
      Lemma unitfree_elimU' :
        inclp elimU (fun i => match i with R A u => ~ exists B, u = [Vs B] end).
      Proof.
        apply FCI.ind.
        intros M [A u] Icl VG S.
        destruct S as [[S0 S1] | [C [S0 S1]]] ; [|specialize (Icl (R C u) S1) ; simpl] ; auto.
      Qed.
      
      Lemma unitfree_elimU :
        unitfree elimU.
      Proof.
        intros A [B H]. apply (unitfree_elimU' H). now (exists B).
      Qed.
      
      (** ** elimU preserves languages *)  
      Lemma elimU_corr A u :
        R A u el G -> (~ exists B, u = [Vs B]) -> R A u el elimU.
      Proof.
        intros H0 H1.
        apply FCI.closure.
        - apply prod_corr. exists A, u.
          repeat split ; eauto using rule_domVG, rule_ranG.
        - left. split ; auto.
      Qed.

      Lemma ran_elimU_G u :
        u el ran elimU -> u el ran G.
      Proof.
        intros H.
        apply ranG_rule in H. destruct H as [A H].
        unfold elimU in H. apply FCI.incl, prod_corr in H.
        destruct H as [? [? [H0 [_ ?]]]]. now inv H0.
      Qed.

      Lemma elimU_corr2 A B u :
        R A [Vs B] el G -> R B u el elimU -> R A u el elimU.
      Proof.
        intros H0 H1.
        apply FCI.closure.
        - apply prod_corr.
          exists A, u. repeat split ; auto.
          + eapply rule_domVG ; eauto.
          + apply rule_ranG in H1. now apply ran_elimU_G in H1.
        - simpl. right. exists B. split ; auto.
      Qed.

      (* TODO: del *)
      Hint Constructors derf.
      (** rules in elimU can be simulated by a derivation *)
      Lemma elimU_corr3' :
        inclp elimU (fun i => match i with R A u => derf G [Vs A] u end).
      Proof.
        unfold elimU. apply FCI.ind.
        intros M [A u] Icl V S.
        destruct S as [[S0 S1] | [B [S0 S1]]] ; [|specialize (Icl (R B u) S1)] ; eauto.
      Qed.

      Lemma elimU_corr3 A u :
        R A u el elimU -> derf G [Vs A] u.
      Proof. intros elimU. exact (elimU_corr3' elimU). Qed.

      (** completeness of derivability *)
      Lemma derfG_derfelimU u v :
        terminal v -> derf G u v -> derf elimU u v.
      Proof.
        intros T D.
        induction D as [| A u v H H0 IHD|] ; auto.
        - specialize (IHD T).
          decide (exists B, u = [Vs B]) as [D | D].
          + destruct D as [B U'].
            assert (H1 : exists v', R B v' el elimU /\ derf elimU v' v).
            { induction IHD as [| | ? ? ? ? IH0 IHD0 IH1 IHD1] ; subst.
              - assert (H1 : @Vs Tt Vt B el [Vs B]) by auto.
                destruct (T0 (Vs B) H1) as [t T']. inv T'.
              - exists u. split ; inv U' ; auto.
              - inv U'. inv IH1. rewrite app_nil_r in *. apply IHD0 ; auto. }
            destruct H1 as [v' [H1 H2]]. subst.
            apply (elimU_corr2 H) in H1 ; eauto.
          + apply elimU_corr in H ; eauto.
        - apply terminal_split in T.
          destruct T as [T0 T1]. eauto.
      Qed.

      (** soundness of derivability *)
      Lemma derfelimU_derfG u v :
        derf elimU u v -> derf G u v.
      Proof.
        induction 1 ; eauto using elimU_corr3, derf_trans.
      Qed.

      Lemma elimU_der_equiv u v :
        terminal v -> (derf G u v <-> derf elimU u v).
      Proof.
        intros H. split ; auto using derfelimU_derfG, derfG_derfelimU.
      Qed.

      Lemma unit_language A u :
        language G A u <-> language elimU A u.
      Proof.
        split ; intros [L0 L1] ; split ; auto ; apply derf_der_equiv ; apply derf_der_equiv in L0 ; [rewrite <- elimU_der_equiv | rewrite elimU_der_equiv] ; auto.
      Qed.

    End UnitRules.
    
  End ElimU.

End ElimU.
