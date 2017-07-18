Require Import List.
Require Import Fin.

Add LoadPath "~/Git/YC_in_Coq/".

Require Import CFG.Binarize.
Require Import CFG.Chomsky.
Require Import CFG.Definitions. 
Require Import CFG.Separate.

Module ChomskyInduction.
  
  Import ListNotations Base Definitions Derivation Chomsky.
  
  Section Definitions.

    Definition syntactic_analysis_is_possible :=
      forall {T V: Type} (G: @grammar T V) (A: var) (l: phrase),
        der G A l ->
        (R A l el G) \/ (exists rhs, R A rhs el G /\ derf G rhs l).
    
  End Definitions.

  Section Induction.

    Context {T V: Type}.

    Variable G: @grammar T V.
    Variable P: @var V -> @phrase T V -> Prop.

    Hypothesis H_chomsky: chomsky G. 
    Hypothesis H_syntactic_analysis: syntactic_analysis_is_possible. 

    Section Lemmas.

      Lemma derivability_from_empty:
        forall w, derf G [] w -> w = [].
      Proof.
        intros.
        assert (E: exists (r: @phrase T V), r = []).
        { exists []. reflexivity. }
        destruct E as [r E]; rewrite <- E in H.
        induction H; inversion E; auto.
      Qed.
      
      Lemma derivability_from_terminal:
        forall x y, derf G [Ts x] y -> [Ts x] = y.
      Proof.
        intros.
        assert (E: exists r, r = [@Ts _ V x]).
        { exists [Ts x]. reflexivity. }
        destruct E as [r E]; rewrite <- E in H.
        induction H; inversion E; subst; auto.
        - apply IHderf1 in E; subst.
          apply derivability_from_empty in H0; subst.
          auto.
      Qed.

      Lemma derf_is_length_monotone:
        forall p1 p2,
          derf G p1 p2 ->
          length p1 <= length p2.
      Proof.
        intros p1 p2 DERF.
        induction DERF.
        - auto.
        - apply Nat.le_trans with (m := |u|); [ | auto].
          apply not_gt; intros CONTR.
          apply lt_n_Sm_le, le_n_0_eq, eq_sym, length_zero_iff_nil in CONTR.
          subst; clear IHDERF DERF.
          destruct H_chomsky as [EF _].
          apply EF in H; auto.
        - simpl in *.
          rewrite app_length, <- Nat.add_1_r, Nat.add_comm.
          apply Nat.add_le_mono; auto.
      Qed.

      Lemma empty_is_not_derivable:
        forall r, ~ der G r [].
      Proof.
        intros r CONTR.
        apply derf_der_equiv in CONTR.      
        apply derf_is_length_monotone in CONTR.
        inversion CONTR.
      Qed.
      
      Lemma derivability_of_terminal:
        forall r t,
          der G r [Ts t] ->
          R r [Ts t] el G.
      Proof.
        intros r t DER.
        destruct (H_syntactic_analysis DER) as [EL|EL]. 
        exact EL. 
        destruct EL as [rhs [EL DER2]].
        assert (LEN:= derf_is_length_monotone DER2). 

        assert (EW: rhs = [] \/ (exists t, rhs = [Ts t]) \/ (exists v, rhs = [Vs v])).
        { destruct rhs; [left; reflexivity | right ].
          destruct rhs; [ destruct s | inversion LEN; inversion H0].
          left; exists t0; reflexivity.
          right; exists v; reflexivity. }

        destruct EW as [EQ1 | [EQ2 | EQ3]].
        { exfalso.
          subst rhs.
          destruct H_chomsky as [EF _].
          specialize (EF r [] EL).
          auto. }
        { destruct EQ2; subst rhs.
          apply derivability_from_terminal in DER2; inversion DER2; subst.
          exact EL. }
        { exfalso.
          destruct EQ3; subst rhs.
          exfalso.
          destruct H_chomsky as [_ [_ [_ UF]]].
          eapply UF.
          exists x; eauto. }
      Qed.

      Lemma derivability_step:
        forall w1 w2 r r1 r2,
          R r [Vs r1; Vs r2] el G ->
          der G r1 w1 ->
          der G r2 w2 ->
          @der T V G r (w1 ++ w2).
      Proof.
        intros w1 w2 r r1 r2 RULE DERw1 DERw2.
        apply rDer in RULE.
        rewrite app_nil_end, app_assoc_reverse.
        apply replN with (B := r2); [|exact DERw2].
        rewrite app_nil_r, <- app_nil_l.
        eapply replN with (B := r1); [|exact DERw1].
        auto.
      Qed.
      
      Lemma derivability_backward_step:
        forall w r,
          length w >= 2 ->
          terminal w -> 
          der G r w ->
          exists r1 r2 w1 w2,
            R r [Vs r1; Vs r2] el G /\
            der G r1 w1 /\
            der G r2 w2 /\      
            length w1 > 0 /\
            length w2 > 0 /\ 
            w1 ++ w2 = w.
      Proof.  
        intros w r LEN TER DER.
        apply H_syntactic_analysis in DER.
        destruct DER as [RULE | [rhs [RULE DER]]].
        { exfalso.
          destruct H_chomsky as [_ [UF [_ _]]].
          destruct w; [inversion LEN | destruct s].
          { assert (L1: Ts t el Ts t :: w). auto.
            specialize (UF _ _ RULE t L1); clear L1.
            inversion UF; subst w.
            inversion LEN; inversion H0. }
          { assert (EL: Vs v el Vs v :: w). auto.
            specialize (TER (Vs v) EL).
            destruct TER as [t EQ].
            inversion EQ. } } 
        { assert (EQ: exists r1 r2, rhs = [Vs r1; Vs r2]).
          { destruct H_chomsky as [EF [SEP [BIN UF]]].
            destruct rhs as [ | [|r1]].
            { specialize (@EF _ _ RULE).
              exfalso; auto. }
            { assert (EL: Ts t el Ts t :: rhs); auto.
              specialize (@SEP _ _ RULE t EL).
              inversion SEP; subst.
              apply derivability_from_terminal in DER; subst.
              simpl in LEN; inversion LEN; inversion H0. }
            { destruct rhs as [ | ].
              { exfalso; eapply UF; exists r1; eauto. }
              { destruct rhs as [|].
                { destruct s as [t | r2].
                  { assert (EL: Ts t el [Vs r1; Ts t]); auto.
                    specialize (@SEP _ _ RULE t EL).
                    inversion SEP; inversion H. }
                  { exists r1, r2; reflexivity. } }
                { specialize (@BIN _ _ RULE).
                  simpl in BIN; inversion BIN; inversion H0; inversion H2. } } } }
          destruct EQ as [r1 [r2 EQ]]; subst rhs.
          eapply derf_split with (u1 := [Vs r1]) (u2 := [Vs r2]) in DER; [ | auto].
          destruct DER as [w1 [w2 [EQ [DER1 DER2]]]].
          apply derf_der_equiv in DER1; apply derf_der_equiv in DER2.
          exists r1, r2, w1, w2. 
          repeat split; auto.
          + destruct w1.
            apply empty_is_not_derivable in DER1; inversion DER1.
            apply gt_Sn_O. 
          + destruct w2.
            apply empty_is_not_derivable in DER2; inversion DER2.
            apply gt_Sn_O. }
      Qed.

    End Lemmas.

    Section MainLemma.

      Hypothesis inductive_step_1:
        forall (r : _) (t : ter),
          R r [Ts t] el G ->
          P r [Ts t].

      Hypothesis inductive_step_2:
        forall (r r1 r2: _) (w1 w2 : phrase),
          R r [Vs r1; Vs r2] el G ->
          P r1 w1 ->
          P r2 w2 ->
          terminal w1 ->
          terminal w2 ->
          der G r1 w1 ->
          der G r2 w2 ->
          P r (w1 ++ w2).
      
      Lemma chomsky_derivability_induction:
        forall (r : _) (w : _),
          @der T V G r w ->
          terminal w ->
          P r w.
      Proof. 
        intros r w DER. 
        assert (LEN: exists n, length w <= n).
        { exists (length w); apply le_n. }
        destruct LEN as [n LEN].
        generalize dependent LEN.
        generalize dependent w.
        generalize dependent r.
        induction n as [|n].
        { intros. 
          exfalso.
          apply le_n_0_eq, eq_sym, length_zero_iff_nil in LEN.
          subst w.
          eapply empty_is_not_derivable; eauto. }
        { intros r w DER LEN TER.
          apply le_lt_or_eq in LEN; destruct LEN as [LEN|LEN].
          { apply IHn; auto. 
            apply lt_n_Sm_le; exact LEN. }
          { assert (LEN': | w | = 1 \/ | w | > 1).
            { destruct n; [left | right]. exact LEN. rewrite LEN; apply gt_n_S, gt_Sn_O. }
            destruct LEN' as [LEN'|LEN']; [clear LEN | ].
            { assert (EW: (exists t, w = [Ts t]) \/ (exists v, w = [Vs v])).
              { destruct w; [inversion LEN' | ].
                destruct w; [destruct s | ].
                left; exists t; reflexivity. right; exists v; reflexivity.
                inversion LEN'. }
              destruct EW as [[t EQ] | [v EQ]]; subst w.
              { apply inductive_step_1, derivability_of_terminal; auto. }
              { exfalso.
                unfold terminal in TER.
                assert (L: (@Vs T V v) el [Vs v]). auto.
                specialize (TER (Vs v) L).
                inversion TER as [t EQ]; inversion EQ. } }
            { apply gt_le_S in LEN'.
              assert (L:= @derivability_backward_step w r LEN' TER DER).
              destruct L as[r1 [r2 [w1 [w2 [IN [DER1 [DER2 [LEN1 [LEN2 EQ]]]]]]]]].
              rewrite <- EQ.
              assert (length w1 + length w2 = length w).
              { rewrite <- EQ, app_length; reflexivity. } 
              rewrite LEN in H.
              rewrite <- EQ in TER.
              destruct (terminal_split TER) as [T1 T2].
              eapply inductive_step_2; eauto.
              { apply IHn; auto.
                apply Nat.add_sub_eq_r in H. rewrite <- H.
                apply Nat.le_sub_le_add_r.
                apply Nat.le_trans with (m := n + 1).
                { rewrite Nat.add_1_r; auto. }
                { apply plus_le_compat_l; auto. } }
              {  apply IHn; auto.
                 apply Nat.add_sub_eq_l in H; rewrite <- H.
                 apply Nat.le_sub_le_add_r.
                 apply Nat.le_trans with (m := n + 1).
                 { rewrite Nat.add_1_r; auto. }
                 { apply plus_le_compat_l; auto. } } } } }
      Qed.

    End MainLemma.
    
  End Induction.

End ChomskyInduction.