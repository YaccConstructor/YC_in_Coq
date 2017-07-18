Require Export Definitions.

Module Symbols.

  Import Base Lists Definitions. 

  (** * Domain and range **)
  Section DomainAndRange.

    Context {Tt Vt: Type}.

    Fixpoint dom (G : @grammar Tt Vt) : list (@symbol Tt Vt):=
      match G with
        |[] => []
        |R A u :: Gr => (Vs A) :: dom Gr
      end.

    Fixpoint ran G: list (@phrase Tt Vt) :=
      match G with
          [] => []
        | R A u :: Gr => u :: ran Gr
      end.

    Lemma rule_domG G A u :
      R A u el G -> Vs A el dom G.
    Proof.
      intros H. induction G as [| [B v] Gr] ; simpl ; auto.
      destruct H as [H | H] ; [inv H | ] ; auto.
    Qed.

    Lemma domG_rule G s :
      s el (dom G) -> exists A u, s = Vs A /\ R A u el G.
    Proof.
      intros H.
      induction G as [| [B v] Gr IHGr] ; simpl in * ; try tauto.
      destruct H as [H | H].
      - subst. exists B, v. auto.
      - destruct (IHGr H) as [A [u [H1 H2]]].
        exists A, u. auto.
    Qed.

    Lemma dom_subset G G' :
      G <<= G' -> dom G <<= dom G'.
    Proof.
      intros E s H.
      apply domG_rule in H.
      destruct H as [A [u [H0 H1]]].
      rewrite H0. eapply rule_domG ; eauto.
    Qed.

    Lemma rule_ranG G A u :
      R A u el G -> u el ran G.
    Proof.
      intros H.
      induction G as [| [B v] G].
      - inv H.
      - simpl. destruct H as [H | H] ; [inv H | ] ; auto.
    Qed.  

    Lemma ranG_rule G u :
      u el ran G -> exists A, R A u el G.
    Proof.
      intros H.
      induction G as [| [B v] Gr IHGr] ; simpl in H ; destruct H.
      - subst. exists B. auto. 
      - destruct (IHGr H) as [A H0]. exists A. auto.
    Qed.

  End DomainAndRange.
  
  (** * Symbols **)
  Section Symbols.

    Context {Tt Vt: Type}.
    
    Fixpoint symbs G: list (@symbol Tt Vt) :=
      match G with
          [] => []
        | R A u :: Gr => Vs A :: u ++ symbs Gr
      end.

    Lemma symbs_dom G s :
      s el dom G -> s el symbs G.
    Proof.
      intros H.
      induction G as [| [A u] Gr IHGr] ; simpl ; auto.
      simpl in H. destruct H ; auto.
    Qed.

    Lemma symbs_inv G s :
      s el symbs G <-> exists A u, R A u el G /\ (s = (Vs A) \/ s el u).
    Proof.
      split.
      - intros E.
        induction G as [| [A u] Gr IHGr] ; simpl in E ; try tauto.
        destruct E as [E | E] ; [exists A, u ; auto|].
        apply in_app_or in E. destruct E as [E | E] ; [exists A, u ; auto|].
        destruct (IHGr E) as [A' [u' [H0 H1]]]. exists A', u'. auto.
      - intros [A [u [H0 H1]]].
        induction G as [| [A' u'] Gr IHGr] ; simpl ; try tauto.
        destruct H0 as [H0 | H0].
        + injection H0 ; intros H2 H3 ; subst. destruct H1 as [H1 | H1] ; [left | right] ; auto.
        + right. apply in_or_app. right. auto.
    Qed.
    
    Lemma symbs_subset G G' s :
      G <<= G' -> s el symbs G -> s el symbs G'.
    Proof.
      intros H0 H1.
      apply symbs_inv in H1.
      destruct H1 as [A' [u' [H1 H2]]].
      assert (H3 : R A' u' el G') by auto.
      eapply symbs_inv ; eauto.
    Qed.

  End Symbols.
  

    (** * Fresh variables **)
  Section FreshVariables.
    
    Context {Tt Vt: Type}.
    
    Context {TtToNat: Tt -> nat}.
    Context {VtToNat: Vt -> nat}.
    Context {NatToTt: nat -> Tt }.
    Context {NatToVt: nat -> Vt}.

    Hypothesis Id1: forall x, TtToNat (NatToTt x) = x.
    Hypothesis Id2: forall x, NatToTt (TtToNat x) = x.
    Hypothesis Id3: forall x, VtToNat (NatToVt x) = x.
    Hypothesis Id4: forall x, NatToVt (VtToNat x) = x.


    (** lift <= and < to symbols *)
    Definition getNat s :=
      match s with
          Vs (V i) => VtToNat i
        | Ts (T i) => TtToNat i
      end.

    Definition sless n s := getNat s <= n.
    Definition sless' s s' := getNat s < getNat s'.

    Instance sless_dec n s : dec (sless n s).
    Proof.
      unfold sless. destruct s as [[i] | [i]] ; auto.
    Defined.

    Lemma sless_monotone m n s :
      m <= n -> sless m s -> sless n s.
    Proof.
      unfold sless ; destruct s as [[i] | [i]] ; simpl ; omega.
    Qed.

    (** compute maximal symbol of a grammar *)

    Fixpoint maxSymbRule (sl : list symbol) :=
      match sl with
        | [] => 0
        | s :: u => let
            n := maxSymbRule u
          in if decision (sless n s) then n else getNat s
      end.

    Fixpoint maxSymb (G : grammar) n :=
      match G with
        | [] => n
        | R A u :: Gr => let
            (m0, m1) := (maxSymbRule (Vs A :: u), maxSymb Gr n)
          in if decision (m0 < m1) then m1 else m0
      end.

    Lemma maxSymbRule_corr u s :
      s el u -> sless (maxSymbRule u) s.
    Proof.
      intros H.
      unfold sless.
      induction u as [| s' u IHu] ; try now destruct H.
      simpl. decide (sless (maxSymbRule u) s') ; destruct H as [H | H] ; try (rewrite <- H) ; auto.
      unfold sless in n.
      setoid_transitivity (maxSymbRule u) ; auto ; omega.
    Qed.

    Lemma maxSymb_corr G s n :
      s el symbs G -> sless (maxSymb G n) s.
    Proof.
      intros H. revert n.
      apply symbs_inv in H.
      destruct H as [A [u [H0 H1]]].
      induction G as [| [A' u'] Gr IHGr] ; intros n ; simpl in H0 ; try tauto.
      change (sless (if decision (maxSymbRule (Vs A' :: u') < maxSymb Gr n) then maxSymb Gr n else maxSymbRule (Vs A' :: u')) s).
      destruct H0 as [H0 | H0].
      - injection H0 ; intros H2 H3 ; subst.
        assert (H4 : s el (Vs A :: u)) by (destruct H1 as [H1 | H1] ; try rewrite H1 ; auto).
        apply maxSymbRule_corr in H4.
        decide (maxSymbRule (Vs A :: u) < maxSymb Gr n) ; auto.
        apply sless_monotone with (m := maxSymbRule (Vs A :: u)) ; auto ; omega.
      - decide (maxSymbRule (Vs A' :: u') < maxSymb Gr n) ; auto.
        apply sless_monotone with (m := maxSymb Gr n) ; auto ; omega.
    Qed.

    (** fresh variables *)

    Definition fresh G s := forall s', s' el symbs G -> sless' s' s.
 
    Lemma pickFresh G :
      { A | fresh G (Vs A) }.
    Proof.
      exists (V (NatToVt (S (maxSymb G 0)))).
      intros s' H.
      apply maxSymb_corr with (n := 0) in H.
      unfold sless in H. unfold sless'.
      destruct s' as [[i] | [i]] ; simpl in * .
      rewrite Id3. omega.
      rewrite Id3. omega.
    Defined.

    Lemma fresh_symbs G s :
      fresh G s -> ~ s el symbs G.
    Proof.
      intros N Sy.
      specialize (N s Sy).
      simpl in N. unfold sless' in N.
      destruct s as [ [i] | [i] ]; omega.
    Qed.  

  End FreshVariables.

End Symbols.