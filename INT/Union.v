Require Import List.
Require Import Fin.

Add LoadPath "../".

Require Import CFG.Base CFG.Definitions CFG.Binarize CFG.Chomsky.
Require Import INT.Base INT.DFA INT.ChomskyInduction.

Module Union.
  Import ListNotations Definitions Derivation
         INT.Base.Base INT.Base ChomskyInduction.

  Section Definitions. 

  Variable Tt Vt: Type.

  Inductive labeled_Vt : Type :=
  |  start : labeled_Vt
  |  lV : nat -> Vt -> labeled_Vt.

  Definition update_var (n : nat) (v: @var Vt): (@var labeled_Vt) :=
    match v with
    | V v => V (lV n v)
    end.
  
  Definition update_symbol (n : nat) (s: @symbol Tt Vt): (@symbol Tt labeled_Vt) :=
    match s with
    | Ts t => Ts t
    | Vs (V v) => Vs (V (lV n v))
    end.
    
  
  Definition update_rule (n : nat) (r : @rule Tt Vt): (@rule Tt labeled_Vt) :=
     match r with
     |  R (V v) p => R (V (lV n v)) (map (update_symbol n) p)
     end.

  Definition update_grammar (n : nat) (g : (@grammar Tt Vt) * Vt): @grammar Tt labeled_Vt :=
    match g with
      (gr, st) => (R (V start) [Vs (V (lV n st))]) :: (map (update_rule n) gr)
    end.

  Fixpoint grammar_union (l : list ((@grammar Tt Vt) * Vt)): @grammar Tt labeled_Vt :=
    match l with
    |  [] => []
    |  (g::t) => update_grammar (length t) g ++ (grammar_union t)
    end.

  (* TODO remove duplicate *)
  Fixpoint to_phrase (w: word): @phrase Tt Vt :=
    match w with
    | s::sx => Ts s :: to_phrase sx
    | _ => []
    end.

  Fixpoint to_word (p: @phrase Tt Vt): list ter :=
          match p with
            | Ts x :: sx => x :: to_word sx
            | _ => []
          end.

  End Definitions.

  Variable Tt Vt: Type.
  
  Definition grammar_to_language {Vl : Type} (g : (@grammar Tt Vl) * Vl) : language :=
    match g with
      (gr, st) => fun w => (der gr (V st) (to_phrase Vl w)) 
    end.                                                  

  Definition tranform_phrase (n : nat) (p : @phrase Tt Vt) : phrase :=
    map (update_symbol n) p.

  Lemma in_app : forall A (v : A) (l1 l2 : list A),
      In v l1 -> In v (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl in H; contradiction.
    simpl in H.
    destruct H.
    left.
    rewrite H.
    reflexivity.
    right.
    apply (IHl1 H).
  Qed.                                 

  (* TODO Import*)
  Definition unVar (v: var): Vt := let '(V e) := v in e.

  Lemma trasform_app : forall (n : nat) (p1 p2 : phrase),
                 tranform_phrase n (p1 ++ p2) =
                 (tranform_phrase n p1) ++ (tranform_phrase n p2).
  Proof.
    intros.
    induction p1.
    reflexivity.
    simpl.
    rewrite IHp1; reflexivity.
  Qed.
  
  Lemma same_union_0 : forall (g : grammar) (vst: Vt) (v : var)
     (l : list (grammar * Vt))
     (p : phrase)
     (d : der g v p),
      der (grammar_union (Tt:=Tt) ((g, vst) :: l)) (update_var (length l) v)
          (tranform_phrase (length l) p).
  Proof.
    intros.
    induction d.
    - destruct A.
      simpl.
      apply vDer.
        
    - apply rDer.
      simpl.
      right.
      apply in_app.
      induction g.
      simpl in H ; contradiction.
      simpl in H.
      destruct H.
      simpl.
      left.
      rewrite H.
      destruct A.
      simpl.
      reflexivity.
      simpl; right. 
      apply (IHg H).
    - rewrite trasform_app.
      rewrite trasform_app.
      apply (replN (B := (update_var (length l) B))
                   (G := (grammar_union (Tt:=Tt) ((g, vst) :: l)))
            ).
      enough (tr_eq :[Vs (update_var (length l) B)] = (tranform_phrase (length l) [Vs B])).
      rewrite tr_eq.
      rewrite <- trasform_app.
      rewrite <- trasform_app.
      apply IHd1.
      destruct B.
      simpl.
      reflexivity.
      apply IHd2.     
  Qed.  

  
  Lemma tranform_phrase_for_word : forall (n : nat) (w : word),
      to_phrase (Tt:=Tt) (labeled_Vt Vt) w =
      tranform_phrase n (to_phrase (Tt:=Tt) Vt w).
  Proof.
    intros.
    induction w.
    simpl.
    reflexivity.
    simpl.
    rewrite IHw.
    reflexivity.
  Qed.  

  Lemma in_app_2 : forall A (v : A) (l1 l2 : list A),
      In v l2 -> In v (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl in H; apply H.
    simpl.
    right.
    apply IHl1.
  Qed.      
  
  Lemma grammar_extention : forall (g1 g2 : @grammar Tt (labeled_Vt Vt))
                                   (v : var) (p : phrase),
      (der g2 v p) -> (der (g1 ++ g2) v p).
  Proof.
    intros.
    induction H.
    apply vDer.
    apply rDer.
    apply in_app_2.
    apply H.
    apply (replN (B := B)).
    apply IHder1.
    apply IHder2.
  Qed.
  
  Lemma same_union_fwd : forall (l : list (grammar * Vt)) (w : word),
     language_list_union (map grammar_to_language l) w ->
     grammar_to_language (grammar_union l, start Vt) w.
  Proof.
    intros l w H1.
    induction l.  
    simpl in H1.
    contradiction.
    simpl in H1.
    destruct H1.
    clear IHl.
    destruct a.
    unfold grammar_to_language in H.
    unfold grammar_to_language.
    remember (to_phrase (Tt:=Tt) Vt w) as p.
    assert  (eq1 : (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) = (tranform_phrase (length l) p)).
    { rewrite Heqp;  apply tranform_phrase_for_word. }
    
    rewrite eq1.
    assert (eq2 : (tranform_phrase (length l) p) = [] ++ (tranform_phrase (length l) p) ++ []).
    { rewrite Heqp.
      simpl.
      rewrite app_nil_r.
      reflexivity. }
    
    rewrite eq2.
    apply (replN (B := (V (lV (length l) v)))).
    apply rDer.
    simpl.
    left.
    reflexivity.
    assert (eq3 : (V (lV (length l) v)) = update_var (length l) (V v)).
    { simpl ; reflexivity. }
    rewrite eq3.
    apply same_union_0.
    exact H.                 
    simpl.
    apply grammar_extention.
    apply IHl.
    apply H.
  Qed.

  Lemma empty_grammar: (forall (st : var) (p : @phrase Tt (labeled_Vt Vt)),
                           (der [] st p) -> p = [Vs st]).
  Proof.
    intros.
    induction H.
    reflexivity.
    contradiction.
    rewrite <- IHder1.
    rewrite IHder2.
    reflexivity.
  Qed.
(*
  Lemma same_union_bkw_0 : forall
    (g : grammar) (v : Vt)
    (l : list (grammar * Vt))
    (n : nat)
    (p : phrase)
    (H : der (grammar_union (Tt:=Tt) ((g, v) :: l)) (V (lV n v))
        (tranform_phrase n p)),
      der g (V v) p \/ (der (grammar_union (Tt:=Tt) l) (V (lV n v)) (tranform_phrase n p)).
*)    
(*
  Lemma der_start :
    forall (l : list (grammar * Vt)) (p : @phrase Tt (labeled_Vt Vt)),
      der (grammar_union l) (V (start Vt)) p -> p <> [(Vs (V (start Vt)))] ->
      exists n0 v0, der (grammar_union l) (V (lV n0 v0)) p.
  Proof.
    intros.
    remember (V (start Vt)) as st in H.
    induction H.
    rewrite Heqst in H0.
    contradiction.
    admit.
    enough (u ++ [Vs B] ++ w <> [Vs (V (start Vt))]).
    assert (exists (n0 : nat) (v0 : Vt),
               der (grammar_union (Tt:=Tt) l) (V (lV n0 v0)) (u ++ [Vs B] ++ w)).
    apply IHder1.
    apply Heqst.
    apply H2.
    destruct H3.
    destruct H3.
    exists x, x0.
    apply (replN (B := B)).
    exact H3.
    exact H1.
  Qed.

 *)
  Lemma grammar_close : forall (l: list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der l v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) l -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall vp, In (Vs vp) p -> P vp).
  Proof.
    intros l p v0 P d is_p H0.
    induction d.
    - intros.
      simpl in H.
      destruct H.
      simplify_eq H.
      intro.
      rewrite <- H1.
      exact is_p.
      contradiction.
    - intros.
      apply (H0 A l0).
      exact H.
      exact is_p.
      exact H1.
    - intros.
      assert (In (Vs vp) v \/ In (Vs vp) u \/ In (Vs vp) w).
      { apply in_app_or in H.
      destruct H.
      right; left; exact H.
      apply in_app_or in H.
      destruct H.
      left; exact H.
      right; right; exact H.
      }
      clear H.
      destruct H1.
      + apply IHd2.
        apply IHd1.
        exact is_p.
        apply in_or_app.
        right.
        apply in_or_app.
        left.
        auto.
        exact H.
      + apply IHd1.
        exact is_p.
        destruct H.
        apply in_or_app.
        left.
        auto.
        apply in_or_app.
        right.
        apply in_or_app.
        right.
        auto.
  Qed.

  Lemma grammar_cut_l1 : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der (l1 ++ l2) v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) (l1 ++ l2) -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall r pr, In (R r pr) l1 -> (P r) -> False) ->
      der l2 v0 p.
  Proof.
    intros.
    induction H.
    - apply vDer.
    - apply rDer.
      apply in_app_or in H.
      destruct H.
      exfalso.
      apply (H2 A l).
      exact H.
      exact H0.
      exact H.
    - apply (replN (B := B)).
      apply (IHder1 H0).
      apply IHder2.
      apply (grammar_close H).
      exact H0.
      exact H1.
      apply in_or_app.
      right.
      apply in_or_app.
      left.
      auto.
  Qed.

  Lemma grammar_cut_l2 : forall (l1 l2 : list rule) (p : @phrase Tt (labeled_Vt Vt)) (v0 : var)
      (P : var -> Prop), 
      der (l1 ++ l2) v0 p ->
      (P v0) ->
      (forall r pr v1, In (R r pr) (l1 ++ l2) -> (P r) -> In (Vs v1) pr -> P v1) ->
      (forall r pr, In (R r pr) l2 -> (P r) -> False) ->
      der l1 v0 p.
  Proof.
    intros.
    induction H.
    - apply vDer.
    - apply rDer.
      apply in_app_or in H.
      destruct H.
      exact H.
      exfalso.
      apply (H2 A l).
      exact H.
      exact H0.
      
    - apply (replN (B := B)).
      apply (IHder1 H0).
      apply IHder2.
      apply (grammar_close H).
      exact H0.
      exact H1.
      apply in_or_app.
      right.
      apply in_or_app.
      left.
      auto.
  Qed.
            
  
  Definition get_n (l : @var (labeled_Vt Vt)) : nat :=
    match l with 
    |  V (start _) => 0
    |  V (lV n _) => S n
    end.

  Lemma grammar_cutable : forall (l : list (grammar * Vt))
                                 (pr : phrase)
                                 (P : nat -> Prop)
                                 (P_0 : P 0 -> False)
                                 (r : var)
                                 (v1 : var), 
    In (R r pr) (grammar_union (Tt:=Tt) l) -> (P (get_n r)) -> In (Vs v1) pr -> (P (get_n v1)).
  Proof.
    intros l pr P P_0 r v1.
    induction l.
    simpl.
    contradiction.
    intros.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    clear IHl.
    assert (n_start : forall v, (R (V (start Vt)) [Vs (V (lV (length l) v))] = R r pr -> False)).
    {
      intros.
      simplify_eq H2.
      intros.
      rewrite <- H3 in H0.
      simpl in H0.
      exact (P_0 H0).
    }    
    destruct a.
    induction g.
    simpl in H.
    destruct H.
    exfalso.
    apply (n_start v H).
    contradiction.
    simpl in H.
    destruct H.
    exfalso.
    apply (n_start v H).
    destruct H.
    destruct a.
    destruct v0.
    simpl in H.
    simplify_eq H.
    intros.
    clear H.
    rewrite <- H2 in H0.
    simpl in H0.
    rewrite <- H3 in H1.
    clear H2 H3 n_start IHg v0 v.
    induction p.
    simpl in H1.
    contradiction.
    simpl in H1.
    destruct H1.
    destruct a.
    simpl in H.
    discriminate.
    destruct v.
    simpl in H.
    simplify_eq H.
    intros.
    rewrite <- H1.
    simpl.
    exact H0.
    apply (IHp H).
    apply IHg.
    simpl.
    right.
    exact H.
    apply (IHl H H0 H1).    
  Qed.

  Lemma z_le_n : forall n, 0 <= n.
  Proof.
    intro.
    induction n.
    auto.
    auto.
  Qed.

  Lemma m_le_n : forall m n,
    m = S n -> m <= n -> False.
  Proof.
    intros.
    revert m H H0.
    induction n.
    intros.
    apply le_n_0_eq in H0.
    rewrite H in H0.
    discriminate.
    intros.
    destruct m.
    discriminate.
    apply (IHn m).
    injection H.
    auto.
    apply le_S_n.
    apply H0.
  Qed.
 
  Lemma сut_grammar_0 : forall
      (g : grammar * Vt)
      (l : list (grammar * Vt))
      (p : phrase (Tt := Tt))
      (n : nat)
      (v0 : Vt)
      (H0 : n = length l)
      (D : der (update_grammar (length l) g ++ grammar_union l) (V (lV n v0)) p),
      (der (update_grammar (length l) g) (V (lV n v0)) p).
  Proof.
    intros.
    apply grammar_cut_l2 with
        (P := fun s => (get_n s = S n))
        (l2 := grammar_union l).
    exact D.
    simpl; reflexivity.
    intros r pr v1 is_in.
    apply grammar_cutable with (l := g::l) (P := fun m => m = S n).
    discriminate.
    simpl.
    exact is_in.
    rewrite H0.
    intros.
    clear D H0 n p g v0.
    assert (get_n r <= length l).
    clear H1.
    induction l.
    simpl in H.
    contradiction.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    destruct a.
    assert (get_n r = 0 \/ get_n r = S (length l)).
    {
      destruct g.
      simpl in H.
      destruct H.
      left.
      injection H as H_eq.
      rewrite <- H_eq.
      reflexivity.
      contradiction.
      simpl in H.
      destruct H.
      injection H as H_eq.
      rewrite <- H_eq.
      left.
      reflexivity.
      destruct H.
      destruct r0.
      destruct v0.
      simpl in H.
      injection H as H_eq; rewrite <- H_eq. 
      right.
      simpl.
      reflexivity.
      right.
      induction g.
      simpl in H.
      contradiction.
      simpl in H.
      destruct H.
      destruct a.
      destruct v0.
      simpl in H.
      injection H as H_eq; rewrite <- H_eq.
      simpl.
      reflexivity.
      apply (IHg H).
    }
    destruct H0.
    rewrite H0.
    apply z_le_n.
    rewrite H0.
    apply le_n.
    simpl.
    apply le_S.
    apply (IHl H).
    apply m_le_n with (m := (get_n r)) (n := (length l)).
    exact H1.
    exact H0.
  Qed.
  

  Lemma name1: forall w st g n,
    der (map (update_rule n) g) (V (lV n st)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) ->
    der g (V st) (to_phrase (Tt:=Tt) Vt w).
  Proof.
    intros.
    
  Admitted.
 
 
  Lemma name2: forall w st n g,
      der
        (R (V (start Vt)) [Vs (V (lV n st))]
           :: map (update_rule n) g) (V (start Vt))
        (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) ->
     
      der (map (update_rule n) g) (V (lV n st))
          (to_phrase (Tt:=Tt) (labeled_Vt Vt) w).
  Proof.
 
  Admitted.

  Lemma rule_n (a : rule)
        (n0 n : nat)
        (v0 : Vt)
        (p : @phrase Tt (labeled_Vt Vt))
        (H : update_rule n a = R (V (lV n0 v0)) p): n0 = n.
  Proof.
    destruct a.
    destruct v.
    simpl in H.
    injection H as H.
    auto.
  Qed.

  Lemma rule_p_n (a : rule)
        (n0 n : nat)
        v
        (v0 : Vt)
        (p : @phrase Tt (labeled_Vt Vt))
        (H : update_rule n a = R v p):
      In (Vs (V (lV n0 v0))) p -> n0 = n.
  Proof.
    destruct a.
    destruct v1.
    simpl in H.
    injection H as H.
    intro.
    rewrite <- H0 in H1.
    clear H0 H p v.
    induction p0.
    contradiction.
    simpl in H1.
    destruct H1.
    destruct a.
    discriminate.
    destruct v.
    simpl in H.
    injection H as H.
    auto.
    auto.
  Qed.

  Lemma inner_in A (a : A) u v w : In a (u ++ v ++ w) -> In a v \/ In a (u ++ w).
  Proof.
    intro.
    apply in_app_or in H.
    destruct H.
    right.
    apply in_or_app.
    auto.
    apply in_app_or in H.
    destruct H.
    auto.
    right.
    apply in_or_app.
    auto.
  Qed.

  Lemma inner_in_rev A (a : A) u v w : In a v \/ In a (u ++ w) -> In a (u ++ v ++ w).
  Proof.
    intro.
    destruct H.
    apply in_or_app.
    right.
    apply in_or_app.
    left.
    exact H.
    apply in_app_or in H.
    destruct H.
    auto.
    auto.
  Qed.

  Lemma rule_induction
        (l : list (grammar * Vt))
        (r : rule)
        (P : rule -> Prop)
        (P_st : forall v, P (R (V (start Vt)) [Vs v]))
        (P_up : forall n a, P (update_rule n a)):
        In r (grammar_union (Tt:=Tt) l) -> P r.
  Proof.
    intro.
    induction l.
    contradiction.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    destruct a.
    clear IHl.
    induction g.
    simpl in H.
    destruct H.
    rewrite <- H.
    apply P_st.
    contradiction.
    destruct H.
    rewrite <- H.
    apply P_st.
    destruct H.
    rewrite <- H.
    apply P_up.
    apply IHg.
    simpl.
    right.
    exact H.
    apply IHl.
    apply H.
  Qed.
      
  Lemma a_start (l : list (grammar * Vt))
        (A : var)
        (p : @phrase Tt (labeled_Vt Vt)):
    der (grammar_union l) A p ->
    In (Vs (V (start Vt))) p -> 
    (V (start Vt) = A).
  Proof.
    intros.
    induction H.
    - destruct H0.
      injection H as H.
      auto.
      contradiction.
    - assert (R A l0 = R A l0 -> V (start Vt) = A).
      apply rule_induction with (l := l) (r := (R A l0)) (P := (fun r => (r = R A l0) -> (V (start Vt))=A)).
      intros.
      injection H1 as H1.
      auto.
      intros.
      destruct a.
      destruct v.
      simpl in H1.
      injection H1 as H1.
      exfalso.
      clear H l H1 A.
      revert p H2.
      induction l0.
      contradiction.
      destruct H0.
      intros.
      rewrite H in H2.
      destruct p.
      discriminate.
      destruct s.
      discriminate.
      destruct v0.
      discriminate.
      intros.
      destruct p.
      discriminate.
      injection H2 as H2.
      apply (IHl0 H p).
      exact H0.
      exact H.
      auto.
    - apply inner_in in H0.
      destruct H0.
      apply IHder2 in H0.
      apply IHder1.
      apply inner_in_rev.
      left.
      rewrite H0.
      auto.
      apply IHder1.
      apply inner_in_rev.
      right.
      exact H0.
  Qed.

  
  Lemma l3 : forall l n0 v0 v1 n1 (p : @phrase Tt (labeled_Vt Vt)),  
      der (grammar_union l) (V (lV n0 v0)) p -> In (Vs (V (lV n1 v1))) p -> n0 = n1.
  Proof.
    intros.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 Heqst n1 v1 H0.
    induction H.
    - intros.
      rewrite Heqst in H0.
      destruct H0.
      injection H as H.
      exact H.
      contradiction.
    - intros.
      induction l.
      contradiction.
      simpl in H.
      apply in_app_or in H.
      destruct H.
      destruct a.
      induction g.
      simpl in H.
      destruct H.
      injection H as H.
      rewrite Heqst in H.
      discriminate.
      contradiction.
      simpl in H.
      destruct H.
      injection H as H.
      rewrite Heqst in H.
      discriminate.
      destruct H.
      rewrite Heqst in H.
      assert (n0 = (length l)).
      apply rule_n with (a := a) (v0:=v0) (p := l0).
      exact H.
      assert (n1 = (length l)).
      apply rule_p_n with (a := a) (v0:=v1) (v:=(V (lV n0 v0))) (p := l0).
      exact H.
      exact H0.
      rewrite H1.
      rewrite H2.
      reflexivity.
      apply IHg.
      simpl.
      right.
      exact H.
      apply IHl.
      exact H.
    - intros n0 v0 is_eq n1 v1 is_in.
      apply inner_in in is_in.
      destruct is_in.
      + destruct B.
        destruct l0.
        assert (V (start Vt) = A).
        apply a_start with (l:=l) (p:=(u ++ [Vs (V (start Vt))] ++ w)).
        exact H.
        apply inner_in_rev.
        auto.
        rewrite is_eq in H2.
        discriminate.
        assert (n = n1).
        apply (IHder2 n v2) with (v1 := v1).
        reflexivity.
        exact H1.
        assert (n0 = n).
        apply (IHder1 n0 v0) with (v1 := v2).
        exact is_eq.
        apply inner_in_rev.
        auto.
        rewrite <- H2.
        rewrite H3.
        auto.
      + apply IHder1 with (v0 := v0) (v1 := v1).
        auto.
        apply inner_in_rev.
        auto.
  Qed.

  Lemma der_n_is_n (a : grammar * Vt)
        (A : var)
        (n : nat)
        (p : @phrase Tt (labeled_Vt Vt)):
   der (update_grammar (Tt:=Tt) n a) A p ->
   forall v0 n0, In (Vs (V (lV n0 v0))) p -> (p = [Vs A]) \/ n = n0.
  Proof.
    intro.      
    induction H.
    - intros.
      left.
      reflexivity.
    - intros.
      right.
      destruct a.
      destruct H.
      injection H as H.
      rewrite <- H1 in H0.
      destruct H0.
      injection H0 as H0.
      exact H0.
      contradiction.
      induction g.
      contradiction.
      destruct H.
      destruct a.
      destruct v1.
      simpl in H.
      injection H as H.
      clear H IHg A v1 g.
      rewrite <- H1 in H0.
      clear l H1.
      induction p.
      contradiction.
      destruct H0.
      destruct a.
      simpl in H.
      discriminate.
      destruct v1. 
      simpl in H.
      injection H as H.
      exact H.
      apply (IHp H).
      apply (IHg H).
    - intros.
      apply inner_in in H1.
      destruct H1.
      + assert (v = [Vs B] \/ n = n0).
        apply (IHder2 v0 n0 H1).
        destruct H2.
        assert (u ++ [Vs B] ++ w = [Vs A] \/ n = n0).
        apply (IHder1 v0 n0).
        rewrite <- H2.
        apply inner_in_rev.
        left.
        exact H1.
        destruct H3.
        rewrite <- H2 in H3.
        auto.
        auto.
        auto.
      + assert (u ++ [Vs B] ++ w = [Vs A] \/ n = n0).
        apply (IHder1 v0 n0).
        apply inner_in_rev.
        right.
        exact H1.
        destruct H2.
        assert (u = []).
        destruct u.
        auto.
        destruct u.
        discriminate.
        discriminate.
        rewrite H3 in H2.
        simpl in H2.
        assert (w = []).
        destruct w.
        auto.
        discriminate.
        rewrite H3 in H1.
        rewrite H4 in H1.
        contradiction.
        auto.
  Qed. 

  Lemma clean_start l (p : @phrase Tt (labeled_Vt Vt)):  
        der (grammar_union l) (V (start Vt)) p ->
        p = [Vs (V (start Vt))] \/
        exists g a u v, (u ++ (g, a) :: v) = l /\ der (grammar_union l) (V (lV (length v) a)) p.
  Proof.
    intros.
    remember (V (start Vt)) as st in H.
    induction H.
    - left.
      rewrite Heqst.
      reflexivity.
    - right.
      induction l.
      contradiction.
      apply in_app_or in H.
      destruct H.
      destruct a.
      clear IHl.
      exists g, v, [], l.
      split.
      auto.
      rewrite Heqst in H.
      destruct H.
      injection H as H.
      rewrite <- H.
      apply vDer.
      exfalso.
      induction g.
      contradiction.
      destruct H.
      destruct a.
      destruct v0.
      discriminate.
      auto.
      assert (H1 := IHl H).
      clear H IHl.
      destruct H1 as [g H1].
      destruct H1 as [a1 H1].
      destruct H1 as [u1 H1].
      destruct H1 as [v1 H1].
      exists g, a1, (a::u1), v1.
      destruct H1.
      split.
      rewrite <- app_comm_cons.
      apply f_equal with (f := fun l => a::l).
      auto.
      apply grammar_extention.
      auto.
    - assert (H1 := IHder1 Heqst).
      clear IHder1.
      destruct H1.
      assert (B = V (start Vt) /\ u = [] /\ w = []).
      {
        destruct u.
        simpl in H1.
        destruct w.
        injection H1 as H1.
        auto.
        discriminate.
        destruct u.
        discriminate.
        discriminate.
      }
      clear H1.
      destruct H2.
      destruct H2.
      rewrite H2.
      rewrite H3.
      simpl.
      assert (v ++ [] = v).
      apply app_nil_r.
      rewrite H4.
      apply IHder2.
      exact H1.
      destruct H1 as [g H1].
      destruct H1 as [a H1].
      destruct H1 as [u0 H1].
      destruct H1 as [v0 H1].
      right.
      exists g, a, u0, v0.
      destruct H1.
      split.
      exact H1.
      apply (replN H2 H0).    
  Qed.
  
  Definition update_grammar_simpl (n : nat) (g : (@grammar Tt Vt) * Vt):
    @grammar Tt (labeled_Vt Vt):=
    match g with
      (gr, st) => (map (update_rule n) gr)
    end.

  Fixpoint grammar_union_simpl (l : list ((@grammar Tt Vt) * Vt)):
    @grammar Tt (labeled_Vt Vt) :=
    match l with
    |  [] => []
    |  (g::t) => update_grammar_simpl (length t) g ++ (grammar_union_simpl t)
    end.

  Lemma no_start_in_der l n0 v0 (p : @phrase Tt (labeled_Vt Vt)):  
        der (grammar_union l) (V (lV n0 v0)) p ->
        In (Vs (V (start Vt))) p -> False.
  Proof.
    intro.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 Heqst.
    induction H.
    - intros.
      rewrite Heqst in H.
      destruct H.
      discriminate.
      contradiction.
    - intros.
      induction l.
      contradiction.
      apply in_app_or in H.
      destruct H.
      destruct a.
      simpl in H.
      destruct H.
      rewrite Heqst in H.
      discriminate.
      induction g.
      contradiction.
      simpl in H.
      destruct H.
      destruct a.
      destruct v1.
      simpl in H.
      injection H as H.
      clear IHl IHg Heqst H.
      rewrite <- H1 in H0.
      clear H1.
      induction p.
      contradiction.
      destruct H0.
      destruct a.
      discriminate.
      destruct v2.
      discriminate.
      exact (IHp H).
      exact (IHg H).
      exact (IHl H).
    - intros.
      apply inner_in in H1.
      destruct H1.
      destruct B.
      destruct l0.
      apply (IHder1 n0 v0 Heqst).
      apply inner_in_rev.
      auto.
      apply (IHder2 n v1).
      reflexivity.
      exact H1.
      apply (IHder1 n0 v0 Heqst).
      apply inner_in_rev.
      right.
      exact H1.
   Qed.   

  Lemma clean_start_rule l a n0 (p : @phrase Tt (labeled_Vt Vt)):  
        der (grammar_union l) (V (lV n0 a)) p ->
        der (grammar_union_simpl l) (V (lV n0 a)) p.
  Proof.
    intros.
    remember (V (lV n0 a)) as st.
    revert n0 a Heqst.
    induction H.
    - intros.
      apply vDer.
    - intros.
      apply rDer.
      induction l.
      contradiction.
      apply in_app_or in H.
      destruct H.
      destruct a0.
      clear IHl.
      apply in_or_app.
      left.
      simpl in H.
      destruct H.
      rewrite Heqst in H.
      discriminate.
      exact H.
      apply in_or_app.
      right.
      apply IHl.
      exact H.
    - intros.
      apply (replN (B := B)).
      apply (IHder1 n0 a Heqst).
      destruct B.
      destruct l0.
      exfalso.
      rewrite Heqst in H.
      apply (no_start_in_der H).
      apply inner_in_rev.
      auto.
      apply (IHder2 n v0).
      auto.
  Qed.

  Lemma ext_grammar l v (p : @phrase Tt (labeled_Vt Vt)):
        der (grammar_union_simpl l) v p ->
        der (grammar_union l) v p. 
  Proof.
    intros.
    induction H.
    - intros.
      apply vDer.
    - intros.
      apply rDer.
      induction l.
      contradiction.
      apply in_app_or in H.
      destruct H.
      clear IHl.
      apply in_or_app.
      left.
      destruct a.
      simpl.
      right.
      exact H.
      apply in_or_app.
      right.
      apply IHl.
      exact H.
    - intros.
      apply (replN (B := B)).
      apply (IHder1).
      apply (IHder2).
  Qed.

  Lemma no_start_in_der_abdtract gA n0 v0 (p : @phrase Tt (labeled_Vt Vt))
    (no_start_rule : forall A l, In (R A l) gA -> In (Vs (V (start Vt))) l -> False):  
    der gA (V (lV n0 v0)) p ->
    In (Vs (V (start Vt))) p -> False.
  Proof.
    intros.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 Heqst.
    induction H.
    - intros.
      rewrite Heqst in H0.
      destruct H0.
      discriminate.
      contradiction.
    - intros.
      apply (no_start_rule A l H).
      exact H0.
    - intros.
      apply inner_in in H0.
      destruct H0.
      destruct B.
      destruct l.
      apply IHder1 with (n0:=n0) (v0:=v0).
      apply inner_in_rev.
      auto.
      exact Heqst.
      apply IHder2 with (n0:=n) (v0:=v1).
      exact H0.
      reflexivity.
      apply IHder1 with (n0:=n0) (v0:=v0).
      apply inner_in_rev.
      right.
      exact H0.
      exact Heqst.
  Qed.
  
  Lemma no_start_in_ders l n0 v0 (p : @phrase Tt (labeled_Vt Vt)):  
        der (grammar_union_simpl l) (V (lV n0 v0)) p ->
        In (Vs (V (start Vt))) p -> False.
  Proof.
    intro.
    apply ext_grammar in H.
    apply (no_start_in_der H).
  Qed.
  

  Lemma not_start2 l n0 v0 A u w:
        A = (V (lV n0 v0)) ->
        der (grammar_union_simpl l) A (u ++ [Vs (V (start Vt))] ++ w) -> False.
  Proof.
    intros.
    rewrite H in H0.
    apply (no_start_in_ders H0).
    apply inner_in_rev.
    auto.
  Qed.
  

   Lemma der_n_is_n_abstract g0
        (n0 : nat)
        (v0 : Vt) 
        (p : @phrase Tt (labeled_Vt Vt)):
     der g0 (V (lV n0 v0)) p ->
     (forall n0 v0 n v l, In (R (V (lV n0 v0)) l) g0 -> In (Vs (V (lV n v))) l -> n = n0) ->
     (forall n0 v0 u w, der g0 (V (lV n0 v0)) (u ++ [Vs (V (start Vt))] ++ w) -> False) ->
   forall v n, In (Vs (V (lV n v))) p -> n = n0.
  Proof.
    intros H H_g0 H_st.
    intros v n.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 n v Heqst.
    induction H.
    - intros.
      rewrite Heqst in H.
      destruct H.
      injection H as H.
      auto.
      contradiction.
    - intros.
      rewrite Heqst in H.
      clear Heqst.
      apply (H_g0 n0 v0 n v l).
      exact H.
      exact H0.
    - intros.
      apply inner_in in H1.
      destruct H1.
      destruct B.
      destruct l.
      exfalso.

      apply H_st with (n0 := n0) (v0 := v0) (u := u) (w := w).
      rewrite <- Heqst.
      exact H. 
      
      assert (n = n1).
      apply (IHder2 n1 v2 n v1).
      reflexivity.
      exact H1.
      assert (n1 = n0).
      apply (IHder1 n0 v0 n1 v2).
      exact Heqst.
      apply inner_in_rev.
      auto.
      rewrite <- H3.
      exact H2.
      apply (IHder1 n0 v0 n v1).
      exact Heqst.
      apply inner_in_rev.
      auto.
  Qed.
  
   Lemma der_n_is_n_2 (l : list (grammar * Vt))
        (n0 : nat)
        (v0 : Vt) 
        (p : @phrase Tt (labeled_Vt Vt)):
   der (grammar_union_simpl l) (V (lV n0 v0)) p ->
   forall v n, In (Vs (V (lV n v))) p -> n = n0.
  Proof.
    intro.
    intros v n.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 n v Heqst.
    induction H.
    - intros.
      rewrite Heqst in H.
      destruct H.
      injection H as H.
      auto.
      contradiction.
    - intros.
      rewrite Heqst in H.
      clear Heqst.
      induction l.
      contradiction.
      apply in_app_or in H.
      destruct H.
      destruct a.
      induction g.
      contradiction.
      simpl in H.
      destruct H.
      destruct a.
      destruct v2.
      simpl in H.
      injection H as H.
      rewrite H in H2.
      rewrite <- H2 in H0.
      clear H IHg IHl H1 H2.
      induction p.
      contradiction.
      destruct H0.
      destruct a.
      discriminate.
      destruct v3.
      injection H as H.
      auto.
      auto.
      auto.
      auto.
    - intros.
      apply inner_in in H1.
      destruct H1.
      destruct B.
      destruct l0.
      apply not_start2 with (n0 := n0) (v0 := v0) in H.
      contradiction.
      apply Heqst.
      assert (n = n1).
      apply (IHder2 n1 v2 n v1).
      reflexivity.
      exact H1.
      assert (n1 = n0).
      apply (IHder1 n0 v0 n1 v2).
      exact Heqst.
      apply inner_in_rev.
      auto.
      rewrite <- H3.
      exact H2.
      apply (IHder1 n0 v0 n v1).
      exact Heqst.
      apply inner_in_rev.
      auto.
  Qed.

  Lemma cut_head a l n0 v0 p:
        der (grammar_union_simpl (a :: l)) (V (lV n0 v0)) p ->
        (length l <> n0) ->
        der (grammar_union_simpl l) (V (lV n0 v0)) p.
  Proof.
    intros.
    remember (V (lV n0 v0)) as st.
    revert n0 v0 H0 Heqst.
    induction H.
    - intros.
      apply vDer.
    - intros.
      apply in_app_or in H.
      destruct H.
      exfalso.
      rewrite Heqst in H.
      clear Heqst.
      destruct a.
      induction g.
      contradiction.
      destruct H.
      destruct a.
      destruct v1.
      injection H as H.
      auto.
      auto.
      apply rDer.
      exact H.
    - intros.
      destruct B.
      destruct l0.
      + exfalso.
        rewrite Heqst in H.
        apply (no_start_in_ders H).  
        apply inner_in_rev.
        auto.
      + apply (replN (B := (V (lV n v1)))).
        apply (IHder1 n0 v0).
        exact H1.
        apply Heqst.
        apply (IHder2 n v1).
        clear IHder1 IHder2.
        assert (n = n0).
        rewrite Heqst in H.
        apply (der_n_is_n_2 H) with (v := v1) .
        apply inner_in_rev.
        left.
        auto.
        rewrite H2.
        exact H1.
        reflexivity.
 Qed.

  Lemma n_le_n (n : nat):
    (S n <= n) -> False.
  Proof.
    intro.
    induction n.
    apply le_n_0_eq in H.
    discriminate.
    apply IHn.
    apply le_S_n.
    exact H.
  Qed.
    
    
  Lemma no_tail (r : list (grammar * Vt))
        (l : phrase)
        (n : nat)
        (v : Vt):
    length r <= n ->
    In (R (V (lV n v)) l) (grammar_union_simpl r) ->
    False.
  Proof.
    intros.
    induction r.
    contradiction.
    apply in_app_or in H0.
    destruct H0.
    - assert (length r < n).
      auto.
      clear H.
      destruct a.
      induction g.
      contradiction.
      simpl in H0.
      destruct H0.
      + destruct a.
        destruct v1.
        simpl in H.
        injection H as H.
        rewrite H in H1.
        apply (n_le_n H1).
      + apply (IHg H).
    - apply IHr.
      apply (le_Sn_le).
      simpl in H.
      exact H.
      exact H0.
  Qed.  
   
  Lemma cut_tail (g : grammar) (a : Vt)
        (r : list (grammar * Vt)) n v p :
    n = length r ->
    der (grammar_union_simpl ((g, a) :: r)) (V (lV n v)) p ->
    der (update_grammar_simpl n (g, a)) (V (lV n v)) p.
  Proof.
    intros.
    remember (V (lV n v)) as st.
    revert n v H Heqst.
    induction H0.
    - intros.
      apply vDer.
    - intros.
      apply in_app_or in H.
      destruct H.
      rewrite H0.
      apply rDer.
      exact H.
      exfalso.
      assert (H1 : length r <= n).
      {
        rewrite H0.
        apply le_n.
      }
      rewrite Heqst in H.
      apply (no_tail H1 H).      
    - intros.
      destruct B.
      destruct l.
      exfalso.
      rewrite Heqst in H0_.
      apply (no_start_in_ders H0_).  
      apply inner_in_rev.
      auto.
      apply (replN (B := (V (lV n0 v1)))).
      apply (IHder1 n v0).
      exact H.
      exact Heqst.
      apply (IHder2 n v1).
      apply H.
      assert (n0 = n).
      rewrite Heqst in H0_.
      apply (der_n_is_n_2 H0_ (v:=v1)).
      apply inner_in_rev.
      auto.
      rewrite H0.
      auto.
 Qed.

  Lemma list_lemma A (a: A) u v l:
    u ++ a :: v = l ->
    length l <> length v.
  Proof.
    intro.
    assert (length v < length l).
    revert u v H.
    induction l.
    - intros.
      exfalso.
      destruct u.
      discriminate.
      discriminate.
    - intros.
      destruct u.
      simpl in H.
      injection H as H.
      rewrite H0.
      auto.
      simpl in H.
      injection H as H.
      simpl.
      apply le_S.
      apply (IHl u v H0).
    - intro.
      rewrite H1 in H0.
      apply (n_le_n H0).
  Qed.

  Lemma update_symbol_rev_l (n : nat) (s1 s2 : @symbol Tt Vt) : 
    update_symbol n s1 = update_symbol n s2 -> s1 = s2.                                        
  Proof.
    intro.
    destruct s1.
    destruct s2.
    simpl in H.
    injection H as H.
    rewrite H.
    reflexivity.
    destruct v.
    discriminate.
    destruct s2.
    destruct v.
    discriminate.
    destruct v.
    destruct v0.
    simpl in H.
    injection H as H.
    rewrite H.
    reflexivity.
  Qed.

   Lemma not_start_in_update g a0 n0 n v A u w:
        A = (V (lV n v)) ->
        der (update_grammar_simpl n0 (g, a0)) A (u ++ [Vs (V (start Vt))] ++ w) -> False.
   Proof.
     intros.
     apply no_start_in_der_abdtract with
         (n0 := n) (v0 := v)
         (p := (u ++ [Vs (V (start Vt))] ++ w))
         (gA := update_grammar_simpl n0 (g, a0)).
     - intros.
       clear H0.
       induction g.
       contradiction.
       destruct H1.
       destruct a.
       destruct v0.
       injection H0 as H0.
       rewrite <- H1 in H2.
       clear IHg H1 H0.
       induction p.
       contradiction.
       destruct H2.
       destruct a.
       discriminate.
       destruct v1.
       discriminate.
       apply (IHp H0).
       apply (IHg H0).
     - rewrite H in H0.
       exact H0.
     - apply inner_in_rev.
       auto.
   Qed.

   Lemma app_tranform_phrase u v n p : 
     u ++ v = tranform_phrase n p ->
     exists u0 v0, u0 ++ v0 = p /\
                  u = tranform_phrase n u0 /\
                  v = tranform_phrase n v0.
   Proof.
     intros.
     revert p H.  
     induction u.
     - intros.
       exists [], p.
       split.
       auto.
       split.
       auto.
       exact H.
     - intros.
       destruct p.
       discriminate.
       destruct a.
       destruct s.
       + injection H as H.
         assert (H1 := IHu p H0).
         destruct H1 as [u0 H1].
         destruct H1 as [v0 H1].
         clear IHu H0.
         destruct H1.
         destruct H1.
         exists (Ts t :: u0), v0.
         split.
         simpl.
         rewrite H0.
         rewrite H.
         reflexivity.
         split.
         simpl.
         rewrite H1.
         reflexivity.
         exact H2.
       + destruct v0.
         discriminate.
       + destruct v0.
         destruct s.
         discriminate.
         destruct v0.
         injection H as H.
         assert (H1 := IHu p H0).
         destruct H1 as [u1 H1].
         destruct H1 as [v1 H1].
         clear IHu H0.
         exists ((Vs (V v0)) :: u1), v1.
         destruct H1.
         destruct H1.
         split.
         simpl.
         rewrite H0.
         reflexivity.
         split.
         rewrite H.
         simpl.
         rewrite H1.
         reflexivity.
         exact H2.
   Qed.

   Lemma der_n_is_n_siml (a : grammar * Vt)
         (n0 : nat)
         (v0 : Vt) 
         (p : @phrase Tt (labeled_Vt Vt)):
     der (update_grammar_simpl n0 a) (V (lV n0 v0)) p ->
     forall v n, In (Vs (V (lV n v))) p -> n = n0.
   Proof.
     intros.
     apply der_n_is_n_abstract with
         (g0 := (update_grammar_simpl n0 a))
         (v0 := v0)
         (p := p)
         (v := v).
     - exact H.
     - intros.
       clear v v0 H0 p H.
       destruct a.
       induction g.
       contradiction.
       destruct H1.
       destruct a.
       destruct v0.
       injection H as H.
       rewrite <- H1 in H2.
       rewrite H in H2.
       clear H H1 IHg.
       induction p.
       contradiction.
       destruct H2.
       destruct a.
       discriminate.
       destruct v3.
       injection H as H.
       auto.
       exact (IHp H).
       exact (IHg H).
     - intros.
       remember (V (lV n1 v1)) as A.
       destruct a.
       apply (not_start_in_update HeqA H1).
     - exact H0.
  Qed.
     

   
  Lemma update_grammar_rev
        (g : grammar)
        (a a0 : Vt)
        (p : phrase)
        (n : nat):
        der (update_grammar_simpl n (g, a0)) (V (lV n a))
         (tranform_phrase n p) ->
        der g (V a) p.
  Proof.
    intro.
    remember (tranform_phrase n p) as p0.
    remember (V (lV n a)) as A.
    revert a HeqA p Heqp0.
    induction H.
    - intros.
      rewrite HeqA in Heqp0.
      destruct p.
      discriminate.
      destruct p.
      simpl in Heqp0.
      destruct s.
      discriminate.
      destruct v.
      simpl in Heqp0.
      injection Heqp0 as H.
      rewrite H.
      apply vDer.
      discriminate.
    - intros.
      apply rDer.
      induction g.
      contradiction.
      destruct H.
      left.
      destruct a1.
      rewrite HeqA in H.
      destruct v.
      simpl in H.
      injection H as H.
      rewrite H.
      clear A IHg HeqA H.
      rewrite Heqp0 in H0.
      clear Heqp0.
      assert (p0 = p).
      revert p H0.
      induction p0.
      + intros.
        destruct p.
        reflexivity.
        discriminate.
      + intros.
        destruct p.
        discriminate.
        injection H0 as H.
        apply update_symbol_rev_l in H.
        rewrite H.
        assert (p0 = p).
        apply IHp0.
        apply H0.
        rewrite H1.
        reflexivity.
      + rewrite H.
        reflexivity.
      + right.
        apply IHg.
        exact H.
    - intros.
      destruct B.
      destruct l.
      exfalso.
      apply (not_start_in_update HeqA H).
      apply app_tranform_phrase in Heqp0.
      destruct Heqp0 as [u1 H1].
      destruct H1 as [t0 H1].
      destruct H1.
      destruct H2.
      apply app_tranform_phrase in H3.
      destruct H3 as [v1 H3].
      destruct H3 as [w1 H3].
      destruct H3.
      destruct H4.
      rewrite <- H3 in H1.
      clear H3.
      rewrite <- H1.
      assert (n0 = n).
      { rewrite HeqA in H.
        apply (der_n_is_n_siml H) with (v := v0).
        apply inner_in_rev.
        auto.
      }
      apply (replN (B := (V v0))).
      apply IHder1.
      exact HeqA.
      unfold tranform_phrase.
      rewrite map_app.
      unfold tranform_phrase in H2.
      rewrite <- H2.
      simpl.
      unfold tranform_phrase in H5.
      rewrite <- H5.
      rewrite H3.
      reflexivity.
      apply IHder2.
      rewrite H3; reflexivity.
      exact H4.
 Qed.

  Lemma tranform_phrase_of_word n w:
    (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) = (tranform_phrase n (to_phrase (Tt:=Tt) Vt w)).
  Proof.
    induction w.
    auto.
    simpl.
    rewrite IHw.
    auto.
  Qed.
                                                
                                                             
     
 Lemma update_grammar_to_union (l : list (grammar * Vt))
       (g : grammar)
       (w : word)
       (a : Vt)
       (n : nat):             
       In (g, a) l ->
  der (update_grammar_simpl n (g, a)) (V (lV n a))
         (to_phrase (Tt:=Tt) (labeled_Vt Vt) w) ->
  language_list_union (map grammar_to_language l) w.
 Proof.
   intros.
   induction l.
   contradiction.
   destruct H.
   simpl.
   left.
   rewrite H.
   simpl.

   apply update_grammar_rev with (a0 := a) (n := n).
   rewrite <- tranform_phrase_of_word.
   exact H0.
   right.
   apply IHl.
   exact H.
 Qed.  
   
 
 Lemma same_union_bkw : forall (l : list (grammar * Vt)) (w : word),
      grammar_to_language (grammar_union l, start Vt) w ->
      language_list_union (map grammar_to_language l) w.
  Proof.
    intros.
    unfold grammar_to_language in H.
    assert (H1 := clean_start H).
    destruct H1.
    {
      exfalso.
      destruct w.
      discriminate.
      discriminate.
    }
    destruct H0 as [g H0].
    destruct H0 as [a H0].
    destruct H0 as [u H0].
    destruct H0 as [v H0].
    clear H.
    destruct H0.
    apply clean_start_rule in H0.
    assert (der (update_grammar_simpl (length v) (g, a)) (V (lV (length v) a))
         (to_phrase (Tt:=Tt) (labeled_Vt Vt) w)).
    revert l H H0.
    induction u.
    intros.
    rewrite app_nil_l in H.
    rewrite <- H in H0.
    remember (length v) as n.
    apply (cut_tail Heqn H0).
    intros.
    destruct l.
    discriminate.
    apply IHu with (l := l).
    rewrite <- app_comm_cons in H.
    injection H as H.
    exact H1.
    
    apply cut_head with (a := p).
    exact H0.
    clear w IHu H0.
    simpl in H.
    injection H as H.
    apply (list_lemma H0).

    apply update_grammar_to_union with (g := g) (a := a) (n := (length v)).
    rewrite <- H.
    apply in_or_app.
    right.
    auto.
    exact H1.
  Qed.

  
  Lemma same_union: forall (l : list ((@grammar Tt Vt) * Vt)),
      language_eq (language_list_union (map grammar_to_language l)) 
                  (grammar_to_language ((grammar_union l), start Vt)).
  Proof.
    intro l.
    apply mk_laguage_eq.
    apply same_union_fwd.
    apply same_union_bkw.
  Qed.