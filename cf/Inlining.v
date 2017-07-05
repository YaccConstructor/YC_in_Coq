Require Export Derivation.

(** * Substitution in grammars *)
Definition substG G s u := map (fun r => match r with R B v => R B (substL v s u) end) G.

Lemma substG_split G1 G2 s u :
  substG (G1 ++ G2) s u = substG G1 s u ++ substG G2 s u.
Proof.
  induction G1 as [| [A v] G1] ; simpl ; f_equal ; auto.
Qed.

Lemma substG_skipRule G A s u v :
  ~ s el u -> substG (R A u :: G) s v = R A u :: (substG G s v).
Proof.
  intros U.
  induction G as [| [C w] Gr IHGr] ; simpl in *.
  - rewrite substL_skip ; auto.
  - inversion IHGr as [H0]. f_equal. now do 2 rewrite H0.
Qed.

Lemma substG_skip G s u :
  ~ s el symbs G -> substG G s u = G.
Proof with (intros H0 ; apply H ; simpl ; auto).
  intros H.
  induction G as [| [A v] Gr IHGr] ; [simpl ; auto|].
  rewrite substG_skipRule ; [f_equal ; apply IHGr | ]...
Qed.

(** substitution of a fresh variable is reversible *)
Lemma substG_undo G B s :
  fresh G (Vs B) -> substG (substG G s [Vs B]) (Vs B) [s] = G.
Proof.
  intros N.
  induction G as [| [A u] Gr IHGr] ; simpl ; auto.
  assert (N' : fresh Gr (Vs B)). {
    intros s' H. apply N. apply symbs_subset with (G := Gr) ; auto. }
  rewrite (IHGr N').
  do 2 f_equal. apply substL_undo.
  intros H.
  assert (H0 : (Vs B) el symbs (R A u :: Gr)) by (simpl ; auto).
  specialize (N (Vs B) H0). unfold sless' in N. destruct B ; simpl in N ; omega.
Qed. 

(** substitution can be simulated by derivability *)
Lemma substL_der G B u v :
  R B v el G -> derT G u (substL u (Vs B) v).
Proof.
  intros H.
  induction u as [| s u IHu] ; simpl ; eauto.
  decide (s = Vs B) as [D | D].
  - rewrite D in *.
    replace (Vs B :: u) with ([Vs B] ++ u) by auto.
    apply derT_concat ; eauto.
  - change (derT G ([s] ++ u) ([s] ++ substL u (Vs B) v)).
    apply derT_concat ; eauto.
Qed.

(** correctness lemma of substG *)
Lemma substG_inG G A s u v :
  R A u el G -> R A (substL u s v) el (substG G s v).
Proof.
  intros H.
  induction G as [| [C w] Gr IHGr] ; simpl ; auto.
  destruct H as [H | H] ; [ inv H ; left | right] ; auto.
Qed.

(** substitution preserves domain *)
Lemma substG_dom G s u :
  dom (substG G s u) = dom G.
Proof.
  induction G as [| [B v] Gr IHGr] ; simpl in * ; auto.
  now f_equal.
Qed.


(** * Elimination of a deterministic rule *)

(** ** if part **)
Lemma in_substG_der G A B u v :
  R A u el (substG G (Vs B) v) -> der (R B v :: G) A u.
Proof.
  intros H. unfold substG in H.
  apply in_map_iff in H.
  destruct H as [[B' v'] [H0 H1]].
  inv H0. apply derT_der_equiv.
  assert (H2 : R B v el (R B v :: G)) by auto.
  apply substL_der with (u := v') in H2.
  apply derT_trans with (v := v') ; eauto.
Qed.  

Lemma der_substG_G G A B u v :
  der (substG G (Vs B) v) A u -> der (R B v :: G) A u.
Proof.
  induction 1 ; eauto.
  now apply in_substG_der.
Qed.

(** ** only-if-part **)
Lemma der_G_substG' G A B u v :
  A <> B -> ~ Vs B el dom G -> ~ Vs B el v -> derL (R B v :: G) A u -> derL (substG G (Vs B) v) A (substL u (Vs B) v).
Proof.
  intros U S V D.
  induction D as [| B' u v' w H H0 IHD].
  - simpl. decide (Vs A = Vs B) as [D | D] ; [inv D ; tauto | constructor].
  - destruct H ; [inv H | ] ;
      do 2 rewrite substL_split in IHD ;
      do 2 rewrite substL_split ;
      simpl in IHD.
    + decide (Vs B' = Vs B') as [DV | DV ] ; try tauto.
      replace (substL v' (Vs B') v') with v' by (rewrite substL_skip ; auto).
      now rewrite app_nil_r in IHD.
    + assert (H1 : Vs B' <> Vs B) by (apply rule_domG in H ; intros H1 ; inv H1 ; tauto).
      decide (Vs B' = Vs B) ; [tauto | ] ; eauto using substG_inG.
Qed.

Lemma der_G_substG G A B u v :
  A <> B -> ~ Vs B el (dom G) -> ~ Vs B el v -> ~ Vs B el u -> der (R B v :: G) A u -> der (substG G (Vs B) v) A u.
Proof.
  intros S V U H D.
  apply derL_der_equiv, der_G_substG' in D ; auto.
  apply derL_der_equiv.
  rewrite substL_skip in D ; auto.
Qed.

(** corollary **)
Lemma der_substG_G_equiv G u v A B :
  A <> B -> ~ Vs B el (dom G) -> ~ Vs B el v -> ~ Vs B el u -> (der (R B v :: G) A u <-> der (substG G (Vs B) v) A u).
Proof.
  intros H H0 H1 H2. split ; intros D ; [apply der_G_substG | apply der_substG_G] ; auto.
Qed.        

Lemma inl_language_equiv G A B u v :
  A <> B -> ~ Vs B el (dom G) -> ~ Vs B el v -> (language (substG G (Vs B) v) A u <-> language (R B v :: G) A u).
Proof.
  intros H H0 H1.
  split ; intros [L0 L1] ; split ; auto ; apply der_substG_G_equiv ; auto ; intros H2 ; destruct (L1 (Vs B) H2) as [a T] ; inv T.
Qed.


(** * Elimination of a list of deterministic rules *)

Fixpoint inlL L G :=
  match L with
    [] => G
  | R A u :: Lr => substG (inlL Lr G) (Vs A) u
  end.

Inductive inlinable (G : grammar) : grammar -> Prop :=
| inN : inlinable G nil
| inR A u Gr : 
   ~ Vs A el u -> ~ Vs A el dom Gr -> ~ Vs A el dom G -> disjoint u (dom Gr) ->
   inlinable G Gr -> inlinable G (R A u :: Gr).
Hint Constructors inlinable.
  
Lemma inlinable_cons M G A u :
  ~ Vs A el dom M -> inlinable G M -> inlinable (R A u :: G) M.
Proof.
  intros V IL.  
  induction IL as [| B v Gr H H0 H1 H2 H3 IH] ; simpl in * ; eauto.
  econstructor 2 ; eauto.
  intros [D | D] ; [inv D| ] ; auto.
Qed.

(** ** if-part **)

Lemma der_inlL_G' M G A u :
  R A u el (inlL M G) -> der (M ++ G) A u.
Proof.
  revert G u.
  induction M as [| [B v] Mr IHMr] ; intros G u D ; simpl in * ; eauto.
  unfold substG in D.
  apply in_map_iff in D.
  destruct D as [[B' u'] [D1 D2]].  
  inv D1. specialize (IHMr G u' D2).
  eapply der_subset with (G2 := R B v :: Mr ++ G) in IHMr ; auto.
  rewrite derT_der_equiv in *.
  eapply derT_trans ; eauto.
  now apply substL_der.
Qed.

Lemma der_inlL_G M G A u :
  der (inlL M G) A u -> der (M ++ G) A u.
Proof.
  induction 1 ; eauto using der_inlL_G'.
Qed.

(** ** only-if-part **)

Lemma inlL_skip G Gr A u :
  disjoint u (dom G) -> inlL G (R A u :: Gr) = R A u :: inlL G Gr.
Proof.
  intros D.
  induction G as [| [B v] G' IHG'] ; simpl in * ; auto.
  assert (H0 : disjoint u (dom G')) by (intros [s [U1 U2]] ; apply D ; exists s ; auto).
  rewrite (IHG' H0).
  assert (H1 : ~ Vs B el u) by (intros U ; apply D ; exists (Vs B) ; auto).
  now apply substG_skipRule.
Qed. 

Lemma inlL_dom M G :
  dom (inlL M G) = dom G.
Proof.
  induction M as [| [A u] Mr IHMr] ; simpl in * ; auto.
  now rewrite substG_dom.
Qed. 

Lemma der_G_inlL M G A u :
  inlinable G M -> Vs A el dom G -> disjoint u (dom M) -> der (M ++ G) A u -> der (inlL M G) A u.
Proof.
  revert G.
  induction M as [| [B v] Mr IHMr] ; intros G IL V T D ; simpl in * ; auto.
  inversion IL as [|B' v' G' H H0 H1 H2 H3] ; subst.
  apply der_G_substG ; auto.
  - intros E ; subst. tauto.
  - now rewrite inlL_dom.
  - intros N. apply T. exists (Vs B). auto.
  - rewrite <- inlL_skip ; auto.
    apply IHMr ; simpl ; auto using inlinable_cons.
    + intros [s [U1 U2]]. apply T. exists s. auto.
    + eapply der_subset ; try exact D ; auto.
Qed.

(** corollary **)

Lemma inlL_langauge_equiv G M A u :
  inlinable G M -> Vs A el dom G -> (language (M ++ G) A u <-> language (inlL M G) A u).
Proof.
  intros H0 H1.
  split ; intros [L0 L1] ; split ; auto ; [apply der_G_inlL | apply der_inlL_G] ; auto.
  intros [x [D0 D1]]. apply domG_rule in D1.
  destruct D1 as [B [v [D1 D2]]]. subst.
  destruct (L1 (Vs B) D0) as [t T]. inv T.
Qed.