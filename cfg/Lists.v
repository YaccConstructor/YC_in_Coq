Require Export fl.cfg.Base.

Module Lists.

  Import Base.
  
  Section Lists.
    (** * Decidability instances *)

    Global Instance eq_dec_prod X Y (Dx : eq_dec X) (Dy : eq_dec Y) :
      eq_dec (X * Y).
    Proof.
      intros [x y] [x' y'].
      decide (x = x') ; decide (y = y') ; try (right ; intros H ; inv H ; tauto).
      left. f_equal ; auto.
    Defined.

    Global Instance filter_prod_dec X Y {D : eq_dec X} (x : X) :
      forall (e : X * Y) , dec ((fun e : X * Y => match e with (xe, _) => x = xe end) e).
    Proof.
      intros [xe _]. auto.
    Defined.

    Global Instance splitList_dec X (D : eq_dec X) (xs ys : list X) : dec (exists zs, xs = ys ++ zs).
    Proof.
      revert xs.
      induction ys as [| s ys IHv]; intros xs.
      - left. exists xs. auto.
      - destruct xs as [|s' xs].
        + right. intros [zs H]. inv H. 
        + decide (s = s') as [DS | DS].
          * rewrite DS.
            destruct (IHv xs) as [IH | IH].
            { left. destruct IH as [zs IH]. exists zs. rewrite IH. auto. }
            { right. intros [zs H]. simpl in H.
              apply IH. exists zs. now inv H. }
          * right. intros [zs H]. inv H. tauto.
    Defined.

    (** * Sublists **)

    Fixpoint slists (X : Type) (p : X -> Prop) {pdec : forall x, dec (p x)} (xs : list X) : list (list X) :=
      match xs with
        | [] => [[]]
        | s::xs' =>
          let
            ys := @slists _ _ pdec xs'
          in let
            zs := map (cons s) ys
          in
          if decision (p s) then ys ++ zs else zs
      end.
    Arguments slists {X} p {pdec} xs.

    Inductive slist (X : Type) (p : X -> Prop) {pdec : forall x, dec (p x)} : list X -> list X -> Prop :=
    | subnil : slist nil nil
    | subconsp s ys xs: p s -> slist ys xs -> slist ys (s :: xs)
    | subcons s ys xs : slist ys xs -> slist (s :: ys) (s :: xs).
    Arguments slist {X} p {pdec} ys xs.
    Hint Constructors slist.

    Lemma slists_slist (X : Type) (xs ys : list X) (p : X -> Prop) (D : forall x, dec (p x)) :
      ys el slists p  xs <-> slist p ys xs.
    Proof. 
      split.
      - revert ys.
        induction xs as [| s xs' IHu] ; intros ys H ; simpl in H.
        + destruct H as [H | H] ; [ rewrite <- H ; constructor | tauto ].
        + decide (p s) ; [ apply in_app_iff in H ; destruct H as [H | H] | ] ; auto; (apply in_map_iff in H ; destruct H as [ys' [H0 H1]] ; subst ; auto).
      - induction 1 as [| s ys xs H H0 IH | s ys xs H IH] ; simpl ; auto.
        * decide (p s) ; firstorder.
        * assert (H1: exists ys', s::ys' = s::ys /\ ys' el (slists p xs)) by firstorder.
          rewrite <- in_map_iff in H1.
          decide (p s) ; [ apply in_app_iff |  ] ; auto.
    Qed.

    (** ** Properties of sublists **)

    Lemma slist_id (X : Type) (xs : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} :
      slist p xs xs.
    Proof.
      induction xs ; auto.
    Qed.  

    Lemma slist_trans (X : Type) (xs ys zs : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} :
      slist p zs ys -> slist p ys xs -> slist p zs xs.
    Proof. 
      intros H1. revert xs.
      induction H1 as [| s ys xs H H0 IH | s ys xs H IH] ; intros xs' H2 ; try now auto ; auto; (remember (s :: xs) as zs ; induction H2 ; [congruence | | inv Heqzs ] ; auto).
    Qed.

    Lemma slist_append  (X : Type) (xs1 xs2 ys1 ys2 : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} :
      slist p ys1 xs1 -> slist p ys2 xs2 -> slist p (ys1 ++ ys2) (xs1 ++ xs2).
    Proof.
      induction 1 ; simpl ; auto.
    Qed.
    
    Lemma slist_equiv_pred (X : Type) (xs ys : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} (p' : X -> Prop) {pdec' : forall x, dec (p' x)}:
      (forall x, p x <-> p' x) -> slist p xs ys -> slist p' xs ys.
    Proof.
      induction 2 ; auto.
      constructor 2 ; firstorder.
    Qed.

    Lemma slist_inv (X : Type) (xs ys : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} :
      slist p ys xs -> (forall s, s el ys -> p s) -> forall s, s el xs -> p s.
    Proof. 
      intros H0 H1 s E.
      induction H0 ; auto; (destruct E as [E | E] ; try rewrite <- E ; auto).
    Qed.

    Lemma slist_split (X : Type) (xs ys : list X) (p : X -> Prop) {pdec : forall x, dec (p x)} :
      slist p ys xs -> forall xs1 xs2, xs = xs1 ++ xs2 -> exists ys1 ys2, slist p ys1 xs1 /\ slist p ys2 xs2 /\ ys = ys1 ++ ys2.
    Proof. 
      induction 1 as [ | s ys xs H H0 IH | s ys xs H IH] ; intros xs1 xs2 U.
      - exists [], [].
        symmetry in U.
        apply app_eq_nil in U ; destruct U as [H1 U].
        rewrite H1, U. repeat split ; auto.
      - destruct xs1, xs2 ; simpl in U ; (try now inv U) ; injection U ; intros U0 U1 ; subst.
        + destruct (IH [] xs2 eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists ys1, ys2; (repeat split ; auto ; try inv IH0 ; auto).
        + destruct (IH xs1 [] eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists ys1, ys2; (repeat split ; auto ; try inv IH0 ; auto).
        + destruct (IH xs1 (x0 :: xs2) eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists ys1, ys2; (repeat split ; auto ; try inv IH0 ; auto).
      - destruct xs1, xs2 ; simpl in U ; (try now inv U) ; injection U ; intros U0 U1 ; subst.
        + destruct (IH [] xs2 eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists ys1, (x :: ys2);(repeat split ; auto ; try inv IH0 ; auto).
        + destruct (IH xs1 [] eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists (x :: ys1), ys2; (repeat split ; auto ; try inv IH0 ; auto).
        + destruct (IH xs1 (x0 :: xs2) eq_refl) as [ys1 [ys2 [IH0 [IH1 IH2]]]]. exists (x :: ys1), ys2; (repeat split ; auto ; try inv IH0 ; auto).
    Qed.


    Lemma slist_subsumes X (p : X -> Prop) {D : forall x, dec (p x)} xs ys :
      slist p xs ys -> xs <<= ys.
    Proof.
      induction 1 ; auto.
    Qed.

    Lemma slist_length X (p : X -> Prop) {D : forall x, dec (p x)} (xs ys : list X) :
      slist p xs ys -> |xs| <= |ys|.
    Proof.
      induction 1 ; simpl ; omega.
    Qed.

    Lemma slist_pred X (p p' : X -> Prop) {D : forall x, dec (p' x)} (xs ys : list X)  :
      slist p' xs ys -> (forall y, y el ys -> p y) -> forall x, x el xs -> p x.
    Proof.
      intros Ss P.
      induction Ss ; intros x' E ; auto.
      destruct E as [E | E] ; auto.
      rewrite <- E. now apply P.
    Qed.


    (** * Segments *)

    Definition segment X (xs ys : list X) := exists xs1 xs2, xs = xs1 ++ ys ++ xs2.

    Fixpoint segms {X} {D : eq_dec X} (xs : list X) :=
      match xs with
          [] => [ [] ]
        | s :: xs =>
          let
            Ss := segms xs
          in
          map (cons s) (filter (fun ys => exists zs, xs = ys ++ zs) Ss) ++ Ss
      end.
    Arguments segms {X} {D} xs.

    (** ** Properties of segments *)

    Lemma segment_nil X {D : eq_dec X} (xs : list X) :
      segment xs [].
    Proof.
      exists xs, []. now rewrite app_nil_r.
    Qed.

    Lemma segment_refl X {D : eq_dec X} (xs : list X) :
      segment xs xs.
    Proof.
      exists [], []. rewrite app_nil_r. auto.
    Qed.

    Lemma segment_trans X {D : eq_dec X} (xs ys zs : list X) :
      segment ys zs -> segment xs ys -> segment xs zs.
    Proof.
      intros [w1 [w2 H0]] [ys1 [ys2 H1]].
      exists (ys1 ++ w1), (w2 ++ ys2). rewrite H1, H0.
      now repeat rewrite <- app_assoc.
    Qed.

    (** ** Equivalence of segment characterizations *)

    Lemma segms_corr1 X {D : eq_dec X} (xs ys : list X) :
      segment xs ys -> ys el segms xs.
    Proof.
      revert ys.
      induction xs as [| s xs IHxs] ; intros ys [ys1 [ys2 H]].
      - simpl. symmetry in H.
        apply app_eq_nil in H.
        destruct H as [H0 H]. apply app_eq_nil in H.
        destruct H as [H1 H2]. subst. auto.
      - destruct ys1 as [| sys1 ys1] ; simpl in H.
        + destruct ys as [| sys ys] ; simpl in H.
          { simpl. apply in_or_app. right. apply IHxs. now apply segment_nil. }
          { injection H ; intros H0 H1 ; subst.
            simpl. apply in_or_app. left. apply in_map_iff.
            exists ys. split ; auto. apply in_filter_iff. split.
            - apply IHxs. exists [], ys2. auto.
            - now (exists ys2). }
        + injection H ; intros H0 H1 ; subst.
          simpl. apply in_or_app. right. apply IHxs.
          now (exists ys1, ys2).
    Qed.      
    
    Lemma segms_corr2 X {D : eq_dec X} (xs ys : list X) :
      ys el segms xs -> segment xs ys.
    Proof.
      intros H.
      induction xs as [| s xs IHxs] ; simpl in H.
      - destruct H as [H | H] ; [subst | tauto].
        now (exists [], []).    
      - apply in_app_iff in H.
        destruct H as [H | H].
        + apply in_map_iff in H. destruct H as [x [H0 H1]].
          apply in_filter_iff in H1. destruct H1 as [H1 [zs H2]].
          rewrite <- H0, H2 in *.
          exists [], zs. auto.
        + destruct (IHxs H) as [x [z IH]].
          exists (s :: x), z. rewrite IH. auto.
    Qed.    

    Lemma segms_corr X {D : eq_dec X} (xs ys : list X) :
      ys el segms xs <-> segment xs ys.
    Proof.
      split ; intros Ss ; [eapply segms_corr2 | eapply segms_corr1]  ; eauto.
    Qed.


    (** * General functions on lists *)

    (** ** Product *)

    Fixpoint product X Y Z (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
      match xs with
          [] => []
        | s :: xs => map (f s) ys ++ product f xs ys
      end.

    Lemma prod_corr1 X Y Z (f : X -> Y -> Z) (xs : list X) (ys : list Y) (z : Z) :
      z el product f xs ys -> exists sxs sys, f sxs sys = z /\ sxs el xs /\ sys el ys.
    Proof.
      intros H.
      induction xs as [| s xs IHxs ] ; simpl in H ; try tauto.
      apply in_app_iff in H.
      destruct H as [H | H].
      - apply in_map_iff in H.
        destruct H as [x [H0 H1]].
        exists s, x. repeat split ; auto.
      - destruct (IHxs H) as [sxs [sys [H0 [H1 H2]]]].
        exists sxs, sys. auto.
    Qed.
    
    Lemma prod_corr2 X Y Z (f : X -> Y -> Z) (xs : list X) (ys : list Y) (z : Z) :
      (exists sxs sys, f sxs sys = z /\ sxs el xs /\ sys el ys) -> z el product f xs ys.
    Proof.
      intros [sxs [sys [H0 [H1 H2]]]].
      induction xs as [| s xs IHxs ] ; try now inv H1.
      simpl. apply in_app_iff.
      destruct H1 as [H1 | H1].
      - rewrite H1 in *. left. apply in_map_iff. exists sys. auto.
      - right. auto.
    Qed.  

    Lemma prod_corr X Y Z (f : X -> Y -> Z) (xs : list X) (ys : list Y) (z : Z) :
      z el product f xs ys <-> exists sxs sys, f sxs sys = z /\ sxs el xs /\ sys el ys.
    Proof.
      split ; [apply prod_corr1 | apply prod_corr2].
    Qed.

    (** ** Projection **)
    Fixpoint fsts X Y (xs : list (X * Y)) :=
      match xs with
          [] => []
        | (x, y) :: xs => x :: fsts xs
      end.

    Lemma fsts_split X Y (xs ys : list (X * Y)) :
      fsts (xs ++ ys) = fsts xs ++ fsts ys.
    Proof.
      induction xs as [| [s1 s2] xs IHxs] ; simpl ; auto.
      now rewrite IHxs.
    Qed.

    Fixpoint snds X Y (xs : list (X * Y)) :=
      match xs with
          [] => []
        | (x, y) :: xs => y :: snds xs
      end.

    Lemma snds_split X Y (xs ys : list (X * Y)) :
      snds (xs ++ ys) = snds xs ++ snds ys.
    Proof.
      induction xs as [| [s1 s2] xs IHxs] ; simpl ; auto.
      now rewrite IHxs.
    Qed.

    (** ** Concat*)
    Fixpoint concat X (xs : list (list X)) :=
      match xs with
          [] => []
        | ys :: xs => ys ++ (concat xs)
      end.

    Lemma concat_split X (xs ys : list (list X)) :
      concat (xs ++ ys) = concat xs ++ concat ys.
    Proof.
      induction xs ; simpl ; [| rewrite IHxs] ; auto using app_assoc.
    Qed.

    (** ** Substitution**)
    Fixpoint substL X {D : eq_dec X} (xs : list X) (y : X) (ys : list X) :=
      match xs with
          [] => []
        | x :: xs => if decision (x = y) then ys ++ substL xs y ys else x :: substL xs y ys
      end.

    Lemma substL_split X {D : eq_dec X} (xs1 xs2 : list X) (y : X) (ys : list X) :
      substL (xs1 ++ xs2) y ys = substL xs1 y ys ++ substL xs2 y ys.
    Proof.
      induction xs1 as [| sxs1 xs1 IHxs1] ; simpl ; try (decide (sxs1 = y) ; rewrite IHxs1) ; auto using app_assoc.
    Qed.

    Lemma substL_skip X {D : eq_dec X} (xs : list X) (y : X) (ys : list X) :
      ~ y el xs -> substL xs y ys = xs.
    Proof.
      intros U.
      induction xs as [| x xs IHxs] ; simpl in * ; auto.
      decide (x = y) as [D0 | D0].
      - exfalso. apply U ; auto.
      - f_equal. apply IHxs.
        intros H. apply U. auto.
    Qed.

    Lemma substL_length_unit X {D : eq_dec X} (xs : list X) (x x' : X) :
      (|xs|) = | substL xs x [x'] |.
    Proof.
      induction xs as [| y xr IHxr] ; simpl ; try decide (y = x) ; simpl ; auto.
    Qed.

    Lemma substL_undo X {D : eq_dec X} (xs : list X) (x x' : X) :
      ~ x' el xs -> substL (substL xs x [x']) x' [x] = xs.
    Proof.
      intros H.
      induction xs as [| y xr IHxr] ; simpl ; auto.
      simpl. decide (y = x) as [D0 | D0] ; subst ; simpl.
      - decide (x' = x') ; try tauto. f_equal. auto.
      - decide (y = x') ; subst.
        + exfalso. now apply H. 
        + f_equal. auto.
    Qed.

    (** ** General lemmas on lists **)
    Lemma list_unit (X : Type) (xs zs : list X) (x y : X) :
      [x] = xs ++ y :: zs -> xs = [] /\ zs = [] /\ x = y.
    Proof.
      intros H.
      destruct xs, zs ; (try now inv H ; auto) ; (injection H ; intros H0 H1 ; subst;
                                                  symmetry in H0 ; apply app_eq_nil in H0 ; destruct H0 ; congruence).
    Qed.
    
  End Lists.

End Lists.