Require Import List.

Add LoadPath "..". 
Require Import CFG.Definitions.
 
Module Base.
 
  Import Definitions.
  
  Section Definitions. 

    Context {Tt Vt: Type}.
    
    Definition word := list (@ter Tt).

    Definition language := word -> Prop.

    Definition language_union (l1 l2 : language) := fun w => (l1 w) \/ (l2 w).

    Definition language_intersection (l1 l2 : language) := fun w => (l1 w) /\ (l2 w).

    Definition language_eq (l1  l2 : language) := forall w : word, l1 w <-> l2 w. 

    Notation "l1 [\/] l2" := (language_union l1 l2) (at level 85).
    Notation "l1 [/\] l2" := (language_intersection l1 l2) (at level 80).
    Notation "l1 [==] l2" := (language_eq l1 l2) (at level 90).

  End Definitions.
  
  Section Lemmas.

     Context {Tt Vt: Type}.
    (* TODO: del *)
    Notation "l1 [\/] l2" := (language_union l1 l2) (at level 85).
    Notation "l1 [/\] l2" := (language_intersection l1 l2) (at level 80).
    Notation "l1 [==] l2" := (language_eq l1 l2) (at level 90).
    
    Lemma mk_laguage_eq :
      forall (l1 l2 : @language Tt),
        (forall w, l1 w -> l2 w) ->
        (forall w, l2 w -> l1 w) -> l1 [==] l2. 
    Proof.
      intros l1 l2 H1 H2.
      unfold language_eq.
      intro w.
      split.
      apply (H1 w).
      apply (H2 w).
    Qed.
    
    Theorem lang_distr : forall l1 l2 l3 : (@language Tt),
                           l1 [/\] (l2 [\/] l3) [==] (l1 [/\] l2) [\/] (l1 [/\] l3).
    Proof.
      intros.
      apply mk_laguage_eq.
      intros w H.   
      unfold language_intersection in H.
      destruct H.
      unfold language_union in *.
      destruct H0.
      left.
      unfold language_intersection.
      intuition.
      right.
      unfold language_intersection.
      intuition.

      intros w H.
      unfold language_union in H.
      destruct H.
      unfold language_intersection in H.
      destruct H.
      unfold language_intersection.
      split.
      exact H.
      unfold language_union.
      left.
      exact H0.
      unfold language_intersection in H.
      unfold language_intersection.
      destruct H.
      split.
      
      exact H.
      unfold language_union.
      right.
      exact H0.
    Qed.


    Fixpoint language_list_union (l : list (@language Tt)) := fun w =>
                                                          match l with
                                                            | nil => False
                                                            | h :: t => (h w) \/ language_list_union t w
                                                          end.

    Theorem lang_distr_2 : forall (l2 : language) (ls : list language),
                             (l2 [/\] (language_list_union ls)) [==]
                                                               (language_list_union (map (fun l => l2 [/\] l) ls)).
    Proof.
      intros l2 ls.
      unfold language_eq.
      intros w.
      split.
      elim ls.
      intros H0.
      unfold language_intersection in H0.
      destruct H0.
      auto.
      intros a tail.
      intro HR.
      intro LI.
      simpl.
      unfold language_intersection in LI.
      simpl language_list_union in LI.
      destruct LI as [l2_w H1].
      elim H1.
      intro.
      left.
      unfold language_intersection.
      apply (conj l2_w H).
      intro.
      right.
      apply HR.
      unfold language_intersection.
      apply (conj l2_w H).
      elim ls.
      simpl.
      intros F; case F.
      clear ls.
      intros LA ls H0 LU.
      simpl language_list_union in LU.
      case LU.
      intro H1.
      unfold language_intersection.
      unfold language_intersection in H1.
      destruct H1.
      split.
      exact H.
      simpl language_list_union.
      left; exact H1.
      intro.
      apply H0 in H.
      unfold language_intersection.
      simpl language_list_union.
      assert(distr : forall (a b c : Prop), (a /\ c) -> a /\ (b \/ c)).
      intros.
      destruct H1.
      auto.
      apply distr.
      unfold language_intersection in H.
      exact H.
    Qed.
    
  End Lemmas.
  
End Base.