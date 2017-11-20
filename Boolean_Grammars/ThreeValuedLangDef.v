(* Require Import List. 
Import ListNotations. 
Require Import Fin.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path ssrfun.


Inductive ter : Type :=
| T : nat -> ter.

Inductive var : Type :=
| V : nat -> var.

Inductive symbol : Type :=
| Ts : ter -> symbol
| Vs : var -> symbol.

Inductive rhs : Type :=
| Con : seq rhs -> rhs
| And : seq rhs -> rhs
| Neg : rhs -> rhs
| Sym : symbol -> rhs.

Definition rule : Type := (var * rhs).

Definition Grammar : Type := seq ter * seq var * seq rule * var.

Section Section1.

  Section Section11.
    
    Let A := nat.
    
    Definition f1 (lst: seq A) := [seq (take x lst, drop x lst) | x <- iota 0 (length lst)].
    
    Fixpoint f2 lst n :=
      match n with
      | 0 => nil
      | 1 => lst
      | S n =>
        let n2 := map (fun x => (fst x, f1 (snd x))) lst in
        let n3 := flatten  (map  (fun x => map (fun y => (fst x ++ [fst y], snd y)) (snd x))  n2) in
        f2 n3 n
      end.
    
    Definition f lst n :=
      let n1 := map (fun x => ([fst x],snd x)) (f1 lst) in
      let res := f2 n1 n in
      map fst (filter (fun x => snd x == []) res).
  
  End Section11.

  Section Section12.

    Definition minimum xs :=
      match xs with
      | nil => 0
      | y::ys => foldl minn y ys
      end.

    Definition maximum xs :=
      match xs with
      | nil => 0
      | y::ys => foldl maxn y ys
      end.  

    Definition concat (langs: seq (seq nat -> nat)) :=
      fun string =>
        maximum 
          (map minimum 
               (map (map (fun x => (fst x) (snd x))) 
                    (map (zip langs) 
                         (f string (length langs))))).

  End Section12.
  
End Section1.

Section Section2.

  Let A := nat.

  Definition Interpretation : Type := var -> seq A -> nat.
  Definition ExtendedInterpretation : Type := rhs -> seq A -> nat.
  
  Definition extendedInterpretation (interpretation: Interpretation): ExtendedInterpretation :=
    let fix intExtHelp (r: rhs) :=
        match r with
        | And nil => fun (string: seq A) => if string == nil then 2 else 0
        | Con nil => fun (string: seq A) => if string == nil then 2 else 0
        | Sym (Ts (T a)) => fun (string: seq A) => if string == [::a] then 2 else 0
        | Sym (Vs a) => fun (string: seq A) => interpretation a string
        | Con rs => fun (string: seq A) => concat (map intExtHelp rs) string
        | Neg r => fun string => 2 - intExtHelp r string
        | And rs => fun (string: seq A) => minimum (map (fun r => intExtHelp r string) rs)
        end in
    fun rhs string => intExtHelp rhs string.

End Section2.

Section Section3.

  Definition isNegative rhs :=
    match rhs with
    | Neg _ => true
    | _ => false
    end.
  Definition isPositive rhs := ~~ (isNegative rhs).
  
End Section3.

Section Section4.

  Definition eq_r nt (rule: rule) :=
    let (lhs,_) := rule in
    match nt, lhs with
    | V n, V lh => n == lh
    end.
                   
  Definition theta (grammar: Grammar) (intJ: Interpretation) :=
    fun intI nt string =>
      let '(ts, nts, rules, ss) := grammar in
      let extIntI := extendedInterpretation intI in 
      let extIntJ := extendedInterpretation intJ in 
      let rhss := map snd (filter (fun rule => eq_r nt rule) rules) in
     
      let res1 :=
          has
            (fun rhs =>
               match rhs with
               | And rhs1 =>
                 let posAts := filter isPositive rhs1 in 
                 let negAts := filter isNegative rhs1 in 
                 all (fun li => extIntI li string == 2) posAts && all (fun li => extIntJ li string == 2) negAts
               | Neg rhs => extIntJ (Neg rhs) string == 2
               | rhs => extIntI rhs string == 2 
               end
            ) rhss in 

      let res2 :=
          all
            (fun rhs => 
               match rhs with 
               | And rhs1=> 
                 let posAts := filter isPositive rhs1 in 
                 let negAts := filter isNegative rhs1 in 
                 has (fun li => extIntI li string == 0) posAts || has (fun li => extIntJ li string == 0) negAts
               | Neg rhs => extIntJ (Neg rhs) string == 0
               | rhs => extIntI rhs string == 0
               end
            ) rhss in     

      if res1 then 2 else if res2 then 0 else 1.

  Definition botIntT (nt: var) := fun (string: seq nat) => 0.
  Definition botIntI (nt: var) := fun (string: seq nat) => 1.
  
  Fixpoint omeg (grammar: Grammar) (interp: Interpretation) (n: nat): Interpretation :=
    match n with
    | 0 => botIntT
    | S n => theta grammar interp (omeg grammar interp n)
    end.

  Fixpoint m (grammar: Grammar) (n k: nat): Interpretation :=
    match n with
    | 0 => botIntI
    | S n => omeg grammar (m grammar n k) k
    end.

End Section4.

Section WW.

  Definition ww: Grammar:=
    (nil,
     nil,
     [
       (V 0,
        And [
            Neg (Con [Sym (Vs (V 1)); Sym (Vs (V 2))]);
              Neg (Con [Sym (Vs (V 2)); Sym (Vs (V 1))]);
              Neg (Sym (Vs (V 1)));
              Neg (Sym (Vs (V 2)))]);
       (V 1, And [Sym (Ts (T 0))]);
       (V 1, And [Con [Sym (Vs (V 3)); Sym (Vs (V 1)); Sym (Vs (V 3))]]);
       (V 2, And [Sym (Ts (T 1))]);  
       (V 2, And [Con [Sym (Vs (V 3)); Sym (Vs (V 2)); Sym (Vs (V 3))]]);
       (V 3, And [Sym (Ts (T 0))]);
       (V 3, And [Sym (Ts (T 1))])
     ],
     V 0). 

  Example example1:
    (m ww 2 2) (V 0) [0;0;1; 0;0;1] == 2.
  Proof. by done. Qed.

  Lemma lemma1:
    forall lst,
      lst = [::0] \/ lst = [::1] <-> (m ww 1 1) (V 3) lst == 2.
  Proof.
    intros lst .
    split; [move => [H|H]| move => H].
    - subst lst. by done.
    - subst lst. by done.
    - destruct lst; first by done.
      destruct lst; first destruct n.
      left. by done.
      right. destruct n. by done. simpl in H. by done.
      simpl in H. admit.
  Admitted.

  Lemma lemma2:
    forall lst lst1 lst2,
      (m ww 1 1) (V 2) lst == 2 <-> lst = lst1 ++ [::1] ++ lst2.
  Proof.
  Admitted.

  Lemma lemma3:
    forall lst lst1 lst2,
      (m ww 1 1) (V 1) lst == 2 <-> lst = lst1 ++ [::0] ++ lst2.
  Proof.
  Admitted. 

  Lemma lemma4:
    forall lst lst',
      (m ww 2 2) (V 0) lst == 2 <-> lst = lst' ++ lst'. 
  Proof.
    intros.
    split; intros.
    admit.
    subst lst.
    simpl.
   Admitted.   
    
  Example example2:
    forall lst, exists k, (m ww k k) (V 0) (lst ++ lst) == 2.
  Proof.
    intros.
    induction lst.
    - exists 2. by done.
  Admitted.
  
End SectionName5. *)
