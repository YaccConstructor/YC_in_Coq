Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.

Section RA_Definition.
  Record RA := {
    Q' : Type;
    T' : Type;
    N' : Type;
    edges' : Ensemble (Q' * Q');
    subpath' : relation (Q' * Q');
    call' : N' -> Q' * Q';
    edge'symbol' : option (T' + N') -> relation (Q');
    startN' : N';
  }.
  
  Variable ra : RA.

  (* State type *)
  Local Definition Q : Type := Q' ra.
  Definition states : Ensemble Q := Full_set Q.
  Variable state'count : nat.
  Axiom states_is_finite : cardinal Q states state'count.
  
  (* Terminal type *)
  Local Definition T : Type := T' ra.
  Definition terminals : Ensemble T := Full_set T.
  Variable terminal'count : nat.
  Axiom terminals_is_finite : cardinal T terminals terminal'count.
  
  (* Nonterminal type *)
  Local Definition N : Type := N' ra.
  Definition nonterminals : Ensemble N := Full_set N.
  Variable nonterminal'count : nat.
  Axiom nonterminals_is_finite : cardinal N nonterminals nonterminal'count.
  
  (* N -> Q * Q *)
  Definition call : N -> Q * Q := call' ra.
  
  (* Symbol *)
  Definition S : Type := option (T + N).
  Definition symbols : Ensemble S := Full_set S.
  Definition symbol'count : nat := terminal'count + nonterminal'count.
  
  (* Edges *)
  Definition edges : Ensemble (Q * Q) := edges' ra.
  Variable edge'count : nat.
  Axiom edges_is_state_pair : forall x y : Q, In (Q * Q) edges (x, y) -> In Q states x /\ In Q states y.
  Axiom edges_is_finite : cardinal (Q * Q) edges edge'count.
  Definition edge'relation: relation Q := fun x y => In (Q * Q) edges (x, y).
  
  (* Edge -> Symbol *)
  Definition edge'symbol (s : S): relation (Q) := edge'symbol' ra s.
  
  (* Paths *)
  Variable path'count : nat.
  Definition paths'relation : relation Q := clos_refl_trans Q edge'relation.
  Definition paths : Ensemble (Q * Q) := fun xy => paths'relation (fst xy) (snd xy).
  Axiom paths_is_state_pair : forall x y : Q, In (Q * Q) paths (x, y) -> In Q states x /\ In Q states y.
  Axiom paths_is_finite : cardinal (Q * Q) paths path'count.
  Lemma unpair : forall A B : Type, forall x : A * B, (fst x, snd x) = x.
  Proof.
    intros.
    elim x.
    intros.
    unfold fst.
    unfold snd.
    auto.
  Qed.
  Lemma unpair_call : forall A B : Type, forall f : A * B -> Prop, forall x : A * B, f x -> f (fst x, snd x).
  Proof.
    unfold fst.
    unfold snd.
    intro.
    intro.
    intro.
    intro.
    elim x.
    intros.
    exact H.
  Qed.
  Lemma edges_is_path'subpath : Included (Q * Q) edges paths.
  Proof.
    unfold Included.
    unfold In.
    unfold paths.
    unfold paths'relation.
    intros.
    unfold edge'relation.
    apply rt_step.
    unfold In.
    apply unpair_call.
    exact H.
  Qed.
  Lemma paths'relation_is_reflexive : reflexive Q paths'relation.
  Proof.
    unfold reflexive.
    apply rt_refl.
  Qed.
  Lemma paths'relation_is_transitive : transitive Q paths'relation.
  Proof.
    unfold transitive.
    apply rt_trans.
  Qed.
  Lemma paths_is_reflexive: forall x, In (Q * Q) paths (x, x).
  Proof.
    assert (reflexive Q paths'relation <-> forall x, In (Q * Q) paths (x, x)) as eval'reflexive.
    tauto.
    apply paths'relation_is_reflexive.
  Qed.
  
  (* Subpath relation *)
  Inductive subpath: relation (Q * Q) :=
  | edge: forall (ab: Q * Q), In (Q * Q) edges ab -> subpath ab ab
  | refl: forall (ab: Q * Q), subpath ab ab
  | trans: forall x y z : Q * Q, subpath x y -> subpath y z -> subpath x z
  | concat_l: forall (ab: Q * Q), forall x y z : Q, subpath ab (x, y) /\ subpath (y, z) (y, z) -> subpath ab (x, z)
  | concat_r: forall (ab: Q * Q), forall x y z : Q, subpath (x, y) (x, y) /\ subpath ab (y, z) -> subpath ab (x, z).
  
  Theorem subpath_is_reflexive : reflexive (Q * Q) subpath.
  Proof.
    intro.
    apply refl.
  Qed.
  Theorem subpath_is_transitive : transitive (Q * Q) subpath.
  Proof.
    intro.
    intro.
    intro.
    apply trans.
  Qed.
  Theorem subpath_edges : forall x y : Q, In (Q * Q) edges (x, y) -> subpath (x, y) (x, y).
  Proof.
    intros.
    apply edge.
    exact H.
  Qed.
  Theorem subpath_concat_l : forall a b x y z : Q, subpath (a, b) (x, y) /\ subpath (y, z) (y, z) -> subpath (a, b) (x, z).
  Proof.
    intro.
    intro.
    intro.
    intro.
    intro.
    apply concat_l.
  Qed.
  Theorem subpath_concat_r : forall a b x y z : Q, subpath (x, y) (x, y) /\ subpath (a, b) (y, z) -> subpath (a, b) (x, z).
  Proof.
    intro.
    intro.
    intro.
    intro.
    intro.
    apply concat_r.
  Qed.
  
  (* Path -> [Symbol] *)
  Definition path'symbols (s: S): relation Q := fun z w : Q => exists x y : Q, edge'symbol s x y /\ subpath (x, y) (z, w).

  (* Calls *)
  Definition calls : relation N := fun n m : N => exists x y, subpath (call n) (x, y) /\ path'symbols (Some (inr m)) x y.
  Definition closcalls := clos_trans N calls.
  Definition is_nonrecursive := forall x, ~ closcalls x x.
  Definition is_fsa n := forall x y, ~ edge'symbol (Some (inr n)) x y.
  Lemma fsa_is_nr: (forall n, is_fsa n) -> is_nonrecursive.
  Proof.
  Admitted.
End RA_Definition.

Section Input_Definition.
  Variable Char : Type.
  Record LinearInput := {
    current : nat -> Char;
    next : nat -> nat;
  }.
End Input_Definition.

Section GLL_Definition.
  Variable GrammarState : Type.
  Variable StackPos : Type.
  Variable SPPFPos : Type.
  Record GLL_Hundler := {
    position : nat;
    state : GrammarState;
    stack_pos : StackPos;
    sppf : SPPFPos;
  }.
End GLL_Definition.

Section RA_Operations.
End RA_Operations.