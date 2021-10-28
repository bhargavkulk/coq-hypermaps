Require Import EqNat.

(** * Hypermaps in Coq *)
(** ** Dimensions
  We define dimensions inductively. As there are only two dimensions to be considered, we just define two branches: 0 and 1.
*)
Inductive dimension: Set :=
| zero: dimension
| one: dimension.

(** We then prove that equality of dimensions is decidable i.e. either two dimensions
    are equal or they are not equal. Logic in Coq is constructive, we need to prove
    seperately, even though it may seem trivial
*)
Theorem eq_dimension_decide: forall p q: dimension,
  {p = q} + {p <> q}.
Proof.
  intros.
  destruct p, q;
  try(left; reflexivity);
  right; intro; discriminate.
Qed.

(** ** Darts
  Darts we simply encode as natural numbers.
*)

Definition dart := nat.
Definition eq_dart_decide := eq_nat_decide.
Definition nil := 0.

(** We set aside 0 for the [nil] dart. We use the [nil] dart for exceptions later on. *)

(** ** Free Maps
  Before going into hypermaps we first define a collection of darts we call a free map.
  We will use this definition of free maps, and some propositions to define hyper maps.
  A Free Map we define inductively as either a empty free map, or a free map with a dart
  inserted into it, or a free map with two darts joined in a specified dimension.
  *)

Inductive free_map: Set :=
(* void(empty) free map *)
| V: free_map
(* inserting dart d into free map f *)
| I(f: free_map)(d: dart): free_map
(* linking darts d1 and d2, of free map f, in dimension d *)
| L(f: free_map)(dim: dimension)(d1 d2: dart): free_map.

(** Then we define [dart_exists] which checks if a dart is in a map *)

Fixpoint dart_exists (d: dart) (f: free_map): Prop :=
  match f with
  | V => False
  | I f' d' => d = d' \/ dart_exists d f'
  | L f' _ _ _ => dart_exists d f'
  end.

(** We then prove decidability of [dart_exists]: either a dart exists in a map,
  or it doesn't
*)

Theorem dart_exists_is_decidable: forall d m,
  {dart_exists d m} + {~dart_exists d m}.
Proof.
  intros.
  induction m; simpl.
  - right. intro. assumption.
  - destruct IHm.
    + left. right. assumption.
    + destruct (eq_dart_decide d d0) as [H1 | H1].
      * apply (eq_nat_eq d d0) in H1.
        left. left. assumption.
      * unfold not in H1.
        right.
        intro.
        destruct H.
        -- apply H1. apply eq_eq_nat. assumption.
        -- apply n. assumption.
  - assumption.
Qed.

Fixpoint A (f: free_map)(k: dimension)(d: dart) :=
  match f with
  | V => nil
  | I f' _ => A f' k d
  | L f' k' d1 d2 =>
      if (eq_dimension_decide k k') then
        if (eq_dart_decide d d1) then
          d2
        else
          A f' k d
      else
        A f' k d
  end.

Fixpoint A_inv (f: free_map)(k: dimension)(d: dart) :=
  match f with
  | V => nil
  | I f' _ => A_inv f' k d
  | L f' k' d1 d2 =>
      if (eq_dimension_decide k k') then
        if (eq_dart_decide d d2) then
          d1
        else
          A_inv f' k d
      else
        A_inv f' k d
  end.

