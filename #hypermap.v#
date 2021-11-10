Require Import Decidable PeanoNat.
Require Eqdep_dec.
Local Open Scope nat_scope.
Notation eq_nat_dec := Nat.eq_dec (only parsing).

Inductive dim : Set := 
 | zero : dim
 | one  : dim.



Lemma eq_dim_dec : forall (i:dim)(j:dim),
 {i=j} + {~i=j}.

Proof.
  intros i.
  induction i as [zero|one].
  (*Case "i = 0".*)
    -intros j.
    destruct j as [zero|one].
    (*SCase "j = 0".*)
      --left. reflexivity.
    (* SCase "j = 1". *)
      --right. intros contra. inversion contra.
  (*Case "i = 1".*)
    -intros j.
    destruct j as [zero|one].
    (*SCase "j = 0".*)
      --right. intros contra. inversion contra.
    (*SCase "j = 1 ".*)
      --left. reflexivity.
Defined.

Definition dart := nat.
Definition eq_dart_dec := eq_nat_dec.
Definition point:= nat. (*(nat * nat)%type.*)
Definition nil := 0.

Inductive fmap : Set :=
V : fmap
| I : fmap -> dart -> point -> fmap
| L : fmap -> dim -> dart -> dart -> fmap.

Fixpoint exd (m:fmap)(d:dart) {struct m} : Prop :=
match m with
V => False
| I m0 x _ => x = d \/ exd m0 d
| L m0 _ _ _ => exd m0 d
end.

Fixpoint A (m:fmap)(k:dim)(d:dart) {struct m} : dart :=
match m with
V => nil
| I m0 _ _ => A m0 k d
| L m0 k0 x y =>
if eq_dim_dec k k0 
  then if eq_dart_dec x d 
          then y 
       else 
          A m0 k d
else A m0 k d
end.

Compute (A (L (L (L (I (I (I (I V 3 3) 2 2) 10 10) 9 9) zero 3 2) one 2 10) zero 10 9) zero 3).

Fixpoint A_1 (m:fmap)(k:dim)(d:dart) {struct m} : dart :=
match m with
V => nil
| I m0 _ _ => A_1 m0 k d
| L m0 k0 x y =>
if eq_dim_dec k k0 then
  if eq_dart_dec y d then x else A_1 m0 k d
else A_1 m0 k d
end.
 
Definition succ (m:fmap)(k:dim)(d:dart) : Prop := 
  A m k d <> nil.
Definition pred (m:fmap)(k:dim)(d:dart) : Prop := 
  A_1 m k d <> nil.

Definition prec_I (m:fmap)(x:dart) : Prop :=
x <> nil /\ ~ exd m x.

Definition prec_L (m:fmap)(k:dim)(x:dart)(y:dart) : Prop :=
exd m x /\ exd m y /\~ succ m k x /\ ~ pred m k y /\ A m k x <> y.

Fixpoint inv_hmap (m:fmap) : Prop :=
match m with
V => True
| I m0 x p => inv_hmap m0 /\ prec_I m0 x
| L m0 k x y => inv_hmap m0 /\ prec_L m0 k x y
end.







