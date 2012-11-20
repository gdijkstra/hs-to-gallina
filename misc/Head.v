Module Head.

Require Import Prelude.

Set Contextual Implicit.

Set Implicit Arguments.

Inductive hd_acc ( a : Set ) : List a -> Prop :=
          | hd_acc_0 : forall (x : a) (_xs : List a) , hd_acc (cons x _xs).

Theorem hd_acc_non_0 : forall (a : Set) (x0 : List a) , hd_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Unset Implicit Arguments.

Definition hd { a : Set } (x0 : List a) (x1 : hd_acc x0) : a :=
             match x0 as _y0 return (x0 = _y0) -> a with
               | cons x _xs => fun _h0 => x
               | nil => fun _h0 => False_rec a (hd_acc_non_0 x1 _h0)
             end (refl_equal x0).

Definition headTest (x0 : List Bool) : Bool.
refine (match x0 with
          | xs => hd (cons True xs) _
        end).
constructor.
Defined.

Definition idBool : Bool -> Bool :=
             id.

Definition exampleList : List Bool :=
             cons True nil.

Set Implicit Arguments.

Inductive Zag : Set :=
          | ZagC : Zig -> Zag
          | ZagStop : Zag
          with
          Zig : Set :=
          | ZigC : Zag -> Zig
          | ZigStop : Zig.

Inductive Rose ( a : Set ) : Set :=
          | R : a -> List (Rose a) -> Rose a.

Unset Implicit Arguments.

Definition rose : Rose Bool :=
             R True (cons (R True nil) (cons (R False nil) nil)).

Set Implicit Arguments.

Inductive Pair ( a : Set ) : Set :=
          | P : a -> a -> Pair a.

Inductive Perfect ( a : Set ) : Set :=
          | Z : a -> Perfect a
          | S : Perfect (Pair a) -> Perfect a.

Unset Implicit Arguments.

Definition perfect : Perfect Bool :=
             S (Z (P True True)).

Set Implicit Arguments.

Inductive Nat : Set :=
          | Zero : Nat
          | Succ : Nat -> Nat.

Unset Implicit Arguments.

refine (
fix  (x0 : Zig) : Nat =>

           match x0 with
             | ZigStop => Zero
             | ZigC z => countZagZig z
           end
         with
         countZagZig (x0 : Zag) : Nat :=
           match x0 with
             | ZagStop => Zero
             | ZagC z => countZigZag z
           end
    ).

Fixpoint plus (x0 : Nat) (x1 : Nat) : Nat :=
           match x0, x1 with
             | Zero, x => x
             | Succ k, x => Succ (plus k x)
           end.

Definition test (x0 : Nat) : Bool -> Bool :=
             match x0 with
               | Zero => idBool
               | Succ k => not
             end.

End Head.

Extraction "Head.hs" Head.


