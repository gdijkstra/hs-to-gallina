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

End Head.

Extraction "Head.hs" Head.


