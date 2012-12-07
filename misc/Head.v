Module Head.

Require Import Prelude.
Require Import List.
Set Contextual Implicit.

Set Implicit Arguments.

Inductive head_acc ( a : Set ) : List a -> Prop :=
          | head_acc_0 : forall (x : a) (_xs : List a) , head_acc (cons x _xs).

Theorem head_acc_non_0 : forall (a : Set) (x0 : List a) , head_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Unset Implicit Arguments.

Definition head { a : Set } (x0 : List a) (x1 : head_acc x0) : a :=
             match x0 as _y0 return (x0 = _y0) -> a with
               | cons x _xs => fun _h0 => x
               | nil => fun _h0 => False_rec a (head_acc_non_0 x1 _h0)
             end (refl_equal x0).

Definition headTest (x0 : List Bool) : Bool.
refine (match x0 with
          | xs => head (cons True xs) _
        end).
constructor.
Defined.


Check fun {a : Set } (x : a) (xs : List a) => head (rev (cons x xs)) .

Check length.

Require Import Omega.

Lemma reverseHeadExists : 
  forall (a : Set) (xs : list a),
    length xs >= 1 ->
  exists h : a, exists t : list a, 
    rev xs = h :: t.
Proof.
  intros a xs lengthxsnonzero.
  induction xs as [|xsH xsT IHxs].
  (* xs = [] *)
  simpl. simpl in lengthxsnonzero. exfalso. inversion lengthxsnonzero.
  (* xs = xsH :: xsT *)
  destruct xsT as [|xsTh xsTt].
    (* nil          *) simpl. exists xsH. exists nil. reflexivity.
    (* xsTh :: xsTt *) simpl in IHxs. assert (S (length xsTt) >= 1) as H. omega.
                       apply IHxs in H. inversion H as [h H']. inversion H' as [t H''].
                       simpl. exists h. exists (t ++ [xsH]). rewrite -> H''.
                       reflexivity.
Qed.

Definition headReverse {a : Set} (x: a) (xs : List a) : a.
refine (head (rev (x :: xs)) _).
induction xs as [|h t IHt].
(* xs = nil    *) constructor.
(* xs = h :: t *) assert (exists h' : a, exists t' : list a, rev (x :: h :: t) = h' :: t').
apply reverseHeadExists. simpl. omega. inversion H as [h' H']. inversion H' as [t' H''].
rewrite -> H''. constructor.
Qed.

End Head.

Extraction Head.
