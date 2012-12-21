Module Head.

Require Import Prelude.
Set Contextual Implicit.

Set Implicit Arguments.

Definition headTest (x0 : List Bool) : Bool.
refine (match x0 with
          | xs => head (cons True xs) _
        end).
constructor.
Defined.


Check fun {a : Set } (x : a) (xs : List a) => head (reverse (cons x xs)) .

Check length.

Require Import Omega.

Lemma reverseHeadExists : 
  forall (a : Set) (xs : list a),
    length xs >= 1 ->
  exists h : a, exists t : list a, 
    reverse xs = h :: t.
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
refine (head (reverse (x :: xs)) _).
induction xs as [|h t IHt].
(* xs = nil    *) constructor.
(* xs = h :: t *) assert (exists h' : a, exists t' : list a, reverse (x :: h :: t) = h' :: t').
apply reverseHeadExists. simpl. omega. inversion H as [h' H']. inversion H' as [t' H''].
rewrite -> H''. constructor.
Defined.

End Head.

Extraction Head.
