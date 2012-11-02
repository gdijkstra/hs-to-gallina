Module BC.

Inductive Nat : Set :=
                      | Zero : Nat
                      | Succ : Nat -> Nat.

Fixpoint div2 (x0 : Nat) : Nat :=
           match x0 with
             | Zero => Zero
             | Succ Zero => Zero
             | Succ (Succ n) => Succ (div2 n)
           end.

Inductive log_accRelevant : Nat -> Set :=
| log_accRelevant_0 : log_accRelevant (Succ Zero)
| log_accRelevant_1 : forall p : Nat , log_accRelevant (Succ (div2 p)) -> log_accRelevant (Succ (Succ p)).

Fixpoint logRelevant (x0 : Nat) (h : log_accRelevant x0) : Nat :=
  match h with
    | log_accRelevant_0 => Zero (* | Succ Zero => Zero *)
    | log_accRelevant_1 p h0 => Succ (logRelevant (Succ (div2 p)) h0) (* | Succ (Succ p) => Succ (log' (Succ (div2 p))) *)
  end.

Inductive log_accIrrelevant : Nat -> Prop :=
| log_accIrrelevant_0 : log_accIrrelevant (Succ Zero)
| log_accIrrelevant_1 : forall p : Nat , log_accIrrelevant (Succ (div2 p)) -> log_accIrrelevant (Succ (Succ p)).

Theorem log_domain_non_zero : forall x : Nat, log_accIrrelevant x -> x <> Zero.
Proof.
  intros x H. inversion H; discriminate.
Qed.

Theorem log_domain_inv :
  forall x p : Nat, log_accIrrelevant x 
                    -> x = Succ (Succ p)
                    -> log_accIrrelevant (Succ (div2 p)).
Proof.
  intros x p h0 heq. inversion h0. rewrite -> heq in H. inversion H.
  rewrite -> heq in H0. inversion H0. rewrite -> H2 in H. assumption.
Defined.

Print log_domain_inv.

Fixpoint logIrrelevant (x0 : Nat) (h : log_accIrrelevant x0) : Nat :=
  match x0 as y return x0 = y -> Nat with
    | Zero => fun h' => False_rec Nat (log_domain_non_zero x0 h h')
    | Succ Zero => fun h' => Zero
    | Succ (Succ p) => fun h' => Succ (logIrrelevant (Succ (div2 p)) (log_domain_inv x0 p h h'))
  end (refl_equal x0).

Theorem log_domain_inv2 :
  forall x p : Nat, log_accIrrelevant (Succ (Succ p))
                    -> log_accIrrelevant (Succ (div2 p)).
Proof.
  admit.
Defined.

(* Fixpoint logIrrelevant2 (x0 : Nat) (h : log_accIrrelevant x0) : Nat := *)
(*   match x0 as y return (match y with *)
(*                         | Zero => unit *)
(*                         | Succ Zero => Nat *)
(*                         | Succ (Succ p) => Nat *)
(*                         end) with *)
(*     | Zero => tt *)
(*     | Succ Zero => Zero *)
(*     | Succ (Succ p) => Succ (logIrrelevant2 (Succ (div2 p)) (log_domain_inv2 x0 p h)) *)
(*   end. *)


Function test (x0 x1 : Nat) : Nat :=
  match x0, x1 with
      | Zero, _ => Zero
      | _, Zero => Succ Zero
      | Succ _, Succ _ => Succ Zero
  end.


Set Implicit Arguments.

End BC.

Extraction Language Haskell.
Set Extraction Optimize.
Recursive Extraction BC.

