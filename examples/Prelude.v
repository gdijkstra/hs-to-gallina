(* Unit *)

Extract Inductive unit => "()" [ "()" ].

(* functions *)

Definition id {a : Set} : a -> a := fun x => x.
Definition const {a b : Set} : a -> b -> a := fun x _ => x.
Definition _compose {a b c : Set} (g : b -> c) (f : a -> b) : a -> c :=
  fun x => g (f x).
(* TODO: add infix operator for compose *)
Definition flip {a b c : Set} (f : a -> b -> c) : b -> a -> c :=
  fun x y => f y x.
Definition _apply {a b : Set} (f : a -> b) (x : a) : b :=
  f x.
(* TODO: add infix operator for apply *)

(* Booleans *)

Require Import Bool.
Open Scope bool_scope.

Definition Bool := bool.
Definition True := true.
Definition False := false.
Definition not := negb.

Definition otherwise := True.

Extract Inlined Constant Bool => "Prelude.Bool".
Extract Inlined Constant False => "Prelude.False".
Extract Inlined Constant True => "Prelude.True".
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

(* Lists *)

Require Import List.
Open Scope list_scope.

Definition List a := list a.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Extract Inductive list => "List" [ "[]" "(:)" ].
Extract Constant List "a" => "[a]".
Extract Inlined Constant app => "(Prelude.++)".

(* Tuples *)

Extract Inductive prod => "(,)" [ "(,)" ].
