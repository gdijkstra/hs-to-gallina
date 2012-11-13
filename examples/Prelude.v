(* Booleans *)

Definition Bool := bool.
Definition True := true.
Definition False := false.

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
