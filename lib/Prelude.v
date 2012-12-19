Extraction Language Haskell.
 
(* Unit *)

Extract Inductive unit => "()" [ "()" ].

(* functions *)

Definition id {a : Set} : a -> a := fun x => x.
Definition const {a b : Set} : a -> b -> a := fun x _ => x.
Definition flip {a b c : Set} (f : a -> b -> c) : b -> a -> c :=
  fun x y => f y x.

Extract Inlined Constant id => "Prelude.id".
Extract Inlined Constant const => "Prelude.const".
Extract Inlined Constant flip => "Prelude.flip".

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
Extract Inlined Constant not => "Prelude.not".
Extract Inlined Constant otherwise => "otherwise".

(* Maybe *)

Definition Maybe (a : Set) := option a.
Definition Just := Some.
Implicit Arguments None [].
Definition Nothing := None.

Definition maybe {a b : Set} (n : b) (f : a -> b) (m : Maybe a) : b :=
  match m with
    | Just x => f x
    | Nothing => n
  end.


Extract Constant Maybe "a" => "Prelude.Maybe a".
Extract Inlined Constant Just => "Prelude.Just".
Extract Inlined Constant Nothing => "Prelude.Nothing".
Extract Inlined Constant maybe => "Prelude.maybe".

(* Lists *)

Require Import List.
Open Scope list_scope.

Definition List (a : Set) := list a.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Extract Inductive list => "List" [ "[]" "(:)" ].
Extract Constant List "a" => "[a]".

Definition filter := filter.
Implicit Arguments app [A].
Definition concat {A : Type} (l : list (list A)) := fold_right (app (A:=A)) nil l.
Implicit Arguments filter [A].

