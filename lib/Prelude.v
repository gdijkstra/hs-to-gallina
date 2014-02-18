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

(* naturals *)

Extract Inductive nat => Int [ "0" "Prelude.succ" ].

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
Extract Inlined Constant otherwise => "Prelude.otherwise".

(* Maybe *)

Inductive Maybe (a : Set) : Set :=
  | Just : a -> Maybe a
  | Nothing : Maybe a.

Definition maybe {a b : Set} (n : b) (f : a -> b) (m : Maybe a) : b :=
  match m with
    | Just x => f x
    | Nothing => n
  end.

Extract Inductive Maybe => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inlined Constant maybe => "Prelude.maybe".

(* Either *)

Inductive Either (a b : Set) : Set :=
  | Left : a -> Either a b
  | Right : b -> Either a b.  

Arguments Left {a b} _.
Arguments Right {a b} _.

Definition either {a b c : Set} (f : a -> c) (g : b -> c) (e : Either a b) : c :=
  match e with
    | Left x => f x
    | Right y => g y
  end.

(* Extract Constant Either "a" "b" => "Prelude.Either a b". *)
Extract Inductive Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inlined Constant either => "Prelude.either".

(* Ordering *)

Inductive Ordering : Set :=
| LT : Ordering
| EQ : Ordering
| GT : Ordering.

Extract Inductive Ordering => "Prelude.Ordering" [ "Prelude.LT" "Prelude.EQ" "Prelude.GT" ].

(* Lists *)

Require Import List.
Open Scope list_scope.

Definition List (a : Set) := list a.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Extract Inductive list => "List" [ "[]" "(:)" ].
Extract Constant List "a" => "[a]".

Definition map := map.
Definition filter := filter.
Definition concat {a : Set} (l : list (list a)) : list a := fold_right (app (A:=a)) nil l.
Definition concatMap {a b : Set} (f : a -> list b) : list a -> list b := fun xs : list a => concat (map a (list b) f xs).

Definition null {a : Set} (l : list a) : Bool :=
  match l with
    | [] => True
    | _ :: _ => False
  end.

Definition length := length.

Definition foldl {a b : Set} (f : a -> b -> a) (z : a) (l : list b) : a := fold_left f l z.

Fixpoint scanl {a b : Set} (f : a -> b -> a) (q : a) (l : list b) : list a := 
  q :: match l with
           | [] => []
           | x :: xs => scanl f (f q x) xs
       end.

Definition scanl1 {a : Set} (f : a -> a -> a) (l : list a) : list a :=
  match l with
    | x :: xs => scanl f x xs
    | [] => []
  end.

Definition foldr {a b : Set} (f : a -> b -> b) (z : b) (l : list a) : b := fold_right f z l.

Fixpoint scanr {a b : Set} (f : a -> b -> b) (q0 : b) (l : list a) : list b :=
  match l with
    | [] => [q0]
    | x :: xs => match scanr f q0 xs with
                   | [] => [] (* This actually never happens *)
                   | q :: qq => f x q :: q :: qq
                 end
  end.

Fixpoint scanr1 {a : Set} (f : a -> a -> a) (l : list a) : list a :=
  match l with
    | [] => []
    | [x] => [x]
    | x :: xs => match scanr1 f xs with
                   | [] => [] (* This actually never happens *)
                   | q :: qq => f x q :: q :: qq
                 end
  end.

Fixpoint replicate {a : Set} (k : nat) (x : a) : list a :=
  match k with
    | 0 => []
    | S n => x :: replicate n x
  end.

Fixpoint take {a : Set} (k : nat) (l : list a) : list a :=
  match k, l with
    | 0, _ => []
    | S n, [] => []
    | S n, x :: xs => x :: take n xs
  end.

Fixpoint drop {a : Set} (k : nat) (l : list a) : list a :=
  match k, l with
    | 0, _ => []
    | S n, [] => []
    | S n, _ :: xs => drop n xs
  end.

Fixpoint takeWhile {a : Set} (p : a -> Bool) (l : list a) : list a :=
  match l with
      | [] => []
      | x :: xs => if p x then x :: takeWhile p xs else []
  end.

Fixpoint dropWhile {a : Set} (p : a -> Bool) (l : list a) : list a :=
  match l with
      | [] => []
      | x :: xs => if p x then dropWhile p xs else xs
  end.

Definition reverse := rev.

Definition and : list Bool -> Bool := foldr andb True.
Definition or : list Bool -> Bool := foldr orb False.
Definition any {a : Set} (p : a -> Bool) (xs : list a) : Bool := or (map a Bool p xs).
Definition all {a : Set} (p : a -> Bool) (xs : list a) : Bool := and (map a Bool p xs).

Arguments map {A B} _ _.
Arguments filter {A} _ _.
Arguments length {A} _.
Arguments app {A} _ _.
Arguments reverse {A} _.

Extract Inlined Constant map => "Prelude.map".
Extract Inlined Constant filter => "Prelude.filter".
Extract Inlined Constant concat => "Prelude.concat".
Extract Inlined Constant concatMap => "Prelude.concatMap".
Extract Inlined Constant null => "Prelude.null".
Extract Inlined Constant length => "Prelude.length".
Extract Inlined Constant foldl => "Prelude.foldl".
Extract Inlined Constant scanl => "Prelude.scanl".
Extract Inlined Constant scanl1 => "Prelude.scanl1".
Extract Inlined Constant foldr => "Prelude.foldr".
Extract Inlined Constant scanr => "Prelude.scanr".
Extract Inlined Constant scanr1 => "Prelude.scanr1".
Extract Inlined Constant replicate => "Prelude.replicate".
Extract Inlined Constant take => "Prelude.take".
Extract Inlined Constant drop => "Prelude.drop".
Extract Inlined Constant takeWhile => "Prelude.takeWhile".
Extract Inlined Constant dropWhile => "Prelude.dropWhile".
Extract Inlined Constant reverse => "Prelude.reverse".
Extract Inlined Constant and => "Prelude.and".
Extract Inlined Constant or => "Prelude.or".
Extract Inlined Constant any => "Prelude.any".
Extract Inlined Constant all => "Prelude.all".

(* Partial list functions *)

Set Contextual Implicit.
Set Implicit Arguments.

Inductive head_acc ( a : Set ) : List a -> Prop :=
          | head_acc_0 : forall (x : a) (xs : List a) , head_acc (cons x xs).

Inductive tail_acc ( a : Set ) : List a -> Prop :=
          | tail_acc_0 : forall (x : a) (xs : List a) , tail_acc (cons x xs).

Inductive last_acc ( a : Set ) : List a -> Prop :=
          | last_acc_0 : forall (x : a) , last_acc (cons x nil)
          | last_acc_1 : forall (x : a) (y : a) (ys : List a) , last_acc ys -> last_acc (cons x (cons y ys)).

Inductive init_acc ( a : Set ) : List a -> Prop :=
          | init_acc_0 : forall (x : a) , init_acc (cons x nil)
          | init_acc_1 : forall (x : a) (y : a) (ys : List a) , init_acc ys -> init_acc (cons x (cons y ys)).

Inductive foldr1_acc ( a : Set ) : (a -> a -> a) -> List a -> Prop :=
          | foldr1_acc_0 : forall (f : a -> a -> a) (x : a) , foldr1_acc f (cons x nil)
          | foldr1_acc_1 : forall (f : a -> a -> a) (x : a) (y : a) (ys : List a) , foldr1_acc f (cons y ys) -> foldr1_acc f (cons x (cons y ys)).

Inductive foldl1_acc ( a : Set ) : (a -> a -> a) -> List a -> Prop :=
          | foldl1_acc_0 : forall (f : a -> a -> a) (x : a) (xs : List a) , foldl1_acc f (cons x xs).

(* Generated proof mess *)

Theorem head_acc_non_0 : forall (a : Set) (x0 : List a) , head_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Theorem last_acc_non_0 : forall (a : Set) (x0 : List a) , last_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Theorem last_acc_inv_1_0 : forall (a : Set) (x0 : List a) (x : a) (y : a) (ys : List a) , last_acc x0 -> (x0 = cons x (cons y ys)) -> last_acc ys .
intros a x0 x y ys H; case H; try (intros; discriminate). intros x' y' ys' Hcall0 . intros Heq0; injection Heq0. intros Heq0_ctx_0 Heq0_ctx_1 Heq0_ctx_2. try (rewrite <- Heq0_ctx_0).  try (rewrite <- Heq0_ctx_1).  try (rewrite <- Heq0_ctx_2). assumption.
Defined.


Theorem tail_acc_non_0 : forall (a : Set) (x0 : List a) , tail_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Theorem init_acc_non_0 : forall (a : Set) (x0 : List a) , init_acc x0 -> (x0 = nil) -> Logic.False .
intros a x0 H; case H; intros; discriminate.
Defined.

Theorem init_acc_inv_1_0 : forall (a : Set) (x0 : List a) (x : a) (y : a) (ys : List a) , init_acc x0 -> (x0 = cons x (cons y ys)) -> init_acc ys .
intros a x0 x y ys H; case H; try (intros; discriminate). intros x' y' ys' Hcall0 . intros Heq0; injection Heq0. intros Heq0_ctx_0 Heq0_ctx_1 Heq0_ctx_2. try (rewrite <- Heq0_ctx_0).  try (rewrite <- Heq0_ctx_1).  try (rewrite <- Heq0_ctx_2). assumption.
Defined.

Theorem foldr1_acc_non_0 : forall (a : Set) (x0 : a -> a -> a) (x1 : List a) (_q0 : a -> a -> a) , foldr1_acc x0 x1 -> (x0 = _q0) -> (x1 = nil) -> Logic.False .
intros a x0 x1 _q0 H; case H; intros; discriminate.
Defined.

Theorem foldr1_acc_inv_1_0 : 
  forall (a : Set) 
         (x0 : a -> a -> a)
         (x1 : List a)
         (f : a -> a -> a)
         (x : a) (y : a)
         (ys : List a) , foldr1_acc x0 x1 -> (x0 = f) -> (x1 = cons x (cons y ys)) -> foldr1_acc f (cons y ys) .
intros a x0 x1 f x y ys H; case H; try (intros; discriminate). 
intros f' x' y' ys' Hcall0. intro Heq0; try (rewrite <- Heq0). intros Heq1; injection Heq1. intros Heq1_ctx_0 Heq1_ctx_1 Heq1_ctx_2. try (rewrite <- Heq1_ctx_0).  try (rewrite <- Heq1_ctx_1).  try (rewrite <- Heq1_ctx_2). assumption.
Defined.

Theorem foldl1_acc_non_0 : forall (a : Set) (x0 : a -> a -> a) (x1 : List a) (_q0 : a -> a -> a) , foldl1_acc x0 x1 -> (x0 = _q0) -> (x1 = nil) -> Logic.False .
intros a x0 x1 _q0 H; case H; intros; discriminate.
Defined.

Unset Implicit Arguments.

Definition head {a : Set} (x0 : List a) (x1 : head_acc x0) : a :=
             match x0 as _y0 return (x0 = _y0) -> a with
               | cons x xs => fun _h0 => x
               | nil => fun _h0 => False_rec a (head_acc_non_0 x1 _h0)
             end (refl_equal x0).

Definition tail {a : Set} (x0 : List a) (x1 : tail_acc x0) : List a :=
             match x0 as _y0 return (x0 = _y0) -> List a with
               | cons x xs => fun _h0 => xs
               | nil => fun _h0 => False_rec (List a) (tail_acc_non_0 x1 _h0)
             end (refl_equal x0).

Fixpoint last { a : Set } (x0 : List a) (x1 : last_acc x0) : a :=
           match x0 as _y0 return (x0 = _y0) -> a with
             | cons x nil => fun _h0 => x
             | cons x (cons y ys) => fun _h0 => last ys (last_acc_inv_1_0 x1 _h0)
             | nil => fun _h0 => False_rec a (last_acc_non_0 x1 _h0)
           end (refl_equal x0).

Fixpoint init { a : Set } (x0 : List a) (x1 : init_acc x0) : List a :=
           match x0 as _y0 return (x0 = _y0) -> List a with
             | cons x nil => fun _h0 => nil
             | cons x (cons y ys) => fun _h0 => cons x (cons y (init ys (init_acc_inv_1_0 x1 _h0)))
             | nil => fun _h0 => False_rec (List a) (init_acc_non_0 x1 _h0)
           end (refl_equal x0).

Fixpoint foldr1 { a : Set } (x0 : a -> a -> a) (x1 : List a) (x2 : foldr1_acc x0 x1) : a :=
           match x0 as _y0, x1 as _y1 return (x0 = _y0) -> (x1 = _y1) -> a with
             | f, cons x nil => fun _h0 _h1 => x
             | f, cons x (cons y ys) => fun _h0 _h1 => f x (foldr1 f (cons y ys) (foldr1_acc_inv_1_0 x2 _h0 _h1))
             | _q0, nil => fun _h0 _h1 => False_rec a (foldr1_acc_non_0 x2 _h0 _h1)
           end (refl_equal x0) (refl_equal x1).

Definition foldl1 {a : Set} (x0 : a -> a -> a) (x1 : List a) (x2 : foldl1_acc x0 x1) : a :=
             match x0 as _y0, x1 as _y1 return (x0 = _y0) -> (x1 = _y1) -> a with
               | f, cons x xs => fun _h0 _h1 => foldl f x xs
               | _q0, nil => fun _h0 _h1 => False_rec a (foldl1_acc_non_0 x2 _h0 _h1)
             end (refl_equal x0) (refl_equal x1).

Extract Inlined Constant head => "Prelude.head".
Extract Inlined Constant tail => "Prelude.tail".
Extract Inlined Constant last => "Prelude.last".
Extract Inlined Constant init => "Prelude.init".
Extract Inlined Constant foldr1 => "Prelude.foldr1".
Extract Inlined Constant foldl1 => "Prelude.foldl1".
