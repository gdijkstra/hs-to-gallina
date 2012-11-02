\documentclass[a4paper,10pt]{article}

%include polycode.fmt

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}

\title{Experimentation project proposal: \\
Translating Haskell programs to Coq programs}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

Suppose we want to verify software written in Haskell using a proof
assistant like Coq. Before we can begin with the verification process,
we need to model our software in the proof assistant's specification
language. Manual translation of Haskell code into Coq's Gallina code
is a tedious job and more importantly, it is prone to subtle mistakes.

We want to write a tool that automatically translate Haskell code to
Gallina code. However, since Coq only allows structural recursion, not
all Haskell definitions can translated directly into Gallina. In order
to deal with some of these cases, we can generate Bove-Capretta
predicates from the original function definition and rewrite the
function definition using this predicate.

Another limitation of a direct translation is that in Coq there is a
distinction between inductive and coinductive data types. If we for
example want to work with infinite lists in Coq, we have to make a
separate coinductive data type. We also want our tool to be able to
assist in this process.

Since one probably will only verify a single Haskell module,
pretending all the imported functions have already been verified. We
want the tool to facilitate this strategy. For example, generate
appropriate axioms for the imported definitions, such that if we
extract the Haskell module from the Coq script, we can plug it back in
our Haskell software without having to change the resulting code
manually.

The following language features would be nice to support, but will
probably be outside the scope of this project:

\begin{itemize}
\item typeclasses
\item GADTs other extensions to Haskell's type system
\item do-notation and list comprehensions
\end{itemize}

\section{Example}

\begin{code}
{-"\text{\{-\# LANGUAGE NoImplicitPrelude \#-\}}"-}
{-"\text{\{-\# OPTIONS\_Hs2Gallina quicksort \#-\}}"-}

module Quicksort where

data Nat =
  Zero
  | Succ Nat

data List a =
  Nil
  | Cons a (List a)

data Bool =
  True
  | False

filter :: (a -> Bool) -> List a -> List a
filter p Nil          =  Nil
filter p (Cons x xs)  =  if p x
                         then Cons x (filter p xs)
                         else filter p xs

lt :: Nat -> Nat -> Bool
lt Zero      Zero      = False
lt Zero      (Succ n)  = True
lt (Succ n)  Zero      = False
lt (Succ n)  (Succ m)  = lt n m

lnot :: Bool -> Bool
lnot True  = False
lnot False = True

ge :: Nat -> Nat -> Bool
ge a b = lnot (lt a b)

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b

append :: List a -> List a -> List a
append Nil          ys = ys
append (Cons x xs)  ys = Cons x (append xs ys)

quicksort :: List Nat -> List Nat
quicksort Nil          = Nil
quicksort (Cons x xs)  = append
                         (quicksort (filter ((flip lt) x) xs))
                         (quicksort (filter ((flip ge) x) xs))
\end{code}

\end{document}
