\documentclass[a4paper,10pt]{article}

%include polycode.fmt

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}

\title{Experimentation project report: \\
Translating Haskell programs to Coq programs}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

% Abstract?

\section{Introduction}
\label{sec:intro}

% Motivate problem some more: Haskell's type system is nice, but not
% expressive enough for actual verification.

Suppose we want to verify software written in Haskell using a proof
assistant like Coq. Before we can begin with the verification process,
we need to model our software in the proof assistant's specification
language. Manual translation of Haskell code into Coq's Gallina code
is a tedious job and more importantly, it is prone to subtle mistakes.

The goal of this experimentation project is to find answers to the
following questions:

\begin{quote}
  ``Can we automate the process of translating Haskell code into a Coq
  script? Can we do this in such a way that if we extract the Haskell
  code from the Coq script, we get back a module with the same
  interface and semantics?''
\end{quote}

\section{Method}
\label{sec:method}

We will use Haskell along with the {\sc UUAG} system to implement a
translation of a Haskell module into a Coq script. To parse the
Haskell file, we will use the \verb+haskell-src-exts+ library. We will
take the abstract syntax tree with all the sugar instead of
translating for example an intermediate language like GHC Core.

Since Haskell is a language with a lot of features, it is unrealistic
to expect that we can support every single one of them right away. The
language fragment that we aim to support is Haskell 98 without at
least the following features:

\begin{itemize}
\item type classes
\item do-notation and list comprehensions
\item record syntax
\item infix notation
\item tuple syntax
\end{itemize}

% Give some more motivation as to why these particular things are not
% supported?

% Say something about popular extensions not supported? Or should that
% be clear?

Later on it will become clear that we also need some further
restrictions on our language to make it all work.

For the most part, Haskell's type system and syntax can be seen as a
subset of that of Coq, so we can translate a lot of constructions in a
very straight-forward manner. However, there are a couple of
situations in which the two systems diverge:

% Something about assuming that the Haskell module is well-typed, has
% type signatures and compiles!

\begin{description}
\item[Ordering/grouping definitions] In Coq, we can only reference
  identifiers that have been defined previously. We need to order our
  definitions according to the dependencies. In the case of mutually
  recursive definitions, we need to group these definitions.
\item[Pattern matching] In Haskell we can pattern match in a lot of
  places, e.g. in lambdas (|\(x:xs) -> x|), in (top-level) definitions
  (|(x:xs) = [a, b, c]|). In Coq we cannot do this, unless the
  equation occurs in a \verb+let+-binding and the pattern happens to
  be an irrefutable pattern.
\item[Type signatures] Every top-level definition needs an explicit
  type signature. Although we can of course infer those from the
  Haskell code, we choose to assume that the user has provided these
  type signatures already.
\item[Parametric polymorphism] Coq does not have a notion of
  parametric polymorphism. We can however fake it, up to a point.
\item[Mutual recursion] We can deal with mutual recursion in Coq for
  top-level definitions, but for local definitions occuring inside a
  \verb+let+, we cannot have mutual recursion.
\end{description}

% Talk about handling of Prelude stuff.

\section{Parametric polymorphism and implicit parameters}
\label{sec:parampoly}

% Also mention the contextual implicit stuff and data type constructors

Coq's type theory doesn't have parametric polymorphism, however, we
can simulate this using implicit parameters, e.g.:

\begin{code}
const :: a -> b -> a
const x _ = x
\end{code}

translates to:

\begin{verbatim}
Definition const { a b : Set } (x0 : a) (x1 : b) : a :=
             match x0 , x1 with
               | x , _ => x
             end.
\end{verbatim}

The parameters \verb+a+ and \verb+b+ are implicit and usually need not
be provided when calling the function \verb+const+. There are however
cases where Coq cannot infer the value of such implicit
parameters. Consider the following example:

\begin{code}
s :: (a -> b -> c) -> (a -> b) -> a -> c
s p q r = p r (q r)

k :: a -> b -> a
k x _ = x

i :: a -> a
i = s k k
\end{code}

Coq will not be able to infer the type parameter |b| of the second
call to |k| in the definition of |i|. If we do the type checking by
hand, we will notice that we can fill in any type we want in that
position, no matter what arguments |i| gets. 

% This is also reflected in the fact that if we look at the GHC Core
% output, we will see that GHC fills in GHC.Prim.Any or something.

\section{General recursion}
\label{sec:genrec}

% Explain problem, explain array of solutions, explain why we chose
% this solution specifically. (Extraction!)

\subsection{Bove-Capretta method}
\label{sec:bcmethod}

\subsection{Implementation}
\label{sec:bcimpl}

% only allow apps and vars

% generate inductive data type
% details on Prop versus Set wrt extraction.

% generate new function

% Detail about contextual implicit arguments for functions that have
% been generated by this method.

\subsubsection{Inversion theorems}
\label{sec:invthms}
% Details on the inversion proofs and why they should work.

% ltac script would be better, I guess?

\subsubsection{Missing patterns}
\label{sec:missingpats}
% Details of missing pattern implementation.

% Details of implementation: what do we restrict ourselves to? Type
% synonyms stuff again.

\subsubsection{Examples}
\label{sec:bcexamples}
% Examples.

% Refine tactic example for how to use stuff. (Find a nice example
% that I encountered in verification challenge?)

\section{Coinduction}
\label{sec:coind}

Another limitation of a direct translation is that in Coq there is a
distinction between inductive and coinductive data types. If we for
example want to work with infinite lists in Coq, we have to make a
separate coinductive data type. With the ``codata'' and ``cofix''
pragmas, we can indicate that we want a coinductive translation of our
definitions.

\begin{code}
{-"\text{\{-\# OPTIONS\_Hs2Gallina codata: Stream \#-\}}"-}
{-"\text{\{-\# OPTIONS\_Hs2Gallina cofix: zeroes  \#-\}}"-}

...

data Stream a = Cons a (Stream a)

zeroes :: Stream Nat
zeroes = Cons 0 zeroes

\end{code}

would translate to:

\begin{verbatim}
CoInductive Stream (a :Set) : Set :=
  | Cons : a -> Stream a -> Stream a.

CoFixpoint zeroes : Stream Nat :=
  Cons 0 zeroes.
\end{verbatim}

Just as we have restrictions as to what recursive definitions we can
specify in Coq, we have similar restrictions for corecursive
definitions: every corecursive call should be \emph{guarded} by a
constructor. Our tool will not check whether this is the case and will
just blindly translate the Haskell definitions.

% Coinduction stuff as a nice extra. Talk about how we don't check
% guardedness and no mixing of induction and coinduction.

\section{Extraction}
\label{sec:extraction}

% Extraction
% Coq needs to update its extraction stuff. Produces broken Haskell.
% Check which version I have and which is the newest etc.

% Talk about how we want to check whether this is still the same
% code. Generating QuickCheck tests to compare programs seems rather
% involved. Unless you make a lot of assumptions. What would be fun to
% have a mapping from QuickCheck properties to Coq properties and
% back? Very much future work. Do we have any guarantees that
% extraction will yield something with the same semantics as the Coq?
% If so, then we needn't care about the fact that our own translation
% might not preserve semantics (up to strictness, whatever that
% means): you verify stuff and you get something that's extracted with
% the same computational behaviour, that should be good enough.

\section{Related work}
\label{sec:relatedwork}

% Related work
% Verifying Haskell in CTT paper
% Function interface and related articles?

\section{Future work}
\label{sec:futurework}

% Future work

% Modules, better syntax support, refine tactic support, type
% synonyms, type classes, GADTs, better integration with GHC for
% finding imports and dependencies and et cetera.

\section{Conclusion}
\label{sec:conclusion}


% Conclusion

% It sort of works nicely? Step in the right direction?

\end{document}
