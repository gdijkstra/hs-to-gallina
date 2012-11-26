\documentclass[a4paper,10pt]{article}

%include polycode.fmt

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}
\usepackage{todonotes}

\newcommand{todoi}[1]{\todo[inline]{#1}}

\title{Experimentation project report: \\
Translating Haskell programs to Coq programs}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

\todoi{Abstract?}

\section{Introduction}
\label{sec:intro}

\todoi{Motivate problem some more: Haskell's type system is nice, but not
expressive enough for actual verification.}

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

\todoi{Motivation for this? Hopefully more readable code and
  proofs (we can more or less do the equational reasoning we are used
  to). More importantly (?): Bove-Capretta and extraction.}

\todoi{ Stress that we do not create a deep embedding of
  Haskell in Coq, but really translate Haskell constructs to the
  corresponding Gallina constructs (if they exist). A consequence of
  this approach is that we reason about our Haskell program as if it
  were total and strict.  Coq will complain about missing patterns and
  non-structural recursion. Ways around this: section~\ref{sec:bcmethod} and
  section~\ref{sec:coind}.}

Since Haskell is a language with a lot of features, it is unrealistic
to expect that we can support every single one of them right away. The
language fragment that we aim to support is Haskell 98 without at
least the following features:

\begin{itemize}
\item type classes
\item |do|-notation
\item list comprehensions
\item record syntax
\item infix notation
\item tuple syntax
\item guards
\end{itemize}

Even though Coq currently does have some notion of type classes, it is
very experimental and therefore we have chosen to disregard type
classes. Since |do|-notation depends on type classes, we also do not
support this.

The other features that we do not support are all relatively
straightforward to implement. 

\todoi{But have not been implemented due to time constraints. Although
  infix notation: needs some work with generating names and such and
  translating priorities.}

Later on it will become clear that we also need some further
restrictions on our language in some cases to make it all work. % rather vague sentence

For the most part, Haskell's type system and syntax can be seen as a
subset of that of Coq, so we can translate a lot of constructions in a
very straight-forward manner. However, in many places there are also
subtleties and intricacies that we have to take care of. 
% Which is the main focus of the following sections?

% Something about assuming that the Haskell module is well-typed, has
% type signatures and compiles!

\section{Type signatures}
\label{sec:typesigs}

In Haskell we leave out type signatures and let the compiler figure
out the type for us. For Coq's type system, type inference is
undecidable, so we have to explicitly annotate at least our top-level
definitions. Instead of doing the type inference ourselves, we assume
that the user has written explicit type signatures for every top-level
definition and use these annotations.

\section{Data types}
\label{sec:datatypes}

% Normal vanilla Haskell data types can be straightforwardly translated

% Note: name of constructor must not coincide with name of data type.

% Note: negative data types are not allowed. Give examples of where
% this can go wrong.

% Note: least fixed point only. Coinduction see sec:coind.

% Built-in support for lists.

% Type synonyms can also be translated straightforwardly. 

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

% Manual solution: add GHC.Prim.Any thing to Coq prelude and use
% explicit implicit parameter assignments. (How does this look in the
% extracted Haskell code?)

\section{Ordering definitions}

% Ordering: topological ordering of dependency graph.

% (Mutual) recursion: strongly connected components of dependency
% graph. We need to explicitly group these mutual definitions with the
% \verb+with+ constructor.

% Mutual recursion in let bindings does not work.

\section{Pattern matching}

% Pattern bindings do not work as expected. Although we have
% irrefutable patterns in Coq, we do not use that feature.

\section{General recursion and partiality}
\label{sec:genrec}

% Explain problem, explain array of solutions, explain why we chose
% this solution specifically. (Extraction!)

\subsection{Bove-Capretta method}
\label{sec:bcmethod}

% explain method

% explain how nested recursion leads to induction-recursion and that
% we cannot easily do this in Coq, in general.

% for sake of simplicity, we only consider apps and vars: no case
% expressions and guards. These can be added.

\subsection{Implementation}
\label{sec:bcimpl}

% generate inductive data type
% details on Prop versus Set wrt extraction.

% generate new function

% Detail about contextual implicit arguments for functions that have
% been generated by this method.

\subsubsection{Inversion theorems}
\label{sec:invthms}
% Since the predicate is of sort Prop, we cannot pattern match on
% inhabitants of this predicate, since the type of the result of the
% function we are transforming is of sort Type. We need inversions
% theorems to get around this.

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
separate coinductive data type. With the \verb+codata+ and \verb+cofix+
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

\section{Prelude}
\label{sec:prelude}

% Show how we support some prelude stuff.
% Of course we skip all the type class stuff

% We also skip the obviously non-terminating stuff like iterate and
% such.

% We have to write our own B-C definitions of partial functions like
% head and tail, but during extraction they get mapped to the Prelude
% functions |head| and |tail|.

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

% Semantics: no idea. We need to trust extraction mechanism and our
% Coq prelude stuff. afaik nothing has been proved about Coq's
% extraction mechanism?

\end{document}
