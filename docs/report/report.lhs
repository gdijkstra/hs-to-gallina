\documentclass[a4paper,10pt]{article}

%include polycode.fmt

\newcommand{\todoi}[1]{\todo[inline]{#1}}

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}
\usepackage{todonotes}

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

For the most part, Haskell's type system and syntax coincide with a
subset of that of Coq, so we can translate a lot of constructions in a
very straight-forward manner. However, in many places there are also
subtleties and intricacies that we have to take care of, which is the
main focus of the following sections.

\section{Type signatures}
\label{sec:typesigs}

In Haskell we leave out type signatures and let the compiler figure
out the type for us. For Coq's type system, type inference is
undecidable, so we have to explicitly annotate at least our top-level
definitions. Instead of doing the type inference ourselves, we assume
that the user has written explicit type signatures for every top-level
definition and use these annotations.

\section{Data types and type synonyms}
\label{sec:datatypes}

Haskell data types can be straightforwardly translated. For example:

\begin{code}
data List a = Nil | Cons a (List a)
\end{code}

translates to:

\begin{verbatim}
Inductive List ( a : Set ) : Set :=
          | Nil : List a
          | Cons : a -> List a -> List a.
\end{verbatim}

One important thing to note here is that since in Coq, names of data
constructors cannot coincide with the name of the data type itself,
since both can be used in exactly the same places.

Type synonyms can also be translated easily:

\begin{code}
  type SillySynonym a b c = Silly b c
\end{code}

becomes:

\begin{verbatim}
Definition SillySynonym ( a b c : Set ) : Set := Silly b c.
\end{verbatim}

\subsection{List notation}
\label{sec:listnotation}

\todoi{Built-in support for lists: it is supported in patterns and
  terms, but gets translated to conses and nils, even though we have
  support for that in Coq. But the extracted code uses conses and nils
  everywhere...}

\subsection{Strictly positive data types}
\label{sec:negative}

Consider the following Haskell data type:

\begin{code}
  data Bad = BadConstr (Bad -> Bad)
\end{code}

If we translate this as follows:

\begin{verbatim}
Inductive Bad : Set :=
          | BadConstr : (Bad -> Bad) -> Bad.
\end{verbatim}

we will get the following error message:

\begin{verbatim}
Error: Non strictly positive occurrence of "Bad" in "(Bad -> Bad) -> Bad".
\end{verbatim}

Coq does not allow such definitions, as it enables us to write terms
that do not have a normal form or even terms of type \verb+False+,
which would make the entire system useless.

Using the |Bad| example, we can write the following:

\begin{code}
  omega :: Bad -> Bad
  omega f = (case f of (BadConstr x) -> x) f

  loop :: Bad
  loop = omega (BadConstr omega)
\end{code}

Reducing |loop| we eventually reduce to |loop| again and can keep on
doing this indefinitely: |loop| has no normal form.

Our tool does not check for these kind of constraints on data types.

\subsection{Coinductive types}

In Haskell, we do not make a distinction between inductive and
coinductive interpretations of data type definitions, e.g. the list
type both has finite lists as infinite lists (or streams) as its
inhabitants. In Coq there is a clear distinction between these two
interpretations. The translation given above reads the data type as an
inductive definition, so we are only allowed to give finite
inhabitants of that data type.

If we want to deal with infinite data structures, we then need to use
coinduction, which we will deal with in section~\ref{sec:coind}.

\section{Parametric polymorphism and implicit parameters}
\label{sec:parampoly}

\todoi{Also mention the contextual implicit stuff and data type
  constructors.}

Coq's type theory does not have parametric polymorphism, however, we
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

\todoi{This is also reflected in the fact that if we look at the GHC
  Core output, we will see that GHC fills in GHC.Prim.Any.}

\todoi{Manual solution: add GHC.Prim.Any thing to Coq prelude and use
  explicit implicit parameter assignments. (How does this look in the
  extracted Haskell code?)}

\section{Ordering definitions}

When writing definitions in Coq, we can only use terms that have been
defined previously. In the case of recursive functions, we need to
explicitly mark it as such, using the \verb+Fixpoint+ command.

In Haskell, the ordering of our definitions does not matter, so when
translating we need to order the definitions ourselves and check
whether they are recursive or not. This corresponds to finding all the
strongly connected components of the dependency graph in a topological
order.

If such a strongly connected component consists of more than one
definition, we have mutually recursive definitions. Coq supports these
constructions by grouping the definitions together with the
\verb+with+ keyword. We can only group functions with other functions
and data types with other data types. However, since Haskell does not
allow us to write data types and functions that mutually depend on
eachother, this is not a problem.

\subsection{Recursion in |let|-bindings}
\label{sec:reclet}

Just as with top-level definitions, local definitions inside |let|s
and |where|s need to be ordered and grouped. For recursive definitions
we have the \verb+let fix+ construct, but this does not extend to
mutually recursive definitions. Our tool therefore does not support
mutually recursive local definitions.

\section{Pattern matching}

Haskell allows us to pattern match in a lot of places.

\todoi{lambda expressions}
\todoi{function definitions}
\todoi{pattern bindings (these only make sense in let statements in coq and even then only if they are irrefutable)}
\todoi{case statements (obviously)}

\section{General recursion and partiality}
\label{sec:genrec}

\todoi{Explain problem, explain array of solutions, explain why we
  chose this solution specifically. (Extraction!)}

\subsection{Bove-Capretta method}
\label{sec:bcmethod}

\todoi{explain method}

\todoi{explain how nested recursion leads to induction-recursion and that
we cannot easily do this in Coq, in general.}

\todoi{for sake of simplicity, we only consider apps and vars: no case
  expressions and guards. These can be added.}

\subsection{Implementation}
\label{sec:bcimpl}

\todoi{generate inductive data type}

\todoi{details on Prop versus Set wrt extraction.}

\todoi{generate new function}

\todoi{Detail about contextual implicit arguments for functions that
  have been generated by this method.}

\subsubsection{Inversion theorems}
\label{sec:invthms}

\todoi{Since the predicate is of sort Prop, we cannot pattern match on
  inhabitants of this predicate, since the type of the result of the
  function we are transforming is of sort Type. We need inversions
  theorems to get around this.}

\todoi{Details on the inversion proofs and why they should work.}

\todoi{Note that ltac script would probably be better}

\subsubsection{Missing patterns}
\label{sec:missingpats}

\todoi{Details of missing pattern implementation.}

\todoi{Details of implementation: what do we restrict ourselves to?
  Type synonyms stuff again.}

\subsubsection{Examples}
\label{sec:bcexamples}

\todoi{Show examples.}

\todoi{Refine tactic example for how to use stuff. (Find a nice
  example that I encountered in verification challenge?)}

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

\todoi{Coinduction stuff as a nice extra. Talk about how we don't
  check guardedness and no mixing of induction and coinduction.}

\section{Extraction}
\label{sec:extraction}

\todoi{Talk about how we want to check whether this is still the same
  code. Generating QuickCheck tests to compare programs seems rather
  involved. Unless you make a lot of assumptions. What would be fun to
  have a mapping from QuickCheck properties to Coq properties and
  back? Very much future work. Do we have any guarantees that
  extraction will yield something with the same semantics as the Coq?
  If so, then we needn't care about the fact that our own translation
  might not preserve semantics (up to strictness, whatever that
  means): you verify stuff and you get something that's extracted with
  the same computational behaviour, that should be good enough.}

\todoi{Coq needs to update its extraction stuff. Produces broken
  Haskell...}

\section{Prelude}
\label{sec:prelude}

\todoi{Show how we support some prelude stuff. Of course we skip all
  the type class stuff}

\todoi{We also skip the obviously non-terminating stuff like iterate
  and such.}

\todoi{We have to write our own B-C definitions of partial functions
  like head and tail, but during extraction they get mapped to the
  Prelude functions |head| and |tail|.}

\section{Related work}
\label{sec:relatedwork}

\todoi{Verifying Haskell in CTT paper}

% Function interface and related articles?

\section{Future work}
\label{sec:futurework}

\todoi{Modules, better syntax support, refine tactic support, type
  synonyms, type classes, GADTs, better integration with GHC for
  finding imports and dependencies and et cetera.}

\section{Conclusion}
\label{sec:conclusion}

\todoi{Semantics preserved? Nothing has been proved about this. We
  need to trust extraction mechanism and our Coq prelude stuff.}

\end{document}
