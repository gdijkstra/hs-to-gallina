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
language fragment that we support is Haskell 98 without the following
features:

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

The other features that we do not support should all be relatively
straightforward to implement.

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

Our tool supports Haskell's built-in list notation. We can support it
at the type-level (e.g. |[a]|) and at the term and pattern level
(e.g. |[a,b,c]|, |a:b:[c]|, |[]|). For the terms and patterns we
translate the infix notation to prefix notation in order to simplify
the code that generates the missing patterns, so we do not have to
deal with a single pattern having multiple representations.

\subsection{Strictly positive data types}
\label{sec:negative}

Coq does not allow us to have negative recursive positions in our data
types, whereas Haskell. To illustrate why we do not want this in a
system like Coq, we will try to express the following lambda terms
using a negative data type in Haskell:

\begin{eqnarray*}
  \omega &=& \lambda x . x x \\
  \Omega &=& \omega \omega
\end{eqnarray*}

If we perform a $\beta$-reduction on $\Omega$, we will get $\Omega$
again. We can keep on doing this indefinitely: $\Omega$ has no normal
form.

Consider the following Haskell data type:

\begin{code}
  data Term = Lam (Term -> Term)
\end{code}

Using this data type we can write the following:

\begin{code}
  omega :: Term -> Term
  omega f = (case f of (Lam x) -> x) f

  loop :: Term
  loop = omega (Lam omega)
\end{code}

We can see the exact same thing happening with |loop| as with
$\Omega$: after a couple of reduction steps |loop| reduces to |loop|.

Allowing negative data types in Coq means that we can construct terms
that have no normal form and also terms of type \verb+False+, which
would make the whole system useless.

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

The parameters \verb+a+ and \verb+b+ are implicit and need not be
provided when calling the function \verb+const+.

We also need implicit parameters for data constructors. If we for
example have the following data type:

\begin{verbatim}
Inductive List ( a : Set ) : Set :=
          | Nil : List a
          | Cons : a -> List a -> List a.
\end{verbatim}

then the type of \verb+Cons+ is 

\begin{verbatim}
Cons : forall a : Set, a -> List a -> List a
\end{verbatim}

This means that every time we call \verb+Cons+, we have to specify the
type \verb+a+. Using the contextual implicit parameters option, we can
tell Coq to infer these parameters instead.

There are cases where Coq cannot infer the value of the implicit
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
position, no matter what arguments |i| gets. GHC solves this
``problem'' by filling in the type |GHC.Prim.Any|. We can do something
similar in Coq, by defining a type \verb+Any+ as the empty type,
i.e. it is isomorphic to \verb+Logic.False+ and manually filling in
the parameters it could not figure out:

\begin{verbatim}
Inductive Any : Set := .

Definition i { a : Set } : a -> a :=
             s k (k (b:=Any)).
\end{verbatim}

Filling in these implicit parameters explicitly can be automated, but
this means that we have to implement a type inference mechanism for
Haskell, which we refrained from doing.

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

Haskell allows us to pattern match in a lot of places. In some cases
this does not map nicely to Gallina constructs. For example, when
writing a lambda expression, we are allowed to immediately pattern
match on the argument, e.g. |\(x,y) -> x|. In Gallina we would have to
write something like:

\begin{verbatim}
 fun xy => match xy with (x,y) => x end}.
\end{verbatim}

Instead of translating it this way, we assume that the patterns
occurring in lambda expressions are variables. Our tool will throw an
error if it encounters any other pattern.

Another situation in which we can pattern match are pattern bindings,
e.g. |(x,y) = e|. Coq has some support for these bindings if the
pattern on the left hand side happens to be an irrefutable pattern and
the definition happens to be inside a \verb+let+ construct. We cannot
do this for top-level definitions, so for pattern bindings we again
assume that the pattern occurring on the left hand side is a variable.

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
