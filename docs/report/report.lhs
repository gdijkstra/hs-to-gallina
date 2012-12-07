\documentclass[a4paper,10pt]{article}

%include report.fmt

\newcommand{\todoi}[1]{\todo[inline]{#1}}

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}
\usepackage{todonotes}
\usepackage{tgpagella}

\title{Experimentation project report: \\
Translating Haskell programs to Coq programs}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

\section{Introduction}
\label{sec:intro}

Haskell programmers like to say that \emph{well-typed programs do not
  go wrong}. But just passing the type checker of our Haskell compiler
does not give us any guarantees about termination or that our program
actually computes the right thing. If we have written a function |sort
:: [Int] -> [Int]| that type checks, we do not know whether it
actually returns the sorted version of the input list. The usual way
to go for checking properties like these is to use a tool like
QuickCheck to test the properties on randomly generated input. If we
want to go one step further and actually \emph{verify} our Haskell
software using a proof assistant, we need to model our Haskell code in
the assistant's specification language. We can then formulate the
properties and begin proving them.

Choosing Coq for the proof assistant is an attractive option, because
its specification language Gallina is a functional programming
language that in many respects is a lot like Haskell. In most cases we
can very easily map our Haskell code to the Gallina
equivalent. Manually translating Haskell code into Gallina code,
however, is still a tedious job and more importantly, it is prone to
subtle mistakes, hence it would be nice if we could automate (parts
of) this process.

During the verification process, we might notice that we have to
change our Gallina code in order to be able to prove that certain
properties hold. Instead of changing the original Haskell code to
reflect these changes, we can generate new Haskell code from our Coq
script using the extraction mechanism. When translating our Haskell
program, we need do this in such a way that the extracted Haskell code
still has the same interface (i.e. the types of the definitions are
the same) so we can plug the verified module back into the rest of our
Haskell code base.

% TODO: Transition to this here below?

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

We implemented the translation using Haskell and the UUAG system. As
Haskell parser, we used the \verb+haskell-src-exts+ parser. The
abstract syntax tree of the Haskell file is then mapped to the
corresponding Gallina code, if this is possible. We use Gallina's own
constructs to give the definitions, instead of writing a deep
embedding of Haskell in Gallina. 

For the most part, Haskell's type system and syntax coincide with a
subset of that of Coq, so we can translate a lot of constructions in a
very straight-forward manner. However, in many places there are also
subtleties and intricacies that we have to take care of, which is the
focus of the sections~\ref{sec:supportedlang}--\ref{sec:patmatch}.

Another aspect of this approach, which is both a positive and a
negative one, is that we get Coq's totality checking for free. Coq
checks whether all pattern matches are exhaustive and whether all
recursive calls are structurally recursive. This also means that we
cannot map every valid Haskell program to its Gallina counterpart
without changing the definition. For definitions with non-exhaustive
pattern matches (e.g. |head|) or non-structural recursion
(e.g. |quicksort|), we implemented the Bove-Capretta method
(section~\ref{sec:bcmethod}).

Apart from non-exhaustive pattern matches and non-structural
recursion, Haskell also allows us to work with infinite data
structures: in Haskell, we do not make a distinction between inductive
and coinductive interpretations of data type definitions, e.g. the
list type both has finite lists as well as infinite lists (or streams)
as its inhabitants. In Coq there is a clear distinction between these
two interpretations. The translation given above reads the data type
as an inductive definition, so we are only allowed to give finite
inhabitants of that data type. If we want to deal with infinite data
structures, we need to use coinduction (section~\ref{sec:coind}).

One of the reasons we did not go for a deep embedding of Haskell in
Coq is that this makes it a lot easier to produce a Coq script that,
if we extract it back to Haskell, produces code that is similar ``on
the outside'' to our original code, i.e. the names of the definitions
remain unchanged as do the types (up to $\alpha$-equivalence). In
section~\ref{sec:extraction} we show how we can make this
work. Section~\ref{sec:prelude} shows how we can have support for a
fragment of the Haskell Prelude, in such a way that the extracted code
also makes sense.

\section{Supported language fragment}
\label{sec:supportedlang}

Since Haskell is a language with a lot of features, it is unrealistic
to expect that we can support every single one of them right away. The
language fragment that we support is Haskell 98 without the following
features:

\begin{itemize}
\item modules
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

Currently we only support translating a single module without any
imports, except for the (implicit) Prelude import (see
section~\ref{sec:prelude}. One way to support modules, is to also
translate all the modules the current module depends on, but this
breaks down as soon as there are dependencies on modules of which we
do not have the source code. It also does not fit nicely in the use
case where we want to verify a single module of a large
project. Instead of translating the modules we depend on, we can
generate axioms for all the definitions we import, so we can pretend,
in our Coq script, that we have those definitions of the right
type. Usually having only the type of the imported definitions is not
enough to be able to prove properties of our own definitions. The user
will probably have to define extra axioms that characterise the
behaviour of the imported definitions.

The other features that we do not support should all be relatively
straightforward to implement, but have not been implemented due to
time constraints.

\section{Type signatures}
\label{sec:typesigs}

In Haskell we leave out type signatures and let the compiler figure
out the type for us. For Coq's type system, type inference is
undecidable, so we have to explicitly annotate at least our top-level
definitions. Instead of doing the type inference ourselves, we assume
that the user has written explicit type signatures for every top-level
definition and use these annotations.

Type signatures for local definitions are ignored when translating to
Gallina. These are usually not needed if we already have the type
signature for the corresponding top-level definition.

\section{List notation}
\label{sec:listnotation}

Our tool supports Haskell's built-in list notation. We can support it
at the type-level (e.g. |[a]|) and at the term and pattern level
(e.g. |[a,b,c]|, |a:b:[c]|, |[]|). For the terms and patterns we
translate the infix notation to prefix notation in order to simplify
the code that generates the missing patterns, so we do not have to
deal with a single pattern having several distinct representations.

The list notation is mapped to Coq's list notation as defined in its
standard library, so that when we want to interactively prove
something about a definition that involves lists, Coq uses the more
convenient syntax for lists, when pretty printing.

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

In the Gallina definition we have to be explicit about the type (or in
Haskell terms: \emph{kind}) of the type parameters. Instead of doing
actual kind inference, we simply assume all type parameters to have
type \verb+Set+, which corresponds to the Haskell kind
|*|. Higher-kinded data types, e.g. data types that have type
parameters of kind |* -> *|, are therefore not supported.

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

Just as with data types, type parameters that do not have kind |*| are
not supported.

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
that have no normal form. Constructions like the above can be used to
define terms of the empty type \verb+False+, which would make the
whole system useless.

Our tool does not check for these kind of constraints on data types
and defers the error messages to Coq.

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

The curly braces indicate that the parameters \verb+a+ and \verb+b+
are implicit.\footnote{Here we assume, just as with the type
  parameters of data types and type synonyms, that all the type
  variables are of kind |*|.} These implicit parameters need not be
provided when calling the function \verb+const+.

Something we did not mention in section~\ref{sec:datatypes} is that we
also need implicit parameters for data constructors. If we for example
have the following data type:

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

The simulation of parametric polymorphism as described above is not
perfect. There are cases where Coq cannot infer the value of the
implicit parameters. Consider the following example:

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
position, no matter what arguments |i| gets. GHC solves this problem
by filling in the type |GHC.Prim.Any|. We can do something similar in
Coq, by defining a type \verb+Any+ as the empty type and manually
filling in the parameters it could not figure out by itself:

\begin{verbatim}
Inductive Any : Set := .

Definition i { a : Set } : a -> a :=
             s k (k (b:=Any)).
\end{verbatim}

Of course, it would be better if our tool could automatically figure
out which implicit parameters it needs to fill in explicitly, but this
means that we have to implement a type inference mechanism for
Haskell, which we refrained from doing.

\section{Ordering definitions}

When writing definitions in Coq, we can only use terms that have been
defined previously. In the case of recursive functions, we need to
explicitly mark it as such, using the \verb+Fixpoint+ command.

In Haskell, the ordering of our definitions does not matter, so when
translating we need to order the definitions ourselves and check
whether they are recursive or not. This corresponds to finding all the
strongly connected components of the dependency graph in a topological
order. If such a strongly connected component consists of more than one
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
mutually recursive local definitions. The user has to lift the mutual
recursion to the top-level so that we are be able to translate the
program.

\section{Pattern matching}
\label{sec:patmatch}

Haskell allows us to pattern match in a lot of places. In some cases
this does not map nicely to Gallina constructs. For example, when
writing a lambda expression, we are allowed to immediately pattern
match on the argument, e.g. |\(x,y) -> x|. In Gallina we would have to
write something like:

\begin{verbatim}
 fun xy => match xy with (x,y) => x end
\end{verbatim}

Instead of translating it this way, we assume that the patterns
occurring in lambda expressions are variables. Our tool will throw an
error if it encounters any other pattern.

Another situation in which we can pattern match are pattern bindings,
e.g. |(x,y) = e|. Coq has some support for these bindings if the
pattern on the left hand side happens to be an irrefutable pattern and
the definition happens to be inside a \verb+let+ construct. We cannot
do this for top-level definitions, so for pattern bindings we again
assume that the pattern occurring on the left hand side is a single
variable.

\section{General recursion and partiality}
\label{sec:genrec}

Coq demands that all our definitions be terminating and total. This is
enforced by checking whether the pattern matches are exhaustive. For
recursive definitions we are restricted to structural recursion: there
should be at least one argument that decreases structurally in every
recursive call, i.e. we pattern match on this argument and call the
function recursively on the constituents of that pattern.

Haskell does not enforce these properties: definitions that violate
either of these properties are commonplace. A typical example of a
function that has non-exhaustive pattern matches is |head|. Of course,
we can rewrite partial functions like these to total ones by using the
|Maybe| data type, but there are cases in which we know that a
particular call to |head| never fails and that the overhead of using
|Maybe| is not worth it. We therefore need a way to translate
functions like |head| in such a way that we can convince Coq that the
call is safe and that the extracted code looks a lot like the original
Haskell code.

Consider the following Haskell definition\todo{Maybe make this into a
  figure so we can refer to it later on?}:

\begin{code}
  quicksort           ::  [Nat] -> [Nat]
  quicksort []        =  []
  quicksort (x : xs)  =  append
                         (quicksort (filter (gt x) xs))
                         (quicksort (filter (le x) xs))
\end{code}

where |Nat| is the natural numbers, |append| is |(++)|, |gt| and |le|
are the ``greater than'' and ``less than or equal'' relations on
|Nat|, i.e. they are of type |Nat -> Nat -> Bool|. If we translate
this directly to Gallina, we will run into the problem that Coq cannot
discover a parameter that structurally decreases every recursive
call. It cannot infer that |filter (gt x) xs| is indeed structurally
smaller than |x : xs|.

There are numerous ways of changing the definition in such a way that
Coq does accept it. A popular method is to use well-founded recursion,
for example using the Program tactic.\todo{Add citation} This method
has the property that we do not need to change the type of our
definition. We can also write our definitions in such a way, that the
proofs of termination get erased during extraction. However, we did
not choose well-founded recursion as it does not allow for definitions
with non-exhaustive pattern matches or functions that only terminate
for certain inputs.

Another approach is to encapsulate the return value in a
non-termination monad, such as Capretta's coinductive delay
monad\todo{Add appropriate references}. These approaches need us to
change the type of our original definition and the body of the
definition needs to be rewritten in monadic style to reflect the
change in return type. Changing the type of the definition also means
that the extracted code will not be compatible anymore.\todo{Meh, what
  does \emph{compatible} mean here? Types are different because the
  types are different...} \todoi{Proving stuff using these monads
  might be painful.}

The method we chose is the Bove-Capretta
method\cite{CambridgeJournals:318914}. Instead of having a general
purpose accessability predicate as we have for well-founded recursion,
we make an ad-hoc one for the definition we want to translate. The
idea is that we can rewrite the function definition to take proofs of
this ad-hoc predicate as an extra argument and that we now recurse
structurally on these proofs. This means that we do have to change the
type of our function, but this can be done in such a way that this
gets erased again during extraction. Another big selling point of this
translation is that it also allows for partial functions.

All the good stuff does come with a price: every time we call a
function (in our Coq script) translated with the Bove-Capretta method,
we need to provide a proof of our ad-hoc accessability predicate. This
technique does not magically prove termination for our programs, it
just makes it possible to prove termination.

\subsection{Bove-Capretta method}
\label{sec:bcmethod}

Suppose that we have a Haskell function |f :: s0 -> hdots -> sn -> tau|
defined by the following equations:

\begin{code}
  f     p00    hdots     p0n =   e0
  vdots        ddots             vdots
  f     pm0    hdots     pmn =   em
\end{code}

We make a special purpose inductive data type (or predicate) that
should have as inhabitants proofs that our function terminates for the
given input. If we add this predicate as an argument to our function
and pass the right values along recursively, we will see that we are
recursing structurally on the proofs of our predicate, that
essentially encode the call graph for the corresponding input.

So suppose we have a Haskell function |f :: s0 -> hdots -> sn -> t|, the
predicate would have type \verb+f_acc : s_0 -> ... -> s_n -> Prop+,
i.e. it is indexed by the arguments of the function.

What does it mean for this function |f| to terminate? How can we
express this as a proposition depending on our input |x0 ... xn|? We
look at all the equations of our definition and can derive the
constructors of our predicate as follows: |f| terminates for input
|pi0 ... pin| (as terms instead of patterns) if it terminates for all
the recursive calls to |f| in |ei|. The constructor for the $i$-th
equation consists of a context induced by the patterns (i.e. all the
pattern variables and their types) and a termination proof for every
recursive call.

\todoi{Note that we only support vars and apps. Support for case
  statements and lambdas can be added, but things get a lot more
  complicated without improving on the expressiveness of things.}

\subsubsection{Generating the inductive data type}
\label{sec:genpred}

\todoi{Extract context, detail with type synonyms, only works with
  data types defined in module itself and built-in types (currently
  only lists)}

\todoi{Extract recursive calls, these need to be fully applied
  (explain why)}

\todoi{Note how nested recursion fails: we depend on the function that
  we are currently defining, mutual recursion between function and
  data type definition, is called induction-recursion, not supported
  by Coq, but supported by Agda.}

\subsubsection{Generating the new function definition}
\label{sec:genfun}

\todoi{add argument to type: contextual implicit arguments are biting
  us now: disable automatic implicit arguments when defining
  functions. (The polymorphic stuff is explicit.}

\todoi{change body of function: dependent pattern matching, theorems
  we need, prop vs set}

\todoi{add right inv thms to right positions. Thms generation proofs
  stuff warrants its own subsubsection later on.}

\todoi{missing patterns also need a case: we need to calculate
  these. explain what kind of theorems we need here and how we can use
  \verb+False_rec+. Refer to later subsubsections for calculation of
  missing pats and generation of proofs.}

\subsubsection{Calculating the missing patterns}
\label{sec:genmispat}

\todoi{explain the general idea, basically paraphrasing that one
  StackOverflow post. Maybe should also cite Augustsson's paper.}

\subsubsection{Inversion theorems and their proofs}
\label{sec:genproof}

\todoi{Explain the gist of it: for recursive calls: we need to select
  the right field of the right constructor. Explain the tactics we use
  for this. For the theorems for missing patterns: we need to prove
  that if we have a proof of termination, then the input cannot match
  with the given pattern. This can then just be done by a simple
  proof.}

\subsubsection{Examples}
\label{sec:genexamples}

Consider the |quicksort| example given above. We can tell the
HsToGallina tool to translate that definition using the following pragma:

\begin{code}
{-"\text{\{-\# OPTIONS\_Hs2Gallina bc: quicksort \#-\}}"-}
\end{code}

The tool will then generate the following (we renamed \verb+quicksort+
to \verb+qs+ to make it all fit on paper and left out the proofs of
the inversion theorems):

\begin{verbatim}
...

Inductive qs_acc : List Nat -> Prop :=
  | qs_acc_0 : qs_acc nil
  | qs_acc_1 : forall (x : Nat) (xs : List Nat) , 
                        qs_acc (filter (gt x) xs) -> 
                        qs_acc (filter (le x) xs) -> 
                        qs_acc (cons x xs).

Theorem qs_acc_inv_1_0 : forall (x0 : List Nat) (x : Nat) (xs : List Nat),
  qs_acc x0 -> (x0 = cons x xs) -> qs_acc (filter (gt x) xs).
...
Defined.

Theorem qs_acc_inv_1_1 : forall (x0 : List Nat) (x : Nat) (xs : List Nat),
  qs_acc x0 -> (x0 = cons x xs) -> qs_acc (filter (le x) xs).
...
Defined.

...

Fixpoint qs (x0 : List Nat) (x1 : qs_acc x0) : List Nat :=
  match x0 as _y0 return (x0 = _y0) -> List Nat with
    | nil => fun _h0 => 
               nil
    | cons x xs => fun _h0 => 
               append (qs (filter (gt x) xs) (qs_acc_inv_1_0 x1 _h0)) 
                      (qs (filter (le x) xs) (qs_acc_inv_1_1 x1 _h0))
           end (refl_equal x0).

...
\end{verbatim}

The definition of |head| as outputted by our tool:

\begin{verbatim}
Inductive head_acc ( a : Set ) : List a -> Prop :=
  | head_acc_0 : forall (x : a) (_xs : List a), head_acc (cons x _xs).

Theorem head_acc_non_0 : forall (a : Set) (x0 : List a),
  head_acc x0 -> (x0 = nil) -> Logic.False.
...
Defined.

Definition head { a : Set } (x0 : List a) (x1 : head_acc x0) : a :=
  match x0 as _y0 return (x0 = _y0) -> a with
    | cons x _xs => fun _h0 => x
    | nil => fun _h0 => False_rec a (head_acc_non_0 x1 _h0)
  end (refl_equal x0).
\end{verbatim}

The definition itself is not too exciting, but when we want to use
this function on some input \verb+e : List a+, we still have to give a
proof \verb+p : head_acc e+. The \verb+refine+ tactic is particularly
useful here. Consider for example the function |headReverse x xs =
head (reverse (x : xs))|: we know that |reverse| preserves the length
of a list, so the pattern match in |head| will not fail. The Coq
translation of this would become:

\begin{verbatim}
Definition headReverse {a : Set} (x: a) (xs : List a) : a.
refine (head (reverse (x :: xs)) _).
...
Defined.
\end{verbatim}

We have left out the proof as it is rather involved: we have to proof
that we can construct a \verb+h+ and \verb+t+ such that
\verb+reverse (x :: xs) = h :: t+, for any \verb+x+ and \verb+xs+.

The extracted Haskell code of this fragment has non of the proofs and
looks almost the same as our original code:

\begin{code}
headReverse :: a1 -> (List a1) -> a1
headReverse x xs =
  head (rev ((:) x xs))
\end{code}

\section{Coinduction}
\label{sec:coind}

A limitation of a direct translation is that in Coq there is a
distinction between inductive and coinductive data types. If we for
example want to work with infinite lists in Coq, we have to make a
separate coinductive data type. With the \verb+codata+ and
\verb+cofix+ pragmas, we can indicate that we want a coinductive
translation of our top-level definitions. For example, if we want to
define an infinite stream of zeroes, we can write something as
follows:

\begin{code}
{-"\text{\{-\# OPTIONS\_Hs2Gallina codata: Stream \#-\}}"-}
{-"\text{\{-\# OPTIONS\_Hs2Gallina cofix: zeroes  \#-\}}"-}

...

data Stream a = Cons a (Stream a)

zeroes :: Stream Nat
zeroes = Cons 0 zeroes

\end{code}

translates to:

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

\section{Extraction}
\label{sec:extraction}

Once we have verified and possibly modified the Gallina code, such
that it actually satisfies the properties we wanted to prove, we can
translate the code back to Haskell using Coq's extraction
mechanism. The translation has been done in such a way that the
extracted code will still have the same types as before (up to
$\alpha$-equivalence), the Bove-Capretta proofs are also removed,
since they all the predicates live in \verb+Prop+, and the coinductive
definitions are extracted to normal Haskell definitions.

Since Coq's type system does not map nicely to Haskell's, it sometimes
uses |unsafeCoerce| to convince GHC's type checker. However, Coq
produces broken Haskell code when it needs |unsafeCoerce|. Even though
this is just a minor syntactic fault that we can fix by a very simple
\verb+sed+ script, it does leave a sour taste.

\section{Prelude}
\label{sec:prelude}

Now that we have a mapping from a subset of the Haskell syntax to
Gallina syntax, we also want to have some support for the Haskell
Prelude. We have achieved this by writing our own Coq Prelude which
implements definitions from the Haskell Prelude as defined in the
Haskell Report.

Apart from implementing the functions, which sometimes just means
picking a definition from the Coq standard library and filling in the
correct parameters, we also specify how these definitions should be
extracted.

Since we do not support all of Haskell 98, we also cannot support all
of the Haskell 98 Prelude. For example, we skipped all the definitions
that need type classes such as the numeric operations.

More interesting cases are functions that have non-exhaustive pattern
matches, e.g. |head| and |tail|. For these functions we have used the
Bove-Capretta method to define them.

So far we have only considered the list functions on finite lists;
e.g. sometimes we want to perform a |take| on an infinite list, which
with the current approach is not possible. We could define two
versions of |take|: an recursive and a corecursive definition, but
this means that whenever we call |take| in our Haskell code, our tool
needs to infer whether we want the recursive or the corecursive
definition, which gets complicated very quickly. We also do not
support functions such as |iterate| and |repeat|, that always produce
infinite lists. We can implement similar functions, but they would
then work on streams instead of lists.

The function |until| is not supported as it is obviously not
structurally recursive, since it the termination behaviour of this
function depends non-trivially on the given input. So it is better for
the user to provide special purpose functions that are less general
instead.

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

\todoi{We can automate a large portion of the translation process.}

\todoi{We still need the QuickCheck tests to see if the extracted code
  makes sense, i.e. nothing has been proved about that.}


\bibliographystyle{plain}
\bibliography{report}

\end{document}
