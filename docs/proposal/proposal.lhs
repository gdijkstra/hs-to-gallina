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
We want to write a tool that automatically translates Haskell code to
Gallina code.

\section{Supported language fragment}

Since Haskell is a language with a lot of features, it is unrealistic
to expect that we can support every single one of them right away. The
language fragment that we aim to support is Haskell 98 without the
following features:

\begin{itemize}
\item typeclasses
\item do-notation and list comprehensions
\item record syntax
\end{itemize}

\section{Parametric polymorphism}

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

\section{General recursion}

Since Coq only allows structural recursion, not all recursive Haskell
definitions can translated directly into Gallina. In order to deal
with some of these cases, we can generate Bove-Capretta predicates
from the original function definition and rewrite the function
definition using this predicate.

With the ``bc'' pragma we can specify of which definitions we want to
generate Bove-Capretta predicates:

\begin{code}
{-"\text{\{-\# OPTIONS\_HsToGallina bc: quicksort \#-\}}"-}

...

quicksort :: [Nat] -> [Nat]
quicksort []      =  []
quicksort (x:xs)  =  quicksort (filter (< x) xs) ++
                     quicksort (filter (>= x) xs)
\end{code}

This method does not work well with nested recursion as we will need
to simultaneously define the predicate and the function, which is
something that cannot be done in Coq.

\section{Coinduction}

Another limitation of a direct translation is that in Coq there is a
distinction between inductive and coinductive data types. If we for
example want to work with infinite lists in Coq, we have to make a
separate coinductive data type. With the ``codata'' and ``cofix''
pragmas, we can indicate that we want a coinductive translation of our
definitions.

\begin{code}
{-"\text{\{-\# OPTIONS\_HsToGallina codata: Stream \#-\}}"-}
{-"\text{\{-\# OPTIONS\_HsToGallina cofix: zeroes  \#-\}}"-}

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

% note that we have left out some implicit argument stuff.

Just as we have restrictions as to what recursive definitions we can
specify in Coq, we have similar restrictions for corecursive
definitions: every corecursive call should be \emph{guarded} by a
constructor. Our tool will not check whether this is the case and will
just blindly translate the Haskell definitions.


\section{Modules}

Since one probably will only verify a single Haskell module,
pretending all the imported functions have already been verified. We
want the tool to facilitate this strategy. For example, generate
appropriate axioms for the imported definitions, such that if we
extract the Haskell module from the Coq script, we can plug it back in
our Haskell software without having to change the resulting code
manually.

\end{document}
