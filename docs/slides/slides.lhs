%include polycode.fmt

\usepackage[T1]{fontenc}

\usetheme{Madrid}
\usecolortheme{dolphin}
\setbeamertemplate{navigation symbols}{} 
\usepackage{appendixnumberbeamer}

\title[Translating Haskell to Coq]{Translating Haskell programs to Coq programs}
\institute[Utrecht University]{Department of Information and Computing
  Sciences\\Faculty of Science, Utrecht University}

\author[G. Dijkstra]{Gabe Dijkstra}

\date{February 21st, 2013}

\begin{document}


\begin{frame}
\maketitle
\note{Go slow!\vspace{3ex}\\}

\note{|.| I'm going to talk about my experimentation project I did under the supervision of Wouter Swierstra\vspace{1ex}\\}

\note{|.| which is about automatically translating Haskell programs to Coq programs\vspace{1ex}\\}
\end{frame}

\section{Motivation}

\begin{frame}\frametitle{Motivation}
  \note{|.|  Suppose we have written a well-typed Haskell program\vspace{1ex}\\}
  \note{|.|  Being well-typed gives us some guarantees, but doesn't say anything about\vspace{1ex}\\}
  \note{|.|  termination\vspace{1ex}\\}
  \note{|.|  pattern match failures\vspace{1ex}\\}
  \note{|.|  sort example even though it type checks, its clearly not correct (except for the empty list)\vspace{1ex}\\}
  \note{|.|  Haskell types are not very expressive\vspace{1ex}\\}
  \note{|.| we cannot easily express in the type that the resulting
    list is a sorted permutation of the input\vspace{1ex}\\}
  \note{|.|  PAUSE catch phrase after the PAUSE\vspace{1ex}\\}
  \note<2->{|.| We want to formally verify correctness of a Haskell program using Coq\vspace{1ex}\\}

  \begin{itemize}
  \item Suppose we have written a well-typed Haskell program
  \item This gives us no guarantees on:
    \begin{itemize}
    \item termination
    \item pattern match failures (in the presence of non-exhaustive patterns)
    \end{itemize}
  \item Correctness:
    \begin{code}
      sort :: [Int] -> [Int]
      sort _ = []
    \end{code}
  \item<2-> We want to formally verify Haskell code using the proof assistant Coq
  \end{itemize}

\end{frame}

\subsection{Coq introduction}

\begin{frame}\frametitle{Coq introduction}
  \note{|.| Since some of you may not be familiar with Coq\vspace{1ex}\\}

  \note{|.| I will give a very brief overview of the system\vspace{1ex}\\}

  \note{|.| Coq is an interactive theorem prover\vspace{1ex}\\}
  \note{|.| Built upon the principle : propositions as (dependent) types\vspace{1ex}\\}
  \note{|.| In which: proofs as programs of the corresponding type\vspace{1ex}\\}
  \note{|.| Proofs are written in Coq's specification language, Gallina \vspace{1ex}\\}
  \note{|.| This is essentially a functional programming language\vspace{1ex}\\}
  \note{|.| We can write these proofs directly in Gallina\vspace{1ex}\\}
  \note{|.| ...or using tactics (which is not the focus of this presentation)\vspace{1ex}\\}
  \note{|.| PAUSE extraction stuff after PAUSE\vspace{1ex}\\}
  \note<2->{|.| from proofs we can extract the functional program to Haskell\vspace{1ex}\\}
  \note<2->{|.| so we can use the verified code in a larger development\vspace{1ex}\\}

  \begin{itemize}
  \item Coq is an interactive theorem prover
  \item Propositions as (dependent) types
  \item Proofs as programs
  \item Gallina is Coq's specification language 
  \item Essentially a functional programming language
  \item We can write proofs using Gallina directly
  \item ...or interactively using tactics
  \item<2-> Extraction
  \end{itemize}
\end{frame}

\subsection{Goal}

\begin{frame}\frametitle{Goal}
  \note{|.| Ok, so we have decided that we want to verify our Haskell
    code using Coq.\vspace{1ex}\\}
  
  \note{|.| Before we can do this: we need to first translate
    everything to Gallina \vspace{1ex}\\}

  \note{|.| This is tedious and rather error-prone \vspace{1ex}\\}

  \note{|.| It would be nice if we had a tool that did this \vspace{1ex}\\}

  \note{|.| In such a way that the extracted code can replace the original \vspace{1ex}\\}

  \note{|.| (This means that the types of the definitions in extracted
    code need to be the same as the ones of the original
    definitions.)\vspace{1ex}\\}

  \note{|.| Of course, it's not realistic to think that we can support
    all of HAskell right away\vspace{1ex}\\}

  \note{|.| Restrict ourselves to Haskell 98 without type classes\vspace{1ex}\\}

  \note{|.| single module with only implicit Prelude import \vspace{1ex}\\}

  \note{|.| PAUSE for top-level definition type sig PAUSE \vspace{1ex}\\}

  \note<2->{|.| assume every top-level definition has type sig \vspace{1ex}\\}

  Translating Haskell code to Gallina by hand is tedious and prone to
  subtle mistakes.

  \begin{itemize}
  \item We want to automate this process
  \item Extracted code needs to be compatible with the original
  \item Restrict ourselves to:
    \begin{itemize}
    \item Haskell 98 without type classes
    \item Single Haskell module with only implicit Prelude import
    \item No extensions
    \end{itemize}
  \item<2-> We assume that every top-level definition has a type signature 
  \end{itemize}

\end{frame}

\section{Translating data types}

\begin{frame}\frametitle{Translating data types}
  \note{|.| Let's have a look at how we can translate Haskell data types\vspace{1ex}\\}
  
  \note{|.| List data type\vspace{1ex}\\}

  \note{|.| With one type parameter\vspace{1ex}\\}

  \note{|.| Can be translated using the Inductive command.\vspace{1ex}\\}

  \note{|.| Syntax that's similar to GADT syntax.\vspace{1ex}\\}

  \note{|.| Also notice that it's more explicit.\vspace{1ex}\\}

  \note{|.| We have to give the kind of the data type.\vspace{1ex}\\}

  \note{|.| We have to give the kind of the type parameters.\vspace{1ex}\\}

  \note{|.| PAUSE for assumption!\vspace{1ex}\\}

  \note<2->{|.| We assume every type parameter to have kind star.\vspace{1ex}\\}

  \note<2->{|.| User has to change this manually if a type parameter has some other kind.\vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      data List a = Nil | Cons a (List a)
    \end{code}
  \end{block}

  \begin{block}{Translation}
\begin{verbatim}
Inductive List ( a : Set ) : Set :=
  | Nil : List a
  | Cons : a -> List a -> List a.
\end{verbatim}
  \end{block}

  \uncover<2->{We assume every type parameter to have kind |*|.}

\end{frame}

\section{Dealing with parametric polymorphism}

\begin{frame}\frametitle{Dealing with parametric polymorphism}
  \note{|.| Now that we know how to translate data types:\vspace{1ex}\\}
  \note{|.| Let's have a look at function definitions.\vspace{1ex}\\}
  \note{|.| Here we see a function |k| (better known as |const|), which is polymorphic.\vspace{1ex}\\}
  \note{|.| Parametric polymorphism does not exist in Coq.\vspace{1ex}\\}
  \note{|.| We solve this using implicit variables.\vspace{1ex}\\}
  \note{|.| Curly braces indicate that |a| and |b| are implicit variables.\vspace{1ex}\\}
  \note{|.| Need not be given when calling this function |k|.\vspace{1ex}\\}
  \note{|.| Coq can infer which type parameter it needs to fill in at the call site.\vspace{1ex}\\}
  \note{|.| PAUSE for type parameter has kind star assumption!\vspace{1ex}\\}
  \note<2->{|.| Type parameter has kind star assumption!\vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      k :: a -> b -> a 
      k a _ = a
    \end{code}
  \end{block}

  \begin{block}{Translation}
\begin{verbatim}
Definition k { a b : Set }
  (x0 : a) (x1 : b) : a :=
  match x0, x1 with
    | a, _ => a
  end.
\end{verbatim}
  \end{block}

  \begin{itemize}
  \item<2-> Again, we assume every type parameter to have kind |*|.
  \end{itemize}
\end{frame}

\begin{frame}
  \note{|.| One might ask the question whether this always works?\vspace{1ex}\\}
  \note{|.| Let's look at the other well-known combinator, |s|\vspace{1ex}\\}
  \note{|.| We know that the identity combinator, |i|, can be written as |s k k|\vspace{1ex}\\}
  \note{|.| So let's try to translate this definition of the combinator |i|.\vspace{1ex}\\}
  \note{|.| PAUSE for error!\vspace{1ex}\\}
  \note<2->{|.| If we try to type check this, Coq will tell us that it cannot infer all type parameters.\vspace{1ex}\\}
  \note<2->{|.| If we do the type inference by hand, we can see why.\vspace{1ex}\\}
  \note<2->{|.| The type parameter Coq talks about is indeed left free.\vspace{1ex}\\}
  \note<2->{|.| And if we look at the GHC-Core output, we see that GHC fills in |GHC.Prim.Any|.\vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      s :: (a -> b -> c) -> (a -> b) -> a -> c
      s p q r = p r (q r)
    \end{code}
  \end{block}

  \begin{itemize}
  \item We know that |i = s k k|.
  \end{itemize}

  \begin{block}{Translation}
\begin{verbatim}
Definition i { a : Set } : a -> a :=
  s k k.
\end{verbatim}
  \end{block}

\uncover<2->{
\begin{verbatim}
Error: Cannot infer the implicit parameter b of k.
\end{verbatim}
}

\end{frame}

\section{Recursion and partiality}

\begin{frame}\frametitle{Recursion and partiality}
  \note{|.| In Coq every definition has to be total\vspace{1ex}\\}
  \note{|.| It has to terminate\vspace{1ex}\\}
  \note{|.| Its pattern matches have to be exhaustive\vspace{1ex}\\}
  \note{|.| Non-terminating definitions can be used to prove anything\vspace{1ex}\\}
  \note{|.| which would make the system inconsistent\vspace{1ex}\\}
  \note{|.| Coq checks whether\vspace{1ex}\\}
  \note{|.| Every recursive call is done on structurally smaller arguments\vspace{1ex}\\}
  \note{|.| Every pattern match is exhaustive\vspace{1ex}\\}

  \begin{itemize}
  \item In Coq every definition has to be total
    \begin{itemize}
    \item It has to terminate
    \item Its pattern matches have to be exhaustive
    \end{itemize}
  \item Non-terminating definitions can be used to prove anything
    \begin{itemize}
    \item which would make the system inconsistent
    \end{itemize}
  \item Coq checks whether
    \begin{itemize}
    \item Every recursive call is done on structurally smaller arguments
    \item Every pattern match is exhaustive
    \end{itemize}
  \end{itemize}

\end{frame}

\begin{frame}\frametitle{Recursion and partiality (cont.d)}
  \note{|.| Show that foldr fits these restrictions\vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      foldr :: (a -> b -> b) -> b -> [a] -> b
      foldr op e []      = e
      foldr op e (x:xs)  = op x (foldr op e xs)
    \end{code}
  \end{block}

  \begin{block}{Translation}
\begin{verbatim}
Fixpoint foldr { a b : Set } 
  (x0 : a -> b -> b) (x1 : b) (x2 : List a) : b :=
  match x0, x1, x2 with
    | op, e, nil       => e
    | op, e, cons x xs => op x (foldr op e xs)
  end.
\end{verbatim}
  \end{block}

\end{frame}

\subsection{Partiality: |head|}
\begin{frame}\frametitle{Partiality: |head|}
  \note{|.| If we try this then PAUSE\vspace{1ex}\\}
  \note<2->{|.| Coq complains that the pattern match is non-exhaustive\vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      head :: [a] -> a 
      head (x:xs) = x
    \end{code}
  \end{block}

  \begin{block}{Translation}
\begin{verbatim}
Definition head { a : Set } (x0 : List a) : a :=
  match x0 with
    | cons x xs => x
  end.
\end{verbatim}
  \end{block}

\uncover<2->{
\begin{verbatim}
Error: Non exhaustive pattern-matching: no clause 
       found for pattern nil
\end{verbatim}
}

\end{frame}

\subsection{Non-structural recursion: |quicksort|}
\begin{frame}\frametitle{Non-structural recursion: |quicksort|}
  \note{|.| If we try this then PAUSE\vspace{1ex}\\}
  \note<2->{|.| Coq complains that the definition is ill-formed\vspace{1ex}\\}
  \note<2->{|.| It does not fit the structural recursion pattern: \vspace{1ex}\\}
  \note<2->{|.| recursive calls are not done on |xs| but on |filter| something |xs|: \vspace{1ex}\\}
  \note<2->{|.| it cannot see that this structurally smaller than |(x : xs)|  \vspace{1ex}\\}

  \begin{block}{Haskell code}
    \begin{code}
      quicksort :: [Nat] -> [Nat] 
      quicksort []        = []
      quicksort (x : xs)  = append  (quicksort (filter (gt x) xs)) 
                                    (quicksort (filter (le x) xs))
    \end{code}
  \end{block}

  \begin{block}{Translation}
\begin{verbatim}
Fixpoint quicksort (x0 : List Nat) : List Nat :=
  match x0 with
    | nil => nil
    | cons x xs => append (quicksort (filter (gt x) xs)) 
                          (quicksort (filter (le x) xs))
  end.
\end{verbatim}
  \end{block}

\uncover<2->{
\begin{verbatim}
Error: Recursive definition of quicksort is ill-formed.
...
\end{verbatim}
}

\end{frame}

\section{General recursion in Coq}
\begin{frame}\frametitle{General recursion in Coq}

  \note{|.| Of course, embedding general recursion in Coq has been the
    subject of study for many years now, so:\vspace{1ex}\\}
  \note{|.| There are several ways to embed general recursion in Coq\vspace{1ex}\\}
  \note{|.| We have the following requirements:\vspace{1ex}\\}
  \note{|.| Needs to allow for non-exhaustive pattern matches\vspace{1ex}\\}
  \note{|.| Extracted definitions have to have the same types as the original definitions\vspace{1ex}\\}
  \note{|.| Bove-Capretta method meets all our requirements\vspace{1ex}\\}
  \note{|.| which is why we chose to implement this method\vspace{1ex}\\}

  \begin{itemize}
  \item There are several ways to embed general recursion in Coq
  \item We have the following requirements:
    \begin{itemize}
    \item Needs to allow for non-exhaustive pattern matches
    \item Extracted definitions have to have the same types as the
      original definitions
    \end{itemize}
  \item Bove-Capretta method meets all our requirements
  \end{itemize}
  
\end{frame}

\section{Bove-Capretta method}
\begin{frame}\frametitle{Bove-Capretta method}

  \note{|.| Generate a predicate from the function definition\vspace{1ex}\\}
  \note{|.| Predicate is indexed by the arguments of the function\vspace{1ex}\\}
  \note{|.| Proofs of the predicate encode call graph for that particular input\vspace{1ex}\\}
  \note{|.| Structurally recurse on these proofs\vspace{1ex}\\}
  \note{|.| Coq's totality checker ensures that we only construct finite call graphs\vspace{1ex}\\}
  \note{|.| This will sound a bit vague right now, so let's take a look at some examples\vspace{1ex}\\}

  \begin{itemize}
  \item Generate a predicate from the function definition
  \item Predicate is indexed by the arguments of the function
  \item Proofs of the predicate encode call graph for that particular input
  \item Structurally recurse on these proofs
  \item Coq's totality checker ensures that we only construct finite call graphs
  \end{itemize}

\end{frame}


\subsection{|head| example}
\begin{frame}\frametitle{|head| example}
  \note{Explain the predicate here and the function. Explain Prop stuff}

  {\small
    \begin{code}
      head :: [a] -> a 
      head (x:xs) = x
    \end{code}
  }

  \begin{block}{Predicate}
    {\small
\begin{verbatim}
Inductive head_acc ( a : Set ) : List a -> Prop :=
  | head_acc_0 : forall (x : a) (_xs : List a), 
                   head_acc (cons x _xs).
\end{verbatim}
    }
  \end{block}

  \begin{block}{Gallina function definition}
    {\small
\begin{verbatim}
Definition head { a : Set } 
  (x0 : List a) (x1 : head_acc x0) : a :=
  match x0 as _y0 return (x0 = _y0) -> a with
    | cons x _xs => fun _h0 => x
    | nil => fun _h0 => False_rec a (head_acc_non_0 x1 _h0)
  end (refl_equal x0).
\end{verbatim}
    }
  \end{block}


\end{frame}

\subsection{|qs| example}
\begin{frame}\frametitle{|qs| example}
  \note{Explain the accessibility predicate here. Explain Prop stuff!
    We cannot pattern match!}

  {\small
    \begin{code}
      {-"\text{\{-\# OPTIONS\_HsToGallina bc: qs \#-\}}"-}
      
      qs           ::  [Nat] -> [Nat]
      qs []        =  []
      qs (x : xs)  =  append  (qs (filter (gt x) xs))
                              (qs (filter (le x) xs))
    \end{code}
  }

  \begin{block}{Predicate}
    {\small
\begin{verbatim}
Inductive qs_acc : List Nat -> Prop :=
  | qs_acc_0 : qs_acc nil
  | qs_acc_1 : forall (x : Nat) (xs : List Nat) , 
                        qs_acc (filter (gt x) xs) -> 
                        qs_acc (filter (le x) xs) -> 
                        qs_acc (cons x xs).
\end{verbatim}
      }
  \end{block}
\end{frame}

\begin{frame}\frametitle{|qs| example (cont.d)}
  \note{Explain the function here. There's lots of stuff going on
    here. Repeat Prop stuff! We cannot pattern match!}

  \begin{block}{Gallina function definition}
{\small
\begin{verbatim}
Fixpoint qs (x0 : List Nat) (x1 : qs_acc x0) : List Nat :=
  match x0 as _y0 return (x0 = _y0) -> List Nat with
    | nil       => fun _h0 => nil
    | cons x xs => fun _h0 => 
               append (qs (filter (gt x) xs) 
                                  (qs_acc_inv_1_0 x1 _h0)) 
                      (qs (filter (le x) xs) 
                                  (qs_acc_inv_1_1 x1 _h0))
           end (refl_equal x0).
\end{verbatim}
}
  \end{block}

\end{frame}

\subsection{Bove-Capretta method implementation}
\begin{frame}\frametitle{Bove-Capretta method implementation}
  \note{|.| As one can see, things get ugly really quickly\vspace{1ex}\\}
  
  \note{|.| Luckily, our tool automates all the boring, ugly parts\vspace{1ex}\\}

  \note{|.| In practice, when proving properties about the function:\vspace{1ex}\\}

  \note{|.| We only have to use the predicate, which looks a lot like
    the original function definition, possibly even
    cleaner!\vspace{1ex}\\}

  Our tool can generate:

  \begin{itemize}
  \item the Bove-Capretta predicate
  \item the theorems needed for the new function definition
  \item the new function definition
  \end{itemize}
  
\end{frame}



\section{Conclusion}

\begin{frame}\frametitle{Conclusion}
  \note{|.| Concluding this presentation, we have written a tool that:\vspace{1ex}\\}
  \note{|.| Can translate a subset of Haskell 98 to Coq\vspace{1ex}\\}
  \note{|.| Automates the ``boring parts'' of the Bove-Capretta method\vspace{1ex}\\}
  \note{|.| (Not in this presentation:) has some support for the Prelude\vspace{1ex}\\}
  \note{|.| (Not in this presentation:) supports infinite data structures using coinduction\vspace{1ex}\\}
  \note{|.| For the curious: the code can be found on my GitHub \vspace{1ex}\\}
  \note{|.| This concludes the presentation. Any questions? \vspace{1ex}\\}
  \note{|.| WARNING WARNING Emergency slides after this!  \vspace{1ex}\\}

  We have written a tool that:

  \begin{itemize}
  \item Can translate a subset of Haskell 98 to Coq
  \item Automates the ``boring parts'' of the Bove-Capretta method
  \item Has some support for the Prelude
  \item Supports infinite data structures using coinduction
  \item For the curious: \verb+https://github.com/gdijkstra/hs-to-gallina+
  \end{itemize}

\end{frame}

% Backup slides!
\appendix


\subsection{Using the Bove-Capretta method}
\begin{frame}\frametitle{Using the Bove-Capretta method}
  \note{|.| Suppose we want to call a function defined using B-C method.\vspace{1ex}\\}

  \note{|.| User has to provide the proof of the predicate\vspace{1ex}\\}

  \note{|.| refine tactic is really useful here\vspace{1ex}\\}

  \begin{itemize}
  \item |headReverse x xs = head (reverse (x :: xs))| never crashes
  \item We can use the \verb+refine+ tactic here.
  \item The user has to provide proofs here.
  \end{itemize}

{\small
\begin{verbatim}
Definition headReverse {a : Set} (x: a) (xs : List a) : a.
refine (head (reverse (x :: xs)) _).
<proof omitted>
Defined.
\end{verbatim}
}
\end{frame}


\end{document}
