%include polycode.fmt

\usepackage[T1]{fontenc}

\usetheme{Madrid}
\usecolortheme{dolphin}
\setbeamertemplate{navigation symbols}{} 

\title[Translating Haskell to Coq]{Translating Haskell programs to Coq programs}
\institute[Utrecht University]{Department of Information and Computing
  Sciences\\Faculty of Science, Utrecht University}

\author[G. Dijkstra]{Gabe Dijkstra}

\date{February 21st, 2013}

\begin{document}


\begin{frame}
\maketitle
\note{|.| Title page}
\end{frame}

\section{Motivation}

\begin{frame}\frametitle{Motivation}
  \note{|.| Motivate stuff here, obviously.}
  \begin{itemize}
  \item Suppose we have written a well-typed Haskell program
  \item No guarantees on:
    \begin{itemize}
    \item termination
    \item pattern match failures (in the presence of non-exhaustive patterns)
    \end{itemize}
  \item 

  \end{itemize}

\end{frame}

\subsection{Coq introduction}

\begin{frame}\frametitle{Coq introduction}
  \note{|.| Introduce Coq stuff here, obviously.}
\end{frame}

\subsection{Goal}

\begin{frame}\frametitle{Goal}
  \note{|.| Ok, so we have a nice system to do verification in, but we
    still need to translate everything to something Coq understands.}
\end{frame}

\section{Translating data types}

\begin{frame}\frametitle{Translating data types}
  \note{|.| Let's have a look at how we can translate Haskell data types\vspace{1.5ex}\\}
  
  \note{|.| List data type\vspace{1.5ex}\\}

  \note{|.| With one type parameter\vspace{1.5ex}\\}

  \note{|.| Can be translated using the Inductive command.\vspace{1.5ex}\\}

  \note{|.| Syntax that's similar to GADT syntax.\vspace{1.5ex}\\}

  \note{|.| Also notice that it's more explicit.\vspace{1.5ex}\\}

  \note{|.| We have to give the kind of the data type.\vspace{1.5ex}\\}

  \note{|.| We have to give the kind of the type parameters.\vspace{1.5ex}\\}

  \note{|.| PAUSE for assumption!\vspace{1.5ex}\\}

  \note<2->{|.| We assume every type parameter to have kind star.\vspace{1.5ex}\\}

  \note<2->{|.| User has to change this manually if a type parameter has some other kind.\vspace{1.5ex}\\}

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
  \note{|.| Now that we know how to translate data types:\vspace{1.5ex}\\}
  \note{|.| Let's have a look at function definitions.\vspace{1.5ex}\\}
  \note{|.| Here we see a function |k| (better known as |const|), which is polymorphic.\vspace{1.5ex}\\}
  \note{|.| Parametric polymorphism does not exist in Coq.\vspace{1.5ex}\\}
  \note{|.| We solve this using implicit variables.\vspace{1.5ex}\\}
  \note{|.| Curly braces indicate that |a| and |b| are implicit variables.\vspace{1.5ex}\\}
  \note{|.| Need not be given when calling this function |k|.\vspace{1.5ex}\\}
  \note{|.| Coq can infer which type parameter it needs to fill in at the call site.\vspace{1.5ex}\\}
  \note{|.| PAUSE for type parameter has kind star assumption!\vspace{1.5ex}\\}
  \note<2->{|.| Type parameter has kind star assumption!\vspace{1.5ex}\\}

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
  \note{|.| One might ask the question whether this always works?\vspace{1.5ex}\\}
  \note{|.| Let's look at the other well-known combinator, |s|\vspace{1.5ex}\\}
  \note{|.| We know that the identity combinator, |i|, can be written as |s k k|\vspace{1.5ex}\\}
  \note{|.| So let's try to translate this definition of the combinator |i|.\vspace{1.5ex}\\}
  \note{|.| PAUSE for error!\vspace{1.5ex}\\}
  \note<2->{|.| If we try to type check this, Coq will tell us that it cannot infer all type parameters.\vspace{1.5ex}\\}
  \note<2->{|.| If we do the type inference by hand, we can see why.\vspace{1.5ex}\\}
  \note<2->{|.| The type parameter Coq talks about is indeed left free.\vspace{1.5ex}\\}
  \note<2->{|.| And if we look at the GHC-Core output, we see that GHC fills in |GHC.Prim.Any|.\vspace{1.5ex}\\}

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
  \note{|.| In Coq every definition has to be total\vspace{1.5ex}\\}
  \note{|.| It has to terminate\vspace{1.5ex}\\}
  \note{|.| Its pattern matches have to be exhaustive\vspace{1.5ex}\\}
  \note{|.| Non-terminating definitions can be used to prove anything\vspace{1.5ex}\\}
  \note{|.| which would make the system inconsistent\vspace{1.5ex}\\}
  \note{|.| Coq checks whether\vspace{1.5ex}\\}
  \note{|.| Every recursive call is done on structurally smaller arguments\vspace{1.5ex}\\}
  \note{|.| Every pattern match is exhaustive\vspace{1.5ex}\\}

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
  \note{|.| Show that foldr fits these restrictions\vspace{1.5ex}\\}

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
  \note{|.| If we try this then PAUSE\vspace{1.5ex}\\}
  \note<2->{|.| Coq complains that the pattern match is non-exhaustive\vspace{1.5ex}\\}

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
  \note{|.| If we try this then PAUSE\vspace{1.5ex}\\}
  \note<2->{|.| Coq complains that the definition is ill-formed\vspace{1.5ex}\\}
  \note<2->{|.| It does not fit the structural recursion pattern: \vspace{1.5ex}\\}
  \note<2->{|.| recursive calls are not done on |xs| but on |filter| something |xs|: \vspace{1.5ex}\\}
  \note<2->{|.| it cannot see that this structurally smaller than |(x : xs)|  \vspace{1.5ex}\\}

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
    subject of study for many years now, so:\vspace{1.5ex}\\}
  \note{|.| There are several ways to embed general recursion in Coq\vspace{1.5ex}\\}
  \note{|.| We have the following requirements:\vspace{1.5ex}\\}
  \note{|.| Needs to allow for non-exhaustive pattern matches\vspace{1.5ex}\\}
  \note{|.| Extracted definitions have to have the same types as the original definitions\vspace{1.5ex}\\}
  \note{|.| Bove-Capretta method meets all our requirements\vspace{1.5ex}\\}
  \note{|.| which is why we chose to implement this method\vspace{1.5ex}\\}

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

  \note{|.| Generate a predicate from the function definition\vspace{1.5ex}\\}
  \note{|.| Predicate is indexed by the arguments of the function\vspace{1.5ex}\\}
  \note{|.| Proofs of the predicate encode call graph for that particular input\vspace{1.5ex}\\}
  \note{|.| Structurally recurse on these proofs\vspace{1.5ex}\\}
  \note{|.| Coq's totality checker ensures that we only construct finite call graphs\vspace{1.5ex}\\}
  \note{|.| This will sound a bit vague right now, so let's take a look at some examples\vspace{1.5ex}\\}

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
  \note{|.| As one can see, things get ugly really quickly\vspace{1.5ex}\\}
  
  \note{|.| Luckily, our tool automates all the boring, ugly parts\vspace{1.5ex}\\}

  \note{|.| In practice, when proving properties about the function:\vspace{1.5ex}\\}

  \note{|.| We only have to use the predicate, which looks a lot like
    the original function definition, possibly even
    cleaner!\vspace{1.5ex}\\}

  Our tool can generate:

  \begin{itemize}
  \item the Bove-Capretta predicate
  \item the theorems needed for the new function definition
  \item the new function definition
  \end{itemize}
  
\end{frame}



\section{Conclusion}

\begin{frame}\frametitle{Conclusion}
  \note{|.| Concluding this presentation, we have written a tool that:\vspace{1.5ex}\\}
  \note{|.| Can translate a subset of Haskell 98 to Coq\vspace{1.5ex}\\}
  \note{|.| Automates the ``boring parts'' of the Bove-Capretta method\vspace{1.5ex}\\}
  \note{|.| (Not in this presentation:) has some support for the Prelude\vspace{1.5ex}\\}
  \note{|.| (Not in this presentation:) supports infinite data structures using coinduction\vspace{1.5ex}\\}
  \note{|.| For the curious: the code can be found on my GitHub \vspace{1.5ex}\\}
  \note{|.| This concludes the presentation. Any questions? \vspace{1.5ex}\\}
  \note{|.| WARNING WARNING Emergency slides after this!  \vspace{1.5ex}\\}

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

\subsection{Using the Bove-Capretta method}
\begin{frame}\frametitle{Using the Bove-Capretta method}
  \note{|.| Suppose we want to call a function defined using B-C method.\vspace{1.5ex}\\}

  \note{|.| User has to provide the proof of the predicate\vspace{1.5ex}\\}

  \note{|.| refine tactic is really useful here\vspace{1.5ex}\\}

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
