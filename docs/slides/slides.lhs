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
\note{Title page}
\end{frame}

\section{Motivation}

\begin{frame}\frametitle{Motivation}
  \note{Motivate stuff here, obviously.}
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
  \note{Introduce Coq stuff here, obviously.}
\end{frame}

\subsection{Goal}

\begin{frame}\frametitle{Goal}
  \note{Ok, so we have a nice system to do verification in, but we
    still need to translate everything to something Coq understands.}
\end{frame}

\section{Translating data types}

\begin{frame}\frametitle{Translating data types}
  \note{Give list example. Note the assumption that we do not do any
    kind inference.}
  \begin{code}
    data List a  = Nil
                 | Cons a (List a)
  \end{code}

\begin{verbatim}
Inductive List ( a : Set ) : Set :=
  | Nil : List a
  | Cons : a -> List a -> List a.
\end{verbatim}
  
\end{frame}

\section{Dealing with parametric polymorphism}

\begin{frame}\frametitle{Dealing with parametric polymorphism}
  \note{Give SKI example.}

  \begin{code}
    s :: (a -> b -> c) -> (a -> b) -> a -> c
    s p q r = p r (q r)
    
    k :: a -> b -> a
    k a _ = a
  \end{code}

\begin{verbatim}
Definition s { a b c : Set } (x0 : a -> b -> c) (x1 : a -> b) (x2 : a) : c :=
  match x0, x1, x2 with
    | p, q, r => p r (q r)
  end.

Definition k { a b : Set } (x0 : a) (x1 : b) : a :=
  match x0, x1 with
    | a, _ => a
  end.
\end{verbatim}

\end{frame}

\begin{frame}

  \begin{itemize}
  \item We know that |i = s k k|.
  \end{itemize}

\begin{verbatim}
Definition i { a : Set } : a -> a :=
  s k k.
\end{verbatim}

\begin{verbatim}
Error: Cannot infer the implicit parameter b of k.
\end{verbatim}
\end{frame}

\section{Recursive definitions}

\begin{frame}\frametitle{Recursive definitions}
  \note{foldr?}
\end{frame}

\section{General recursion / partiality}

\begin{frame}\frametitle{General recursion / partiality}
  \note{Recurse stuff generally here, partially.}

  \begin{code}
    head :: [a] -> a
    head (x:xs) = x
  \end{code}

\begin{verbatim}
Definition head { a : Set } (x0 : List a) : a :=
  match x0 with
    | cons x xs => x
  end.
\end{verbatim}

\begin{verbatim}
Error: Non exhaustive pattern-matching: no clause found for pattern nil
\end{verbatim}

\end{frame}

\begin{frame}\frametitle{Non-structural recursion}
  \begin{itemize}
  \item In Coq, every recursive definition has to be structurally recursive
  \item We can only have recursive calls on structurally smaller arguments
  \item To prevent non-termination
  \end{itemize}

  \begin{code}
    quicksort :: [Nat] -> [Nat]
    quicksort []        =  []
    quicksort (x : xs)  =  append
                           (quicksort (filter (gt x) xs))
                           (quicksort (filter (le x) xs))
  \end{code}

\begin{verbatim}
Fixpoint quicksort (x0 : List Nat) : List Nat :=
  match x0 with
    | nil => nil
    | cons x xs => append (quicksort (filter (gt x) xs)) (quicksort (filter (le x) xs))
  end.
\end{verbatim}

\begin{verbatim}
Error:
Recursive definition of quicksort is ill-formed.
...
\end{verbatim}
\end{frame}

\begin{frame}\frametitle{Using the Bove-Capretta method}

  \begin{itemize}
  \item |headReverse x xs = head (reverse (x :: xs))| never crashes
  \item We can use the \verb+refine+ tactic here.
  \item The user has to provide proofs here.
  \end{itemize}

\begin{verbatim}
  Definition headReverse {a : Set} (x: a) (xs : List a) : a.
refine (head (reverse (x :: xs)) _).
<proof omitted>
Defined.
\end{verbatim}
\end{frame}

\section{Conclusion}

\begin{frame}\frametitle{Conclusion}
  \note{Conclude stuff here, obviously.}
\end{frame}

\end{document}
