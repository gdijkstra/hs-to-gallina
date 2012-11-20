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

\section{Introduction}
\label{sec:intro}

% Motivate problem some more: Haskell's type system is nice, but not
% enough for actual verification.

Suppose we want to verify software written in Haskell using a proof
assistant like Coq. Before we can begin with the verification process,
we need to model our software in the proof assistant's specification
language. Manual translation of Haskell code into Coq's Gallina code
is a tedious job and more importantly, it is prone to subtle mistakes.

The goal of this experimentation project is to find an answer to the
following question:

\begin{quote}
  ``Can we automate the process of translating Haskell code into a Coq
  script?''
\end{quote}

% Introduce method

% Talk about how Gallina and Haskell are pretty much alike in a lot of
% respects, but differ very much in others. Think about type
% inference, parametric polymorphism, type classes, GADTs. Total
% versus partial.

% Translate stuff with UUAG system
% Order stuff according to the dependencies.
% Talk about intricacies with type synonyms, explicit type signatures
% and infix operator names.

% Talk about handling of Prelude stuff.

% Bove-Capretta system
% Explain problem, explain array of solutions, explain why we chose
% this solution specifically. (Extraction!)
% Explanation of solution.
% Details of implementation: what do we restrict ourselves to? Type
% synonyms stuff again.
% Details on Prop versus Set wrt extraction.
% Details of missing pattern implementation.
% Details on the inversion proofs and why they should work.
% Examples.
% Refine tactic example for how to use stuff. (Find a nice example
% that I encountered in verification challenge?)

% Coinduction stuff as a nice extra.

% Related work
% Verifying Haskell in CTT paper
% Function interface and related articles?

% Future work

% Modules, better syntax support, refine tactic support, type
% synonyms, type classes, GADTs, better integration with GHC for
% finding imports and dependencies and et cetera.

% Conclusion

% Coq needs to update its extraction stuff. Produces broken Haskell.

% It sort of works nicely? Step in the right direction?

\end{document}
