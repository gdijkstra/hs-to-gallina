\documentclass[a4paper,10pt]{article}

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{cite}

\title{Experimentation project proposal: \\
Verifying Haskell programs in Coq}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

Suppose we want to verify software written in Haskell, using a proof
assistant like Coq. Before we can start verifying, we first need to
write a model of our software in the proof assistant's specification
language. Manual translation of Haskell code into Coq's Gallina code
is tedious and more importantly, prone to subtle mistakes. 

We want to write a tool that automatically translate Haskell code to
Gallina code. However, since Coq only allows structural recursion, not
all Haskell definitions can translated directly into Gallina. In order
to deal with some of these cases, we can generate Bove-Capretta
predicates from the original function definition and rewrite the
function definition using this predicate.

Another limitation of a direct translation is that in Coq there is a
distinction between inductive and coinductive data types. If we want
to work with infinite lists in Coq, we have to make a separate
coinductive data type. We also want our tool to be able to assist in
this process.

\end{document}
