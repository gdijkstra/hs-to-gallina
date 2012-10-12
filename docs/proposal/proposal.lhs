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

% Main goal: write verified Haskell code?
% Means: via Coq's extraction mechanism.

% Do we suppose we have some Haskell code? Or do we suppose we want to
% write Haskell code first to prototype stuff?

% Situation
% In order to write verified software:
% We need model/write program in Coq

% Either way: writing software in Coq is a pain: specifically
% termination.

% Manual translation Haskell -> Coq is tedious and prone to errors.

% Propose: automatic translation of Haskell to Coq. Via the AST with
% all the sugar.

% In order to deal with general recursion, we also want to
% automatically create Bove-Capretta predicates from our function
% definition.

% Alternative: translate GHC Core -> Coq and use a special monad to
% deal with partiality.
% The extracted code will not as directly match the original code.

% Experiment with these methods: compare examples.




\end{document}
