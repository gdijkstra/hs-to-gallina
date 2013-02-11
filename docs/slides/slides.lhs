\documentclass[usenames,svgnames,dvipsnames,table]{beamer}
%include polycode.fmt

\usepackage[T1]{fontenc}

\usetheme{Copenhagen}
\usecolortheme{dolphin}
\defbeamertemplate*{title page}{customized}[1][]
{
  \begin{center}
  \usebeamerfont{title}\inserttitle\par
  \usebeamerfont{subtitle}\usebeamercolor[fg]{subtitle}\insertsubtitle\par
  \usebeamerfont{author}\usebeamercolor[fg]{textnormal}\insertauthor\par
  \bigskip
  \usebeamerfont{institute}\insertinstitute\par
  \usebeamerfont{date}\insertdate\par
  \bigskip
  \usebeamercolor[fg]{titlegraphic}\inserttitlegraphic
\end{center}
}

\title{Translating Haskell programs to Coq programs}
\author{Gabe Dijkstra}
\institute[Dept. of CS @@ UU.nl]{Utrecht University Department of Computing Science}
\date{\today}

\begin{document}


\begin{frame}
\maketitle
\end{frame}

\setcounter{tocdepth}{1}
\begin{frame}
  \tableofcontents
\end{frame}

\section{Introduction}

\begin{frame}
  \frametitle{Introduction}
  \begin{itemize}
    \item a
    \item b
    \item cdefghij
  \end{itemize}
\end{frame}

\end{document}
