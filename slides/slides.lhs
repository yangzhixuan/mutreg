% Copyright 2004 by Till Tantau <tantau@users.sourceforge.net>.
%
% In principle, this file can be redistributed and/or modified under
% the terms of the GNU Public License, version 2.
%
% However, this file is supposed to be a template to be modified
% for your own needs. For this reason, if you use this file as a
% template and not specifically distribute it as part of a another
% package/program, I grant the extra permission to freely copy and
% modify this file as you see fit and even to delete this copyright
% notice. 

\documentclass[professionalfont]{beamer}

% Replace the \documentclass declaration above
% with the following two lines to typeset your 
% lecture notes as a handout:
%\documentclass{article}
%\usepackage{beamerarticle}

\addtobeamertemplate{navigation symbols}{}{%
    \usebeamerfont{footline}%
    \usebeamercolor[fg]{footline}%
    \hspace{1em}%
    \insertframenumber/\inserttotalframenumber
}

\setlength{\parskip}{\baselineskip} 
\setlength\itemsep{1em}

\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{hyperref}
\usepackage{stmaryrd}
\usepackage{mathtools}
\DeclarePairedDelimiter\set\{\}
\DeclarePairedDelimiter\sguard[]
\DeclarePairedDelimiter\sembrk\llbracket\rrbracket

\usepackage{mathpartir}

\newcommand{\bang}{\,\mathop{!}\,}
\newcommand{\effect}[2]{#1 \bang #2}
%
% If you use the hyperref package, please uncomment the following line
% to display URLs in blue roman font according to Springer's eBook style:
\renewcommand\UrlFont{\color{blue}\rmfamily}

\newcommand{\Zhixuan}[2][blue]{{\color{#1}\{Zhixuan: #2\}}}
%\newcommand{\Zhixuan}[2][blue]{}
\newcommand{\hide}[2][blue]{}

\newcommand{\judgeThree}[3]{#1 {\color{blue}\;||\;} #2 {\color{blue}\;\vdash\;} #3}
\newcommand{\judgeOneDef}[1]{\judgeThree{\Gamma}{\Psi}{#1}}
\newcommand{\judgeTwoDef}[2]{\judgeThree{\Gamma}{#1}{#2}}
\newcommand{\preEq}[3]{#1 \langle\; #2 \eqA #3 \;\rangle}
\newcommand{\eqC}{=_{\texttt{CBPV}}}
\newcommand{\eqA}{=_{\texttt{Alg}}}
\newcommand{\typing}[3]{#1 {\color{blue}\;\vdash\;} #2 : #3}

\newcommand{\labelcode}[1]{
  \vspace{-5em}
  \begin{equation}
      \label{#1}
     \vspace{2em}
  \end{equation}
}
\newcommand{\labelcodetag}[2]{
  \vspace{-5em}
  \begin{equation}
    \tag{\textsc{#1}} \label{#2}
     \vspace{2em}
  \end{equation}
}

\newcommand{\somemargin}{\vspace{1cm}}
\newcommand{\somesmallmargin}{\vspace{0.5em}}
\newcommand{\myeg}{{\color{green}E.g.}}
\newcommand{\Emph}[1]{{\color{red}\emph{#1}}}


%include polycode.fmt
%include lineno.fmt
%format udl(x) = "\underline{" x "}"
%format (udl(x)) = "\underline{" x "}"
%format (red(x)) = "{\color{red}" x "}"
%format t1 = "t_1"
%format t2 = "t_2"
%format v1 = "v_1"
%format v2 = "v_2"
%format a1 = "a_1"
%format a2 = "a_2"
%format k1 = "k_1"
%format k2 = "k_2"
%format l1 = "l_1"
%format l2 = "l_2"
%format x1 = "x_1"
%format x2 = "x_2"
%format r1 = "r_1"
%format r2 = "r_2"
%format A1 = "A_1"
%format A2 = "A_2"
%format D1 = "D_1"
%format D2 = "D_2"
%format . = ".\;"

%format ** = "\times"
%format thunk = "\mathbf{thunk}"
%format match = "\mathbf{match}"
%format as = "\mathbf{as}"
%format force = "\mathbf{force}"
%format return = "\mathbf{return}"
%format inj1 = "\mathbf{inj}_1"
%format inj2 = "\mathbf{inj}_2"
%format wideeq = "\quad\quad = \quad\quad"
%format newD = "\mathit{new}_D"
%format getD = "\mathit{get}_D"
%format putD = "\mathit{put}_D"

%format phi = "\phi"
%format union = "\cup"
%format eset = "\emptyset"
%format sg(x) = "\sguard{" x "}"
%format _r(x) = "r(" x ")"

\title{A Dynamic Region System for Transforming Effect-dependent Programs}
\subtitle{}

% A subtitle is optional and this may be deleted
%\subtitle{Optional Subtitle}

\author{Zhixuan~Yang}
% - Give the names in the same order as the appear in the paper.
% - Use the \inst{?} command only if the authors have different
%   affiliation.

\institute[SOKENDAI] % (optional, but mostly needed)
{SOKENDAI and NII}
% - Use the \inst command only if there are several affiliations.
% - Keep it simple, no one is interested in your street address.

\date{May 2019}
% - Either use conference name or its abbreviation.
% - Not really informative to the audience, more for people (including
%   yourself) who are reading the slides online

\subject{Theoretical Computer Science}
% This is only inserted into the PDF information catalog. Can be left
% out. 

% If you have a file called "university-logo-filename.xxx", where xxx
% is a graphic format that can be processed by latex or pdflatex,
% resp., then you can add a logo as follows:

% \pgfdeclareimage[height=0.5cm]{university-logo}{university-logo-filename}
% \logo{\pgfuseimage{university-logo}}

% Delete this, if you do not want the table of contents to pop up at
% the beginning of each subsection:

\AtBeginSection[]
{
  \begin{frame}<beamer>{Outline}
    \tableofcontents[currentsection]
  \end{frame}
}

% Let's get started
\begin{document}

\begin{frame}
  \titlepage
\end{frame}

%\begin{frame}{Outline}
%  \tableofcontents
%  % You might wish to add the option [pausesections]
%\end{frame}

%lhslatex commands
%format while = "\mathbf{while}"

% Section and subsections will appear in the presentation overview
% and table of contents.

\section{Background}
\begin{frame}{}
  \begin{block}{Assuming you are an optimising compiler, will you transform}
    \[|put p v; l <- get q; K| \quad\quad \text{(In C syntax } |*p = v; l = *q; K| \text{)}\]
    to
    \[|l <- get q; put p v; K| \quad\quad \text{(In C syntax } |l = *q; *p = v; K| \text{)}\]
  \end{block}
  (|put p v| writes |v| to the cell |p|;
  |get q| reads cell |q|)
  \pause
  \begin{center}
  \begin{alertenv}
    {Only when |put p| and |get q| access different cells ($p \neq q$) !}
  \end{alertenv}
  \end{center}
\end{frame}

\begin{frame}{Pointer Analyses}
  We need a way to statically track which memory cells a program may access.

  Two orthogonal problems:
  \begin{enumerate}
    \setlength\itemsep{1em}
    \item How to ``talk about'' memory cells statically---a static abstraction of memory. 

      \myeg\ ``|p| points to \underline{a cell allocated by the |new| at line 10}''.
    \item How to track which memory cells a pointer variable may point to
  \end{enumerate}
\end{frame}

\begin{frame}{Pointer Analyses in Compilers}
  Core of static program analysis, intensively studied
  \begin{itemize}
    \item Usually with simple model to question 1: partitioning the memory cells by the |new| call in the code allocating it
      \begin{center}
      \includegraphics[height=3cm]{pic1}
      \end{center}
    \item Automated solution to question 2: data-flow analyses, abstract interpretation ...
  \end{itemize}
\end{frame}


\begin{frame}{Pointer Analyses Beyond Compilers}
  Program transformations are not limited to compilers.

  \begin{itemize}
    \setlength\itemsep{1em}
    \item Equational proof: transforming a program to a simple and obviously correct program
    \item Done by human: allowing more refined memory models (that are not possible for automated analyses).
  \end{itemize}

\end{frame}

\begin{frame}{Pointer Analyses Beyond Compilers}
  Region system (Lucassen and Gifford 1988): the memory is partitioned into \emph{regions} (mentally, by the programmer)

  \begin{itemize}
    \item Reference (pointer) type |Ref r D| is indexed by a region
    \item |new: (r : Region) -> D -> Ref r D| takes a region argument
    \item Use a type system to track which regions a program access
  \end{itemize}

  Compared to the line-number-based memory model, we can distinguish memory cells by passing different region argument to the same |new| call.
\end{frame}

\begin{frame}{Naive model vs.\ region model}
  \begin{code}
    makeList [] = return Nil
    makeList (a:as) = {  ls <- makeList as;
                         p <- new (a, ls);
                         return (Ptr p) }

    l1 <- makeList a1
    l2 <- makeList a2
  \end{code}

  In the naive model, both $l_1$ and $l_2$ point to cells allocated by the |new| at line \#3.
\end{frame}

\begin{frame}{Naive model vs.\ region model}
  (Assuming $r_1 \neq r_2$)
  \numbersreset
  \begin{code}
    makeList (red(r1)) [] = return Nil
    makeList (red(r1)) (a:ax) = {  ls <- makeList r ax;
                                   p <- new r (a, ls)
                                   return (Ptr p)}

    l1 <- makeList (red(r1)) a1
    l2 <- makeList (red(r2)) a2
  \end{code}

  In the region model, $l_1$ and $l_2$ point to cells in region $r_1$ and $r_2$ respectively.
\end{frame}

\begin{frame}{Static region is not enough}
  \begin{itemize}
    \setlength\itemsep{1em}
    \item Existing region systems assume memory can be \Emph{statically} partitioned.
    \item For some pointer-manipulating programs, this assumption does not hold.
  \end{itemize}

  \only<1> {
    \begin{columns}
      \begin{column}{0.4 \linewidth}
        \numbersreset
        \begin{code}
          traverse (Ptr r)
          traverse (Ptr t)
        \end{code}
      \end{column}
      \begin{column}{0.6 \linewidth}
        \includegraphics[height=3cm]{pic2}
      \end{column}
    \end{columns}
    At some place in the code, we may want to put the list |r| in a region.
  }

\end{frame}


\begin{frame} {Static region is not enough}
  At some other point in the program, we may want to put \underline{the first cell} of list |r| and \underline{the rest of the list} in different regions to reason about the program.

  \begin{columns}
    \begin{column}{0.5 \linewidth}
      \numbersreset
      \begin{code}
        p Nil = return ()
        p (Ptr r) = {  (a, n) <- get r
                       put r (a, m)
                       traverse n
                       put r (a, n) }
      \end{code}
    \end{column}
    \begin{column}{0.5 \linewidth}
      \includegraphics[height=3cm]{pic3}
    \end{column}
  \end{columns}
  Thus, a \emph{static} region system is not sufficient.
\end{frame}

\begin{frame}{A dynamic region system}
  We wish a more \emph{dynamic} region system such that
  \begin{itemize}
    \item the region to which a cell belongs can determined dynamically (by the contents of memory cells)
    \item we can track the regions a program access
  \end{itemize}

  This is what this work wants to do.
\end{frame}

\begin{frame}{A dynamic region system}
  Currently, my dynamic region system is very simple. A region is
  \begin{itemize}
    \item a single memory cell or 
    \item the \emph{current} reachable closure from a memory cell.
  \end{itemize}
  For example, the judgement
  \begin{equation*}
  l : \mathit{ListPtr} \; a \vdash t\; l : \mathbf{1} \bang \set{\mathit{get}_{\mathit{r}(l)}}
  \end{equation*}
  asserts the program $t\;l$ only reads the linked list starting from $l$.
\end{frame}

\begin{frame}{Separation guard}
  A complementary construct: \emph{separation guard}

  \begin{itemize}
    \item it checks some pointers or their reachable closures are disjoint, otherwise terminates the program
    \item resembles the precondition of separation logic
  \end{itemize}

  For example,
  \[{\color{gray} l : \mathit{ListPtr}\;a, l_2 : \mathit{Ref}\; (a,\,\mathit{ListPtr} \; a)} \vdash \sguard{r(l) * l_2} : \mathbf{F} |Unit|\]
  checks the cell $l_2$ is not any node of linked list $l$.
\end{frame}


\begin{frame}{Program transformation}
  Put dynamic region system and separation guard together, we can express and prove some transformations.

  \begin{exampleblock}{Example}
    \[\inferrule{
        l : \mathit{ListPtr} \; a \vdash t\; l : \mathbf{1} \bang \set{\mathit{get}_{\mathit{r}(l)}} }
       {\sguard{\mathit{r}(l) * l_2};\mathit{put} \; l_2 \; v; t\; l \quad = \quad \sguard{\mathit{r}(l) * l_2}; t\; l; \mathit{put} \; l_2 \; v}  \]
  \end{exampleblock}
\end{frame}


\section{Preliminaries: effect theories, a language and a logic}

\begin{frame}{Language}
  For the purpose of discussion, we fix a small programming language based Levy's \emph{call-by-push-value} calculus with algebraic effects (but no handlers)

  \begin{align*}
    &\text{Base types: }  & \sigma ::=\ & |Bool| \mid |Unit| \mid |Void| \mid \ldots \\
    &\text{Value types: } & A ::=\ & \sigma \mid |ListPtr D| \mid |Ref D| \mid A_1 \times A_2 \\ &&& \mid A_1 + A_2 \mid \mathbf{U} \underline{A}\\
    &\text{Storable types: } &D ::=\ & \sigma \mid |ListPtr D| \mid |Ref D| \mid D_1 \times D_2 \\ &&& \mid D_1 + D_2 \\
    &\text{Computation types: } &\underline{A} ::=\ & \mathbf{F} A \mid |A1 -> udl(A2)| \\\\
  \end{align*}
\end{frame}

\begin{frame}{Syntax}
  \begin{align*}
    &\text{Value terms: } &v ::=\ & x \mid c \mid |Nil| \mid |Ptr v| \mid (v_1,\,v_2) \\ &&& \mid |inj1|^{A_1 + A_2}\ v \mid |inj2|^{A_1 + A_2}\ v \mid |thunk t|\\
    &\text{Computation terms: } &t ::=\ & |return v| \mid |{x : A <- t1; t2}| \\ &&& \mid |match v as {(x1, x2) -> t}| \\
    && \mid\ & |match v as {Nil -> t1, Ptr x -> t2}| \\
    && \mid\ & |match v as {inj1 x1 -> t1, inj2 x2 -> t2}| \\
    && \mid\ & |\x : A . t| \mid |t v| \mid |force v| \mid |op v| \mid \\ &&& \mu x : \mathbf{U} \underline{A}.\ t \\
    &\text{Operations: } & |op| ::=\ & |fail| \mid |get| \mid |put| \mid |new| \mid \ldots 
  \end{align*}
\end{frame}

\begin{frame}{Effect theories}
  For the operations in the language, we have equations on them:
  \begin{itemize}
    \item |l <- get p; put p l = return ()|
    \item |put p v1; put p v2 = put p v2|
    \item \dots
    \item And this \emph{separation axiom}
     \numbersreset 
     \begin{code}
     {  l1 <- newD v1          wideeq   {  l1 <- newD v1
        l2 <- newD v2                      l2 <- newD v2 
        match l1 == l2 as                  t1 }
          {  False -> t1
             True -> t2 }}
    \end{code}
  \end{itemize}
\end{frame}

\begin{frame}{Type system and semantics}
  \begin{block}{Type system}
    Please refer to Plotkin and Pretnar's \textit{A Logic for Algebraic Effects} paper.
  \end{block}
  \begin{block}{Semantics}
    $\sembrk{A}$ maps to some set.

    $\sembrk{\underline{A}}$ maps to the set of tree whose internal nodes of operations and leaves are $A$-values.

    $\sembrk{\typing{\Gamma}{t}{\tau}}$ maps to a function $\sembrk{\Gamma} \rightarrow \sembrk{\tau}$.
  \end{block}
\end{frame}

\begin{frame}{Logic}
  We have a first-order equational logic for reasoning about programs of this language.

  Judgements
    \[ \judgeOneDef{\phi} \]
    $\Gamma$ is a context of the types of free variables and $\Phi$ is a list of formulas that are the premises of $\phi$.

  Terms
    \begin{align*}
      \phi ::=\  & t_1 \eqC t_2 \mid t_1 \eqA t_2 \mid \forall x : A.\ \phi \mid \forall x : \underline{A}.\ \phi \\
           \mid\ & \exists x : A.\ \phi \mid \exists x : \underline{A}.\ \phi  \mid \phi_1 \wedge \phi_2 \mid \phi_1 \vee \phi_2 \\
           \mid\ & \neg\phi \mid \phi_1 \rightarrow \phi_2 \mid \top \mid \bot 
    \end{align*}
\end{frame}

\begin{frame}{Inference rules}
  The logic system's inference rules are:
  \begin{itemize}
      \only<1>{
        \item Standard rules for classical first order connectives and structural rules for judgements,
      }
      \only<2>{
    \item standard $\beta$- and $\eta$- equivalence for CBPV language constructs, for example,
      \begin{mathpar}
          \inferrule{ }{|{x <- return v; t}| \eqC t[v/x]}
          \and
          \inferrule{ }{|(\x. t) v| \eqC t[v/x]}
          \and
          \inferrule{ }{|case True of {True -> t1; False -> t2}| \eqC t_1}
      \end{mathpar}
    }
    \only<3>{
      \item rules inherited from the effect theories, for example,
        \[\inferrule{ }{|{put (l1, v1); put (l2, v2); t}| \eqA |{put (l2, v2); t}|}\]
    }
      \only<4>{
        \item algebraicity of effect operations, an inductive principle over computations and a universal property of computation types.
      }
  \end{itemize}
\end{frame}

\begin{frame}{Sum up of preliminaries}
  Plotkin's algebraic effects have these layers of concepts:
  \begin{enumerate}
    \item Basic types (e.g.\ |Nat|, |Bool|, \ldots)
    \item Effect theories (operations and equations)
    \item A programming language with effect operations, sequential composition, and (possibly) handlers
    \item An equational logic for reasoning about programs of this language.
  \end{enumerate}

  \only<2>{ The logic is rich and powerful---we will express our region system in this logic.}
\end{frame}

\section{Dynamic region system}
\begin{frame}{Region system as logic predicates}
Our dynamic region systems are defined as logic predicates on computation terms in the logic.

Let |op| range over possible effect operations in the language.
We extend the term of the logic:
\begin{align*}
  \phi &::= \ldots \mid \effect{t}{\epsilon} \\
  \epsilon &::= \emptyset \mid \epsilon,|op| \mid \epsilon,|get|_{r(v)} \mid \epsilon,|put|_{r(v)} \mid \epsilon,|get|_{v} \mid \epsilon,|put|_{v}
\end{align*}
\end{frame}

\begin{frame}{Well-formedness}
The new term is well-formed when
\begin{mathpar}
\inferrule{\typing{\Gamma}{t}{\mathbf{F}{A}}}{\typing{\Gamma}{\effect{t}{\cdot}}{\mathbf{form}}}
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}{\typing{\Gamma}{\effect{t}{\epsilon, |op|}}{\mathbf{form}}}
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|Ref D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_v}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|ListPtr D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_{r(v)}}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\end{mathpar}
\end{frame}

\begin{frame}{Semantics}
We intend the semantics of $\sembrk{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}$ to be
  \[\set{\gamma \in \sembrk{\Gamma} \mid \sembrk{t}(\gamma) \text{ is a computation only invokes operations in } \epsilon }\]

  I am hesitating about the definition---should we interpret |get|/|put| in |t|?
\end{frame}


\begin{frame}{Inference rules}

\begin{mathpar}
  \inferrule{ }{\judgeThree{\Gamma}{\Psi}{\effect{|return x|}{\emptyset}}} \textsc{ R-Pure}
  \and
  \inferrule{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}} \\ \epsilon \subseteq \epsilon'}{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon'}}} \textsc{ R-Sub}
  \and
  \inferrule{\judgeOneDef{t \eqC t' \;\wedge\; \effect{t'}{\epsilon}}}{\judgeOneDef{\effect{t}{\epsilon}}} \textsc{ R-Eq}
\end{mathpar}

And for any ${|op : A -> udl(B)| \in \epsilon}$ that is not $|get|/|put|_{r(v)}$,
\begin{mathpar}
  \inferrule{\judgeThree{\Gamma, a : B}{\Psi}{\effect{|k|}{\epsilon}}}{\judgeOneDef{\effect{|(a <- op v; k)|}{\epsilon}}} \;  \textsc{ R-Op}
\end{mathpar}
\end{frame}


\begin{frame}{Inference rules}{}
  {\color{blue} Intuitively, } \\ if $\epsilon$ contains $|get|_{r(v)}$ or $|put|_{r(v)}$, the program can read or write the cells linked from $|v : ListPtr D|$.
\begin{itemize}
  \item When $|v = Nil|$, the program get no cells to access from $r(v)$.
  \item When $|v = Ptr v'|$, the program can read or write the cell |v'|,
    \begin{itemize}
      \item and if it reads it by |(a, n) <- get v'|, its allowed operation on $r(v)$ is inherited by $r(n)$ and $v'$
    \end{itemize}
\end{itemize}
\end{frame}


\begin{frame}{Inference rules}
If ${|get|_{r(v)}} \in \epsilon$
\begin{mathpar}
  \inferrule{\judgeOneDef{\effect{|t Nil|}{\epsilon \setminus \set{|get|_{r(v)},\ |put|_{r(v)}}}} \\ 
             \judgeThree{\Gamma, v'}{\Psi}{|t (Ptr v')| \eqC |{(a, n) <- get v'; k}|} \\
             \judgeThree{\Gamma, v', a, n}{\Psi,\ \effect{|t n|}{\epsilon[r(n)/r(v)]}}{\effect{k}{\epsilon[r(n)/r(v)] \cup \epsilon[v'/r(v)]}}}
             {\judgeOneDef{\effect{|t v|}{\epsilon}}}
\end{mathpar}

If $|put|_{r(v)} \in \epsilon$
\begin{mathpar}
  \inferrule{ \judgeOneDef{\effect{|t Nil|}{\epsilon \setminus \set{|get|_{r(v)},\ |put|_{r(v)}}}} \\
             \judgeOneDef{|t (Ptr v')| \eqC |{put v' c; k}|} \\
             \judgeThree{\Gamma}{\Psi}{\effect{k}{\epsilon[v'/r(v)]}}}
            {\judgeOneDef{\effect{|t v|}{\epsilon}}} 
\end{mathpar}
\end{frame}

\begin{frame}
  \begin{theorem}[Soundness]
     If $\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}}$, then $\sembrk{\Psi} \subseteq \sembrk{\effect{t}{\epsilon}}$.
  \end{theorem}
  \begin{proof}
    To do
  \end{proof}
\end{frame}

\section{Separation guards}

\begin{frame}{Separation guards}
  \begin{itemize}
    \item Our dynamic region systems proves a program only operates on certain memory cells
      \[ \effect{t_1}{\{|get|_{r(l_1)}, |put|_{r(l_1)}\}} \quad \text{ and } \effect{t_2}{\{|get|_{r(l_2)}, |put|_{r(l_2)}\}}  \]
    \item This information is useful only when we can also shows the cells that two programs respectively operates on are disjoint

      \[  r(l_1) \cap r(l_2) = \emptyset \implies t_1; t_2 = t_2;t_1 \]

    \item Ultimately, disjointness comes from the separation axiom of |new|, but it is too primitive for practical use.
  \end{itemize}
  \only<2>{ We introduce \Emph{separation guards} for tracking disjointness more easily at a higher level. }
\end{frame}

\begin{frame}
Following separation logic, we write $\phi = l_1 * l_2 * \cdots * l_n$ to denote that cells described by $l_i$ are dijoint.

Each $l_i$ can be either a value |v| of type |Ref D|, or |_r(v)| for a value |v| of type |ListPtr D|.

A separation guard $\sguard{\phi}$ is a computation of type $\mathbf{F}|Unit|$.
\end{frame}

\begin{frame}{Definition}
$\sguard{\phi}$ is defined as
\numbersreset
\begin{code}
  sg(phi) = sepChk phi eset

  sepChk [] s = return ()
  sepChk (v * phi) x = if l `elem` x then fail else sepChk phi (x union l)
  sepChk (_r(v) * phi) x = {x' <- chkList v x; sepChk phi x'}
  
  chkList Nil x = return x
  chkList (Ptr p) x = if  p `elem` x 
                          then {fail; return ()}
                          else {(_, n) <- get p; chkList n (x union p)}
\end{code}
|sg(phi)| checks regions $l_i$ of $\phi$ are distinct.
\end{frame}

\begin{frame}{Inference rules}
Define $\preEq{c}{a}{b}$ to be $(c;a) \eqA (c;b)$.

We have the following inference rules for separation guards
\begin{mathpar}
  \inferrule{ }{\preEq{|sg(phi)|}{|new t|}{|(l <- new t; sg(phi * l); return l)|}}
  \and
  \inferrule{\judgeThree{\Gamma}{\Psi, l_1 \neq l_2}{t_1 \eqA t_2}}{ \judgeOneDef{\preEq{\sguard{l_1 * l_2}}{t_1}{t_2}} }
  \and
  \inferrule{ }{|return Nil| \eqA |(l <- return Nil; sg(_r(l)); return l)|}
  \and
  \inferrule{ }{\preEq{\sguard{r(l)}}{|new (Cell a l)|}{|(l' <- new (Cell a l); sg(_r(l')); return l')|}}
\end{mathpar}
\end{frame}

\begin{frame}{Inference rules}
  The rule for list induction
  \[\inferrule{ \texttt{base case} \\ \texttt{inductive case}}{ \judgeOneDef{\preEq{\sguard{r(l) * \phi}}{t_1}{t_2}}} \quad(\textsc{ListInd})\]

\begin{itemize}
  \item \texttt{base case} is $\judgeTwoDef{\Psi, l \eqA |Nil|}{\preEq{\sguard{\phi}}{t_1}{t_2}}$ 
  \item \texttt{inductive case} is
  \begin{align*}
    &\judgeTwoDef{l = |Ptr l'|, \texttt{hyp}}{ \\&\quad\quad\quad\quad \preEq{\left(|(Cell _, n) <- get l'; sg(l' * _r(n) * phi)|\right)}{t_1}{t_2}}
  \end{align*}
  and $\texttt{hyp} =_{\mathtt{def}} \preEq{\sguard{r(n) * \phi}}{t_1}{t_2}$
\end{itemize}
\end{frame}


\begin{frame}{Soundness}
\begin{theorem}
The inference rules for separation guards are sound.
\end{theorem}
\begin{proof}
  To do.
  It'll be a large verifying proof.
\end{proof}
\end{frame}


\begin{frame}{Program transformations}

Now we have enough ingridents to express the program transformations I wanted:

A frame rule:
\[
\inferrule{\judgeOneDef{\effect{t_1}{\overline{\phi_1}}} \\ \judgeOneDef{\preEq{\sguard{\phi_1}}{t_1}{t_2}}}{\judgeOneDef{\preEq{\sguard{\phi_1 * \phi_2}}{t_1}{(t_2;\sguard{\phi_2})}}}
\]

Commutativity lemma
\[
\inferrule{\judgeOneDef{\effect{t_i}{\overline{\phi_i}}} \; (i = 1, 2) }{\judgeOneDef{\preEq{\sguard{\phi_1 * \phi_2}}{(t_1; t_2)}{(t_2; t_1)}}}
\]

  \only<2>{Proof: induction on the derivation of region predicates and using the inference rules of separation guards.}
\end{frame}


\begin{frame}{Conclusion}
  \begin{itemize}
   \setlength\itemsep{1em}
    \item We proposed static methods to track
      \begin{itemize}
        \item which memory cells a program access, and
        \item if these cells are disjoint.
      \end{itemize}
    \item Technical parts are remained to be completed and polished.
  \end{itemize}
\end{frame}

\end{document}
