% This is samplepaper.tex, a sample chapter demonstrating the
% LLNCS macro package for Springer Computer Science proceedings;
% Version 2.20 of 2017/10/04
%

%\documentclass[runningheads]{llncs}
\documentclass{sokendai_thesis}

%

\usepackage[sort]{natbib}
\usepackage{natbib}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{hyperref}
\usepackage{stmaryrd}
%%%%% SOKENDAI Thesis
\let\openbox\undefined \usepackage{amsthm} % newtxmath in the preamble already defined openbox
%%%%%%%%%%%%%%
\usepackage{mathtools}
\DeclarePairedDelimiter\set\{\}
\DeclarePairedDelimiter\sguard[]
\DeclarePairedDelimiter\sguardP[{]'}
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
%\newcommand{\paperOrDissertation}{paper}
\newcommand{\paperOrDissertation}{dissertation}

\newcommand{\hide}[2][blue]{}

\def\sectionautorefname{Section}
\def\chapterautorefname{Chapter}
\def\subsectionautorefname{Section}

\newcommand{\judgeThree}[3]{#1 {\color{blue}\;||\;} #2 {\color{blue}\;\vdash\;} #3}
\newcommand{\judgeOneDef}[1]{\judgeThree{\Gamma}{\Psi}{#1}}
\newcommand{\judgeTwoDef}[2]{\judgeThree{\Gamma}{#1}{#2}}
\newcommand{\preEq}[3]{#1 \langle\; #2 \eqA #3 \;\rangle}
\newcommand{\eqC}{=}
\newcommand{\eqA}{=}
%\newcommand{\eqC}{=_{\texttt{CBPV}}}
%\newcommand{\eqA}{=_{\texttt{Alg}}}
\newcommand{\typing}[3]{#1 \vdash #2 : #3}
%\newcommand{\rcl}[1]{#1^{\rightarrow}}
\newcommand{\rcl}[1]{{\mathbf{rc}\;#1}}
\newcommand{\hint}[1]{{\color{olive}\text{[- #1 -]}}}

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
% lhs2tex definitions
%include polycode.fmt

%format udl(x) = "\underline{" x "}"
%format (udl(x)) = "\underline{" x "}"
%format op1 = "\mathit{op}_1"
%format op2 = "\mathit{op}_2"
%format t1 = "t_1"
%format t2 = "t_2"
%format v1 = "v_1"
%format v2 = "v_2"
%format k1 = "k_1"
%format k2 = "k_2"
%format l1 = "l_1"
%format l2 = "l_2"
%format x1 = "x_1"
%format x2 = "x_2"
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
%format phi1 = "\phi_1"
%format phi2 = "\phi_2"
%format phi3 = "\phi_3"
%format eps = "\epsilon"
%format phieps = "\phi_\epsilon"
%format union = "\cup"
%format intersect = "\cap"
%format eset = "\emptyset"
%format sg(x) = "\sguard{" x "}"
%format sgP(x) = "\sguardP{" x "}"
%format sem(x) = "\sembrk{" x "}"
%format _r(x) = "\rcl{" x "}"
%format rcl(x) = "rcl{" x "}"
%format _F = "\mathbf{F}"
%format _U = "\mathbf{U}"
%format foldrlsw = "\mathit{foldrl}_{\mathit{sw}}"
%format _eqa = "\eqA"
%format _dots = "\ldots"


%%%%%%%%%%%%
%SOKENDAI Thesis



\title{A Mutable Region System for Equational Reasoning about Pointer Algorithms}
\author{Zhixuan Yang}
\date{June 2019}
\crest{SOKENDAI.pdf} % comment out if you don't have a crest.
%\keywords{Latex Template, Sokendai, PhD Thesis} % for PDF meta-info




%%%%%%%%%%%




\begin{document}

%%%%%%%%%%%%%%%%%% LNCS Front matter%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%      %
%%%%%%      \title{A Mutable Region System for Equational Reasoning about Pointer Algorithms}
%%%%%%      %
%%%%%%      %\titlerunning{Abbreviated paper title}
%%%%%%      % If the paper title is too long for the running head, you can set
%%%%%%      % an abbreviated paper title here
%%%%%%      %
%%%%%%      \author{\today}
%%%%%%      %\author{First Author\inst{1}\orcidID{0000-1111-2222-3333} \and
%%%%%%      %Second Author\inst{2,3}\orcidID{1111-2222-3333-4444} \and
%%%%%%      %Third Author\inst{3}\orcidID{2222--3333-4444-5555}}
%%%%%%      %
%%%%%%      
%%%%%%      %\authorrunning{F. Author et al.}
%%%%%%      
%%%%%%      % First names are abbreviated in the running head.
%%%%%%      % If there are more than two authors, 'et al.' is used.
%%%%%%      %
%%%%%%      %\institute{Princeton University, Princeton NJ 08544, USA \and
%%%%%%      %Springer Heidelberg, Tiergartenstr. 17, 69121 Heidelberg, Germany
%%%%%%      %\email{lncs@springer.com}\\
%%%%%%      %\url{http://www.springer.com/gp/computer-science/lncs} \and
%%%%%%      %ABC Institute, Rupert-Karls-University Heidelberg, Heidelberg, Germany\\
%%%%%%      %\email{\{abc,lncs\}@uni-heidelberg.de}}
%%%%%%      %
%%%%%%      \maketitle              % typeset the header of the contribution
%%%%%%      %
%%%%%%      \begin{abstract}
%%%%%%        %Algebraic effects provide a uniform foundation for a wide range of computational effects, including local state, where programs can not only read and write memory cells but also create new ones at runtime.
%%%%%%        \Zhixuan[red]{This abstract is not very accurate. You can ignore it.}
%%%%%%        The equational theories of algebraic effects are natural tools for reasoning about programs using the effects, and some of the theories are proved to be complete, including the one of local state---the effect of mutable memory cells with dynamic allocation.
%%%%%%        Although being complete, reasoning about large programs with only a small number of equational axioms can sometimes be cumbersome and unscalable, as exposed in a case study of using the theory of local state to equationally reason about the Schorr-Waite traversal algorithm.
%%%%%%        Motivated by the recurring patterns in the case study, this papers proposes a conservative extension to the theory of local state called \emph{separation guards}, which is used to assert the disjointness of memory cells and allows local equational reasoning as in separation logic.
%%%%%%      
%%%%%%      \keywords{Equational Reasoning \and Effect systems \and Program transformation \and Pointer programs \and Algebraic effects}
%%%%%%      \end{abstract}
%
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%5 SOKENDAI Thesis Front matter

\frontmatter
\maketitle

\chapter*{Abstract}
The algebraic treatment of computational effects makes impure imperative programs amenable to equational reasoning, and it can be combined with region systems, or more generally type-and-effect systems, to derive non-trivial program equivalences by tracking effect operations that may be used by a program.
In this \paperOrDissertation, we propose a novel mutable region system, in which region partitioning is not statically fixed but follows the points-to structure of memory cells.
Our mutable region system overcomes the limitations of existing static region systems in tracking pointer-manipulating algorithms.
We demonstrate the usefulness of our system in an example of equational reasoning about the Schorr-Waite traversal algorithm restricted to linked lists.


\chapter*{Acknowledgement}
The first person I'd want to thank is Josh Ko who guided and trained me in the programming language world and convinced me of the beauty and power of rigorous reasoning.
I'd also thank Zirun Zhu for being my best friend in Japan---you are probably the funniest and most heartwarming man I ever knew.
Without any doubts, I've spent a lot of wonderful time and had many inspiring discussions with other fellow students and interns of the lab---Yongzhe Zhang, Chunmiao Li, Liye Guo, Vandang Tran, Jo\~ao Pereira.

I also want to thank my supervisors Zhenjiang Hu and Ichiro Hasuo for investing time and funding on my project and giving precious comments on my research.
Besides, I want to thank Taro Sekiyama and Jeremy Gibbons for discussing my project with me and giving me much encouragement.

During my days in Japan, all these people mentioned above, my parents in China, and my friends scattered over cities and countries helped me to fight with depression and find a meaning for my life.
Thank you all, sincerely.

I'm grateful for all the happiness and sorrow I had in Japan.


\vspace{2cm}

\hfill Zhixuan Yang

\hfill Arai, Ichikawa

\hfill On a rainy day, 2019

  \tableofcontents
  %\listoffigures
\mainmatter

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\chapter{Introduction}

Plotkin and Power's algebraic effects~\cite{Plotkin2002,Plotkin2004} and their handlers~\cite{Plotkin2013,Pretnar2010} provide a uniform foundation for a wide range of computational effects by defining an effect as an algebraic theory---a set of operations and equational axioms on them.
The approach has proved to be successful because of its composability of effects and clear separation between syntax and semantics.
Furthermore, the equations defining an algebraic effect are also natural tools for equational reasoning about programs using the effect, and can be extended to a rich equational logic~\cite{Pretnar2010,Plotkin2008}.
The equations of some algebraic effects are also proved to be (Hilbert-Post) complete, including the effects of global and local state~\cite{Staton2010}.


However, if one is limited to use only equational axioms on basic operations and must always expand the definition of a program to the level of basic operations, this style of reasoning will not be scalable.
A widely-studied solution is to use an \emph{effect system} to track possible operations used by a program and use this information to derive equations (i.e.\ transformations) of programs.
For example, if two programs $f$ and $g$ only invoke operations in sets $\epsilon_1$ and $\epsilon_2$ respectively and every operation in $\epsilon_1$ commutes with every operation in $\epsilon_2$, then $f$ and $g$ commute:
\[x \leftarrow f; y \leftarrow g; k \quad = \quad y \leftarrow g; x \leftarrow f; k\]
The pioneering work by Lucassen and Gifford~\cite{Lucassen1988} introduced an effect system to track memory usage in a program by statically partitioning the memory into \emph{regions} and used that information to assist scheduling parallel programs.
%The idea of using regions to statically track memory usage is
Benton et al.~\cite{Benton2006,Benton2007,Benton2009} and Birkedal et al.~\cite{Birkedal2016} gave relational semantics of such region systems of increasing complexity and verified some program equations based on them.
Kammar and Plotkin~\cite{Kammar2012} presented a more general account for effect systems based on algebraic effects and studied many effect-dependent program equations.
In particular, they also used the Gifford-style region-based approach to manage memory usage.

There is always a balance between expressiveness and complexity.
Despite its simplicity and wide applicability, tracking memory usage by \emph{static} regions is not always effective for equational reasoning about some pointer-manipulating programs, especially those manipulating recursive data structures.
It is often the case that we want to prove operations on one node of a data structure is irrelevant to operations on the rest of the structure; thus a static region system requires that we annotate the node in a region different from that of the rest of the data structure.
If this happens to every node (e.g.\ in a recursive function), each node of the data structure needs to have its own region, and thus the abstraction provided by regions collapses: regions should abstract disjoint memory cells, not memory cells themselves.
In \autoref{sec:prob}, we show a concrete example of equational reasoning about a tree traversal program and why a static region system does not work.


%A notable example is the Schorr-Waite traversal algorithm~\cite{Schorr1967}, which traverses a pointer-based binary tree using only constant space by reusing the memory cells of the tree itself to control the recursion.
%During the traversal, the memory cells of the nodes of the tree may be modified to store references to different regions at different stages of execution.
%However, when those cells are read, existing effect systems fail to track to which region the stored reference precisely is, disabling program transformations that we would like to use.

The core of the problem is the assumption that every memory cell statically belongs to one region, but when the logical structure of memory is mutable (e.g.\ when a linked list is split into two lists), we also want regions to be mutable to reflect the structure of the memory (e.g.\ the region of the list is also split into two regions).
To mitigate this problem, we propose a \emph{mutable region system}.
In this system, a region is either (i) a single memory cell or (ii) all the cells reachable from a node of a recursive data structure along the points-to relation of cells.
Although this definition is apparently restrictive, we believe it sufficient to demonstrate our ideas in this \paperOrDissertation and generalisations to more forms of regions are easy, e.g.\ regions that are the disjoint union of two subregions.
For example, the judgement
\begin{equation}\label{equ:tvs}
l : \mathit{ListPtr} \; a \vdash t\; l : \mathbf{1} \bang \set{\mathit{get}_{\rcl{l}}}
\end{equation}
asserts the program $t\;l$ only reads the linked list starting from $l$, where the type $\mathbf{data}\;\mathit{ListPtr}\;a = \mathit{Nil} \mid \mathit{Ptr}\;(\mathit{Ref}\; (a,\,\mathit{ListPtr} \; a))$  \footnote{Here |Nil| and |Ptr| are data constructors. |Nil| has type |ListPtr a| and |Ptr| has type |Ref (a, ListPtr a) -> ListPtr a|.} is either $\mathit{Nil}$ marking the end of the list or a reference to a cell storing a payload of type $a$ and a $\mathit{ListPtr}$ to the next node of the list.
The cells linked from $l$ form a region $\rcl{l}$ but it is only dynamically determined, and therefore may consist of different cells if the successor field (of type $\mathit{ListPtr}\;a$) stored in $l$ is modified.

We also introduce a complementary construct called \emph{separation guards}, which are effectful programs checking some pointers or their reachable closures are disjoint, otherwise stopping the execution of the program.
For example,
\[l : \mathit{ListPtr}\;a,\ l_2 : \mathit{Ref}\; (a \times \mathit{ListPtr} \; a) \vdash \sguard{\rcl{l} * l_2} : \mathbf{1}\]
can be understood as a program checking the cell $l_2$ is not any node of linked list $l$.
With separation guards and our effect system, we can formulate some program equations beyond the expressiveness of previous region systems.
For example, given judgement~(\ref{equ:tvs}), then
\[ \sguard{\rcl{l} * l_2};\mathit{put} \; l_2 \; v; t\; l \quad = \quad \sguard{\rcl{l} * l_2}; t\; l; \mathit{put} \; l_2 \; v  \]
says that if cell $l_2$ is not a node of linked list $l$, then modification to $l_2$ can be swapped with $t\;l$, which only accesses list $l$.
In \autoref{sec:case}, we demonstrate using these transformations, we can straightforwardly prove the correctness of a constant-space linked list folding algorithm, which is a special case of the Schorr-Waite traversal algorithm.

The remainder of this \paperOrDissertation is structured as follows: in \autoref{sec:prob} we show the limitation of static region systems by guiding the reader through an attempt to equationally reason about an interesting constant-space list folding algorithm; in \autoref{sec:reg} we present our solution---a mutable region system, its semantics and inference rules, which are our main technical contribution; in \autoref{sec:eq} we give a series of program equivalences based on our region system and use them to complete our proof attempt in \autoref{sec:prob}; in \autoref{sec:dis} we discuss related work and future directions.

\chapter{Limitation of Static Region Systems}\label{sec:prob}
This chapter we show the limitation of static region systems with a practical example of equational reasoning: proving the straightforward recursive implementation of |foldr| for linked lists is semantically equivalent to an optimised implementation using only constant space.
The straightforward implementation is not tail-recursive and thus it uses space linear to the length of the list, whereas the optimised version cleverly eliminate the space cost by reusing the space of the linked list itself to store the information needed to control the recursion and restore the linked list after the process.
This optimisation is essentially the Schorr-Waite algorithm~\cite{Schorr1967} adapted to linked lists, whose correctness is far from obvious and has been used as a test for many approaches of reasoning about pointer-manipulating programs~\cite{Moller1997,Butler,Bird2001,Reynolds2002}.


In the following, we start with an attempt to an algebraic proof of the correctness of this optimisation---transforming the optimised implementation to the straightforward one with equational axioms of the programming language and its effect operations.
From this attempt, we can see the limitation of static region systems: we want the region partitioning to match the logical structure of data in memory, but when the structure is mutable, static region systems do not allow region partitioning to be mutable to reflect the change of the underlying structure.

\section{Motivating Example: Constant-space |foldr| for Linked Lists}
The straightforward implementation of folding (from the tail side) a linked list is simply
\begin{code}
foldrl : (A -> B -> B) -> B -> ListPtr A -> _F B
foldrl f e v =  case v of 
                  Nil    -> return e
                  Ptr r  -> {  (a, n) <- get r; b <- foldrl f e n;
                               return (f a b) }
\end{code}
where |_F B| is the type of computations of |B| values and the letter $l$ in |foldrl| means linked lists.
The program is recursively defined but not tail-recursive, therefore a compiler is likely to use a stack to implement the recursion.
At runtime, the stack has one frame for each recursive call storing local arguments and variables so that they can be restored later when the recursion returns.
If we want to minimise the space cost of the stack, we may notice that most local variables are not necessary to be saved in the stack: arguments |f| and |e| are not changed throughout the recursion, and local variables |a|, |n| and |r| can be obtained from |v|.
Hence |v| is the only variable that a stack frame needs to remember to control the recursion.
Somewhat surprisingly, we can even reduce the space cost further: since |v| is used to restore the state when the recursive call for |n| is finished and the list node |n| happens to have a field storing a |ListPtr| (that is used to store the successor of |n|), we can store |v| in that field instead of an auxiliary stack.
But where does the original value of that field of |n| go?
They can be stored in the corresponding field of its next node too.
The following program implements this idea with an extra function argument to juggle with these pointers of successive nodes.
\begin{code}
  foldrlsw f e v = fwd Nil v

  fwd f e p v =  case v of
                   Nil   -> bwd f e p v
                   Ptr r -> {  (a, n) <- get r; put (r, (a, p));
                               fwd f e v n }

  bwd f b v n =  case v of
                   Nil   -> return b
                   Ptr r -> {  (a, p) <- get r; put (r, (a, n));
                               bwd f (f a b) p v }
\end{code}
|foldrlsw| is in fact a special case of the Schorr-Waite traversal algorithm which traverses a graph whose vertices have at most 2 outgoing edges using only 1 bit for each stack frame to control the recursion.
The Schorr-Waite algorithm can be easily generalised to traverse a graph whose out-degree is bounded by $k$ using $\log k$ bits for each stack frame, and the above program is the case when $k = 1$ and the list is assumed to be not cyclic.

\section{Verifying |foldrlsw|: First Attempt} \label{subsec:ve}
Let us try to prove the optimisation above is correct, in the sense that |foldrlsw| can be transformed to |foldrl| by a series of applications of equational axioms on programs that we postulate, including those characterising properties of the language constructs like |case| and function application, and those characterising the effectful operations |get| and |put|.

To prove by induction, it is easy to see that we need to prove a strengthened equality:
\begin{equation} \label{equ:hyp}
  |{ b <- foldrl f e v; bwd f b p v }| = |fwd f e p v|
\end{equation}
which specialises to |foldrlsw = foldrl| when |p = Nil|.
When |v = Nil|, the equality can be easily verified.
When |v = Ptr r|, we have
\begin{equation*}
   |fwd f e p v = { (a, n) <- get r; put (r, (a, p)); fwd f e v n }|
\end{equation*}
Assuming we have some inductive principle allowing us to apply Equation~\ref{equ:hyp} to |fwd f e v n| since |n| is the tail of list |v| (We will discuss inductive principles later in \autoref{sec:sepinf}), we proceed:
\begin{center}
\begin{code}
fwd f e p v  =  {  (a, n) <- get r; put (r, (a, p));
                   b <- foldrl f e n; bwd f b v n }
             = {-"\hint{Expanding $\mathit{bwd}$}"-}
                {  (a, n) <- get r; put (r, (a, p));
                   b <- foldrl f e n;
                   (a, p) <- get r; put (r, (a, n));
                   bwd f (f a b) p v  }
\end{code}
\labelcode{code:com}
\end{center}
Now we can see why the optimisation works: |fwd| first modifies node |v| (i.e.\ |Ptr r|) to point to |p|, and after returning from the recursive call to |n|, it recovers |p| from node |v| and restores |v| to point to |n|.
Hence we can complete the proof if we show the net effect of those operations leaves node |v| unchanged.

To show this, if we can prove the two computations in Equation~\ref{code:com} commute with |foldr f e n|: 
\begin{align}
  &|{| {|b <- foldrl f e n;|}\ \boxed{|(a, p) <- get r; put (r, (a, n));|} | K}| \nonumber \\
  =\  &|{| \boxed{|(a, p) <- get r; put (r, (a, n));|} \  {|b <- foldrl f e n;|}| K}| \label{equ:com}
\end{align}
Then
\begin{code}
fwd f e p v  =  {  (a, n) <- get r; put (r, (a, p)); 
                   (a, p) <- get r; put (r, (a, n));
                   b <- foldrl f e n; 
                   bwd f (f a b) p v  }
             = {-"\hint{Properties of $\mathit{put}$ and $\mathit{get}$; See below}"-}
                {  (a, n) <- get r;  
                   b <- foldrl f e n; 
                   bwd f (f a b) p v  }
             = {-" \hint{Contracting the definition of $\mathit{foldrl}$} "-}
                {  b' <- foldrl f e v; bwd f b' p v  }
\end{code}
which is exactly what we wanted to show (Equation~\ref{equ:hyp}).
The properties used in the second step are 
\begin{align}
  |{put (r, v); x <- get r; K} = {put (r, v); {-"K[v/x]"-}}| \nonumber \\
  |{put (r, v); put (r, u); K} = {put (r, u); K}| \label{laws:gp} \\
  |{x <- get r; put (r, x); K} = {x <- get r; K}| \nonumber
\end{align}
Therefore, what remains is to prove the commutativity in Equation~\ref{equ:com}, which is arguably the most important step of the proof.
Intuitively, |get r| and |put (r, (a, n))| access cell |r|, i.e.\ the head of the list |v|, while |foldrl f e n| accesses the tail of list |v|.
Hence if we want to derive Equation~\ref{equ:com} with a region system, we can annotate cell |r| with some region $\epsilon_1$ and all the cells linked from |n| with region $\epsilon_2$ so that Equation~\ref{equ:com} holds because |get r| and |put (r, (a, n))| access a region different from the one |foldrl f e n| accesses.

Unfortunately, this strategy does not quite work for two reasons:
First, since the argument above for |r| also applies to |n| and all their successors, what we finally need is one region $\epsilon_i$ for every node $r_i$ of a linked list.
This is unfavourable because the abstraction of regions collapses---we are forced to say that |foldrl f e n| only accesses list |n|'s first node, second node, etc, instead of only one region containing all the nodes of |n|.
The second problem happens in the type system: Now that the reference type is indexed by regions, the type of the $i$-th cell of a linked list may be upgraded to $|Ref|\ \epsilon_{i}\ (a \times |ListPtr|_{i+1}\ a)$.
But this type signature prevents the second field of this cell pointing to anything but its successor, making programs changing the list structure like |foldrlsw| untypable.
This problem cannot be fixed by simply change the type of the second field to be the type of references to arbitrary region, because we will lose track of the region information necessary for our equational reasoning when reading from that field. \Zhixuan{Clarify more} \Zhixuan{unnecessary for region polymorphism in typing recursive definitions}

The failure of static region systems in this example is due to the fact that a static region system presumes a fixed region partitioning for a program.
While as we have seen in the example above, in different steps of our reasoning, we may want to partition regions in different ways:
it is not only because we need region partitioning to match the logic structure of memory cells which is mutable---as in the example above, a node of a list is modified to points to something else and thus should no longer be in the region of the list.
Even when all data are immutable, we may still want a more flexible notion of regions---in one part of a program, we probably reason at the level of lists and thus we want all the nodes of a list to be in the same region; while in another part of the same program, we may want to reason at the level of nodes, then we want different nodes of a list in different regions.

\chapter{Mutable Region System}\label{sec:reg}
Our observations in the last section suggest us to develop a more flexible region system.
Our idea is to let the points-to structure of memory cells \emph{determine} regions: a region is either a single memory cell or all the cells reachable from one cell along the points-to structure of cells.
We found it is simpler to implement this idea in a logic system rather than a type system: we introduce effect predicates $\effect{(\cdot)}{\epsilon} $ on programs of computation types where $\epsilon$ is a list of effect operations in the language and two `virtual' operations $|get|_r$ and $|put|_r$ where $r$ is a region in the above sense.
The semantics of $\effect{t}{\epsilon}$ is that program $t$ only invokes the operations in $\epsilon$.
Inference rules for effect predicates are introduced.

\section{Preliminaries: the Language and Logic}
%\Zhixuan[red]{To write: this section fixes a programming language of algebraic effects and briefly describes an equational logic for it following \cite{Plotkin2008,Pretnar2010}.But we need to distinguish two equalities: $\eqC$ and $=_{\mathit{AE}}$.}

As the basis of discussion, we fix a small programming language with algebraic effects based on Levy's call-by-push-value calculus~\cite{Levy2012call}.
For a more complete treatment of such a language, we refer the reader to Plotkin and Pretnar's work~\cite{Plotkin2008}.
The syntax of this language are listed in Figure~(\ref{lang-syn}).
The language has two categories of types: value types, ranged over by |A|, and computation types, ranged over by $\underline{A}$.
Value types excluding thunk types ($\mathbf{U}\underline{A}$) are called storable types, ranged over by |D|.
In this language, only storable types can be stored in memory cells.
Furthermore, we omit general recursively-defined types for simplicity and restrict our treatment to only one particular recursive type: 
type |ListPtr A| is isomorphic to
\[|Unit + Ref (A ** ListPtr A)|\]

\begin{figure}
  \centering
  \begin{align*}
    &\text{Base types: }  & \sigma ::=\ & |Bool| \mid |Unit| \mid |Void| \mid \ldots \\
    &\text{Value types: } & A,\ B: :=\ & \sigma \mid |ListPtr D| \mid |Ref D| \mid A_1 \times A_2 \mid A_1 + A_2 \mid \mathbf{U} \underline{A}\\
    &\text{Storable types: } &D ::=\ & \sigma \mid |ListPtr D| \mid |Ref D| \mid D_1 \times D_2 \mid D_1 + D_2 \\
    &\text{Computation types: } &\underline{A},\ \underline{B}::=\ & \mathbf{F} A \mid |A1 -> udl(A2)| \\\\
    &\text{Base values: } & c ::=\ & |True| \mid |False| \mid () \mid \ldots \\
    &\text{Value terms: } &v ::=\ & x \mid c \mid |Nil| \mid |Ptr v| \mid (v_1,\,v_2) \mid |inj1|^{A_1 + A_2}\ v \mid |inj2|^{A_1 + A_2}\ v \mid |thunk t|\\
    &\text{Computation terms: } &t ::=\ & |return v| \mid |{x <- t1; t2}| \mid |match v as {(x1, x2) -> t}| \\
    && \mid\ & |match v as {Nil -> t1, Ptr x -> t2}| \\
    && \mid\ & |match v as {inj1 x1 -> t1, inj2 x2 -> t2}| \\
    && \mid\ & |\x : A . t| \mid |t v| \mid |force v| \mid |op v| \mid \mu x : \underline{A}.\ t \\
    &\text{Operations: } & |op| ::=\ & |fail| \mid \Omega \mid |get| \mid |put| \mid |new| \mid \ldots 
  \end{align*}
  \caption{Syntax of the language.}\label{lang-syn}
\end{figure}



We assume that the language includes the effect of failure (|fail|), non-divergence ($\Omega$) and \emph{local state}~\cite{Staton2010}.
Failure has one nullary operation |fail| and no equations.
Local state has the following three operations:
\begin{align*}
  |get|_D &: |Ref D -> _F D| \\
  |put|_D &: |Ref D ** D -> _F Unit| \\
  |new|_D &: |D -> _F (Ref D)|
\end{align*}
and they satisfy (a) the three equations in (\ref{laws:gp}) and
\[ |{x <- get r; y <- get r; K}| = |{x <- get r; {-"K[x/y]"-}}| \]
(b) commutativity of |get| and |put| on different cells, for example,
\[ |{put (l1, u); put (l2, v); K}| = |{put (l2, v); put (l1, u); K}| \quad (|l1| \neq |l2|) \]
(c) commutativity laws for |new|, that is, 
\begin{gather*}
  |{l <- new v; put (r, u); K} = {put (r, u); l <- new v; K}| \\
  |{l <- new v; x <- get r; K} = { x <- get r; l <- new v; K}| \\
  |{l1 <- new v; l2 <- new u; K} = {l2 <- new u; l1 <- new v; K}|
\end{gather*}
and (d) the following \emph{separation law}: for any |D|,
\begin{center}
\vspace{-1em}
\begin{code}
     {  l1 <- newD v1          wideeq   {  l1 <- newD v1; t1 }
        match l1 == l2 as
          {  False -> t1
             True -> t2 }}
\end{code}
\labelcodetag{Ax-Sep}{law:disj}
\vspace{-1cm}
\end{center}
which is a special case of the axiom schema $\text{B}3_n$ in~\cite{Staton2010} but is sufficient for our purposes.
\Zhixuan{In the standard treatment, these equations come with a context of free variables like $l_2$ in the last one. Do you find it strange if I omit them?}

\Zhixuan{ Give a brief description of the semantics... }

We also need an equational logic for reasoning about programs of this language.
We refer the reader to the papers~\cite{Pretnar2010,Plotkin2008} for a complete treatment of its semantics and inference rules.
Here we only record what is needed in this \paperOrDissertation.
The formulas of this logic are:
\begin{align*}
  \phi ::=\  & t_1 \eqC t_2  \mid \forall x : A.\ \phi \mid \exists x : \underline{A}.\ \phi \\
       \mid\ & \exists x : A.\ \phi \mid \exists x : \underline{A}.\ \phi  \mid \phi_1 \wedge \phi_2 \mid \phi_1 \vee \phi_2 \\
       \mid\ & \neg\phi \mid \phi_1 \rightarrow \phi_2 \mid \top \mid \bot 
\end{align*}
The judgement of this logic has form $\judgeOneDef{\phi}$ where $\Gamma$ is a context of the types of free variables and $\Phi$ is a list of formulas that are the premises of $\phi$.
The inference rules of this logic include:
\begin{enumerate}
  \item Standard rules for connectives in classical first order logic and structural rules for judgements (e.g.\ weakening and contraction on premises),
  \item standard equivalences for language constructs including sequencing, thunking, function application, case analysis, etc, as in call-by-push-value~\cite{Levy2012call}. 
    For example,
    \begin{mathpar}
      \inferrule{ }{\judgeThree{v : A,\ t : A \rightarrow \underline{A}}{}{|{x <- return v; t}| \eqC |t v|}}
        \and
        \inferrule{ \typing{\Gamma}{|(\x. t)|}{A\rightarrow\underline{A}} \\ \typing{\Gamma}{v}{A}}{ \judgeThree{\Gamma}{}{|(\x. t) v| \eqC t[v/x]}}
        \and
        \inferrule{ }{\judgeThree{t_1 : \underline{A},\ t_2 : \underline{A}}{}{|case True of {True -> t1; False -> t2}| \eqC t_1}}
    \end{mathpar}
  \item rules inherited from the effect theories, for example,
    \[\inferrule{ }{\judgeThree{l_{1,2} : |Ref D|,\ v_{1,2} : D,\ t : \underline{A}}{}|{put (l1, v1); put (l2, v2); t}| \eqA |{put (l2, v2); t}|}\]
  \item algebraicity of effect operations, the inductive principle over computations and the universal property of computation types.
\end{enumerate}
In this \paperOrDissertation, we will only use the first three kinds of rules.

%A difference from the logic defined in~\cite{Plotkin2008,Pretnar2010} is that we distinguish equivalences derived only from CBPV rules (written as $\eqC$) and those derived from both CBPV rules and effect theories (written as $\eqA$).
%This is preferable for our purpose because we do not want to regard |{v <- get l; put l v}| and |return ()| as the same because they invoke different operations.

\section{Effect System as Logic Predicates}
Unlike existing type-and-effect systems, our mutable region system is defined as logic predicates on computation terms in the logic.
Let |op| range over possible effect operations in the language.
We extend the term of the logic:
\begin{align*}
  \phi &::= \ldots \mid \effect{t}{\epsilon} \\
  \epsilon &::= \emptyset \mid \epsilon,|op| \mid \epsilon,|get|_{\rcl{v}} \mid \epsilon,|put|_{\rcl{v}} \mid \epsilon,|get|_{v} \mid \epsilon,|put|_{v}
\end{align*}
The new term is well-formed when
\begin{mathpar}
\inferrule{\typing{\Gamma}{t}{\mathbf{F}{A}}}{\typing{\Gamma}{\effect{t}{\cdot}}{\mathbf{form}}}
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}{\typing{\Gamma}{\effect{t}{\epsilon, |op|}}{\mathbf{form}}}\;(|op| \not\in \set{|get|,\;|put|})
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|Ref D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_v}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|ListPtr D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_{\rcl{v}}}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\end{mathpar}
Although $\epsilon$ is formally a list of comma-separated operations, we will regard it as a set and thus use set operations like inclusion and minus on it.

\begin{example}
  Let $\Gamma$ be $\set{l : |Ref D|,\ r : |Ref (D ** ListPtr D)|}$, 
  \[\typing{\Gamma}{\effect{|{(a, n) <- get r; put (l, a)}|}{\set{|put|_{l},\ |get|_{\rcl{|(Ptr r)|}}}}}{\mathbf{form}}\]
  is derivable.
\end{example}

Although our effect predicate is defined only on first-order computations, we can work with higher order functions by using quantification in the logic.
For example, if $\typing{\Gamma}{t}{|ListPtr D| \rightarrow \mathbf{F}A}$
\[\judgeThree{\Gamma}{}{\forall (l : |ListPtr D|).\ \effect{|t l|}{\set{|get|_{\rcl{l}}}}}\]
is well-formed and it expresses that function |t| only reads |l| when it is applied to list |l|.

The intended meaning of effect predicate $\effect{t}{\epsilon}$ is: provided that the regions mentioned in $\epsilon$ are disjoint, the computation $t$ only applies a finite number of operations in $\epsilon$.
Before giving a formal definition of this semantics, we present the inference rules first in the rest of this section, which may provide more intuition, and then in \autoref{subsec:sem} we give the formal semantics of effect predicates.


%\section{Effect System as Logic Predicates}
%%\Zhixuan{This section defines the well-formedness and semantics of predicates $\effect{t}{\epsilon}$: $t$ is a (possibly) infinite operation tree consisting only operations in $\epsilon$.}
%
%Unlike existing type-and-effect systems, our mutable region system is defined as logic predicates on computation terms in the logic.
%Let |op| range over possible effect operations in the language.
%We extend the term of the logic:
%\begin{align*}
%  \phi &::= \ldots \mid \effect{t}{\epsilon} \\
%  \epsilon &::= \emptyset \mid \epsilon,|op| \mid \epsilon,|get|_{\rcl{v}} \mid \epsilon,|put|_{\rcl{v}} \mid \epsilon,|get|_{v} \mid \epsilon,|put|_{v}
%\end{align*}
%The new term is well-formed when
%\begin{mathpar}
%\inferrule{\typing{\Gamma}{t}{\mathbf{F}{A}}}{\typing{\Gamma}{\effect{t}{\cdot}}{\mathbf{form}}}
%\and
%  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}{\typing{\Gamma}{\effect{t}{\epsilon, |op|}}{\mathbf{form}}}
%\and
%  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|Ref D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_v}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
%\and
%  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|ListPtr D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_{\rcl{v}}}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
%\end{mathpar}
%
%The intended meaning of the formula $\effect{t}{\epsilon}$ is that the computation $t$ only invokes operations in $\epsilon$.
%Specially, $|get|_v$ and $|put|_v$ in $\epsilon$ mean reading and writing the reference $v : |Ref D|$, and $|get|_{\rcl{v}}$ and $|put|_{\rcl{v}}$ mean reading and writing all the cells linked from $v$ of type $|ListPtr D|$.
%
%The semantics of $\sembrk{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}$ (abbreviated as $\sembrk{\effect{t}{\epsilon}}$ below) is a subset of $\sembrk{\Gamma}$ that is the \emph{least}-fixed-point solution of the following mutual-recursive equations.
%\Zhixuan[red]{No, this definition is wrong.
%A plausible definition: for all memory configuration (in which regions in $\epsilon$ are fintie), running $t$ (with get/put handled and other operations un-handled) only operates corresponding cells (and terminates).}
%\begin{align*}
%  &\sembrk{\effect{t}{\epsilon}} &= \set{ \gamma \in \sembrk{\Gamma} \mid \exists & \typing{\Gamma}{v}{A}.\ \sembrk{t}(\gamma) = \sembrk{|return v|}(\gamma)} \\
%%
%  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|op : B -> (udl(C))| \in \epsilon,\ \typing{\Gamma}{v}{B},\ \typing{(\Gamma, c : C)}{k}{\mathbf{F}A}.\\
%  &&&\sembrk{t}(\gamma) = \sembrk{|c <- op v; k|}(\gamma) \wedge \forall v_c \in \sembrk{C}.\ (\gamma, v_c) \in \sembrk{\effect{k}{\epsilon}}} \\
%%
%  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|get|_v \in \epsilon,\ \typing{(\Gamma, c : D)}{k}{\mathbf{F}A}.\\
%  &&&\sembrk{t}(\gamma) = \sembrk{|c <- get v; k|}(\gamma) \wedge \forall v_c \in \sembrk{D}.\ (\gamma, v_c) \in \sembrk{\effect{k}{\epsilon}}} \\
%%
%  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|put|_v \in \epsilon,\ \typing{\Gamma}{d}{D},\ \typing{\Gamma}{k}{\mathbf{F}A}.\\
%  &&&\sembrk{t}(\gamma) = \sembrk{|put (v,d); k|}(\gamma) \wedge \gamma \in \sembrk{\effect{k}{\epsilon}}} \\
%%
%  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|get|_{\rcl{v}} \in \epsilon, \text{if } \sembrk{v}(\gamma) = \sembrk{|Nil|} \text{ then } \gamma \in \sembrk{\effect{t}{\epsilon \setminus \set{|get|_{\rcl{v}}, |put|_{\rcl{v}}}}} \\
%  &&& \quad \text{otherwise } \exists\; l'.\  \sembrk{t}(\gamma) = \sembrk{|(d,n) <- get l'; k|}(\gamma) \\
%  &&& \quad\wedge \forall v_d, v_n.\ (\gamma, v_d, v_n) \in \sembrk{\effect{k}{\epsilon[\rcl{n}/\rcl{v}] \cup \epsilon[l'/\rcl{v}]}}} \\
%%
%  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|put|_{\rcl{v}} \in \epsilon, \text{if } \sembrk{v}(\gamma) = \sembrk{|Nil|} \text{ then } \gamma \in \sembrk{\effect{t}{\epsilon \setminus \set{|get|_{\rcl{v}}, |put|_{\rcl{v}}}}} \\
%  &&& \quad \text{otherwise } \exists\; l',\; d,\; k.\  \sembrk{t}(\gamma) = \sembrk{|put (l',d); k|}(\gamma) \\
%  &&& \quad\wedge \gamma \in \sembrk{\effect{k}{\epsilon[l'/\rcl{v}]}}}
%\end{align*}
\section{Inference Rules}\label{subsec:inf}
An advantage of tracking effects in the equational logic is that we only need to design inference rules for effects-related language constructs---|return|, sequencing and operation application.
Other language constructs like case-analysis are handled by the equational logic as we will see in the example below.
%
% The following is a largest-fixed-point version, but I switched to least-fixed-point.
%\begin{mathpar}
%  \inferrule{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}} \\ \epsilon \subseteq \epsilon'}{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon'}}}
%\and
%\inferrule{\judgeThree{\Gamma}{\Psi}{\exists x.\; t \eqC |return x|}}{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}}}
%\and
%\inferrule{\judgeThree{\Gamma, t : F\sigma}{\pi(t)}{\exists v, k.\; t \eqC |(a <- op v; k a)| \;\wedge\; \pi(|k a|)}}%
%          {\judgeThree{\Gamma, t : F\sigma}{\pi(t)}{\effect{t}{\epsilon}}} \quad ({|op| \in \epsilon} )
%\and
%\inferrule{\judgeThree{\Gamma, t : F\sigma, l : |ListPtr|}{\pi(t, l), l = \mathit{Nil}}{\effect{t}{\epsilon \setminus \set{\mathit{put}_{\rcl{l}}}}}
%  \\ \judgeThree{\Gamma, t : F\sigma, l' : \ldots}{\pi(t, l), l = |Ptr l'|}{\exists k.\; t \eqC |(put l' v; k)| \;\wedge\; k \texttt{ preserves}}}%
%          {\judgeThree{\Gamma, t : F\sigma, l : |ListPtr|}{\pi(t, l)}{\effect{t}{\epsilon}}}
%(\mathit{put}_{\rcl{l}} \in \epsilon)
%\end{mathpar}
%where $k \texttt{ preserves}$ abbreviates $((\forall x, m.\;\pi(x, m) \rightarrow \effect{x}{\epsilon[l / m]}) \rightarrow \effect{k}{\set{|put l'|} \cup \epsilon})$.
%\begin{mathpar}
%\inferrule{\judgeThree{\Gamma, t : F\sigma}{\pi(t), l = \mathit{Nil}}{\effect{t}{\epsilon}} 
%  \\ \judgeThree{\Gamma, t : F\sigma, l' : \ldots}{\pi(t), l = |Ptr l'|}{\exists k.\; t \eqC |(n <- get l' v; k n)| \;\wedge\; \forall n.\; |k n| \texttt{ preserves}}}%
%          {\judgeThree{\Gamma, t : F\sigma}{\pi(t)}{\effect{t}{\set{\mathit{get}_{\rcl{l}}} \cup \epsilon}}}
%\end{mathpar}
%where $|k n|\texttt{ preserves}$ abbreviates 
%\[(\forall x.\;\pi(x) \rightarrow \effect{x}{\set{\mathit{get}_{\rcl{l}}} \cup \epsilon}) \rightarrow \effect{k}{\set{|get l'|, \mathit{get}_{\rcl{n}}} \cup \epsilon[l'/\rcl{l}] \cup \epsilon[\rcl{n}/\rcl{l}]}\]
%
Our inference rules are:
\begin{itemize}
  \item two structural rules
  \begin{mathpar}
    \inferrule{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}} \\ \epsilon \subseteq \epsilon'}{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon'}}} \textsc{ R-Sub}
    \and
    \inferrule{\judgeOneDef{t \eqC t' \;\wedge\; \effect{t'}{\epsilon}}}{\judgeOneDef{\effect{t}{\epsilon}}} \textsc{ R-Eq}
  \end{mathpar}
  \item rules for |return| and sequencing
    \begin{mathpar}
      \inferrule{ }{\judgeThree{x : A}{ }{\effect{|return x|}{\emptyset}}} \textsc{ R-Pure}
      \and
      \inferrule{\judgeThree{\Gamma}{\Psi}{\effect{t_1}{\epsilon}} \\ \judgeThree{\Gamma, x : A}{\Psi}{\effect{t_2}{\epsilon}}}{\judgeThree{\Gamma}{\Psi}{\effect{|{x <- t1; t2}|}{\epsilon}}} \textsc{ R-Seq}
    \end{mathpar}
  \item rules for effect operations, for any operation of type $A \rightarrow \underline{B}$ in the language,
    \[\inferrule{ }{\judgeThree{v : |A|}{ }{ \effect{|op v|}{\set{op}}}} \textsc{ R-Op}\]
    and specially for $|get|_l$ and $|put|_l$ (Formally, they are not operation of the language so these rules are needed)
    \begin{mathpar}
      \inferrule{ }{\judgeThree{l : |Ref D|}{ }{\effect{|get l|}{\set{|get|_l}}}}
      \and
      \inferrule{ }{\judgeThree{l : |Ref D|,\;a : D}{ }{\effect{|put (l, a)|}{\set{|put|_l}}}}
    \end{mathpar}
  \item rules for $|get|_\rcl{l}$ and $|put|_\rcl{l}$
    \begin{mathpar}
      %\inferrule{  \judgeThree{\Gamma}{\Psi}{\effect{k}{ \epsilon \setminus \set{ |get|_x, |put|_x} }} }{ \judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon[|Nil| / x]}}} \; (|get|_x \in \epsilon \text{ or } |put|_x \in \epsilon)
      \inferrule{  \judgeThree{\Gamma}{\Psi}{\effect{t}{ \epsilon \setminus \set{ |get|_\rcl{|Nil|}, |put|_\rcl{|Nil|}} }} }{ \judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}}} \textsc{ R-Nil}
      \and
      \inferrule{  \judgeThree{\Gamma, a, n}{\Psi}{\effect{k}{ \epsilon[l/x] \cup \epsilon[\rcl{n}/x]}} }{ \judgeThree{\Gamma}{\Psi}{\effect{|{(a, n) <- get l; k}|}{\epsilon[\rcl{|(Ptr l)|} / x]}}} \; (|get|_x \in \epsilon) \textsc{ R-GetRc}
      \and
      \inferrule{ \judgeThree{\Gamma}{\Psi}{\effect{k}{\epsilon[l / x]}}}{\judgeThree{\Gamma}{\Psi}{\effect{k}{\epsilon[\rcl{|(Ptr l)|} / x]}}} \; (|put|_x \in \epsilon) \textsc{ R-PutRc}
    \end{mathpar}
    These rules deserve some explanation: The rule \textsc{R-Nil} means that $|get|_\rcl{|Nil|}$ and $|put|_\rcl{|Nil|}$ cannot be used by the program;
    the rule \textsc{R-GetRc} means that if a program has the permission to read the list from $l$, it can read the cell $l$ and its permission on $\rcl{(|Ptr l|)}$ is split into the same permission on cell $l$ and the rest of the list (i.e.\ $\rcl{n}$);
    \begin{example}
      By \textsc{R-GetRc}, if $\judgeThree{\Gamma, a, n}{}{\effect{k}{\set{|get|_l, |put|_l, |get|_\rcl{n}, |put|_\rcl{n}}}}$ is derivable, then 
      \[\judgeThree{\Gamma}{}{\effect{|{(a, n) <- get l; k}|}{\set{|get|_\rcl{|(Ptr l)|}, |put|_\rcl{|(Ptr l)|}}}}\]
      is derivable.
    \end{example}
    the rule \textsc{R-PutRc} says that if a program has the permission to write the list from $l$, then it has the permission to write the cell $l$ itself.
    This rule seems not very useful, but it reflects the fact that even if a program can write $\rcl{|Ptr l|}$, if it cannot read $l$, its accessible cells are restricted to $l$ only.

  \item Finally, we introduce a rule that may not be valid in more general settings but is safe in our context because it assumes all lists in memory are finite.
    The rule is, under side condition ${|get|_{\rcl{v}}} \in \epsilon$,
    \begin{mathpar}
      \inferrule{ \judgeThree{\Gamma,\ v}{\Psi, |v = Nil|}{\effect{t}{\epsilon}} \\ 
          \judgeThree{\Gamma,\ v,\ r}{\Psi,\ |v = Ptr r|}{|t = {(a, n) <- get r; k}|} \\
          \judgeThree{\Gamma, v, r, a, n}{\Psi,\ |v = Ptr r|,\ \effect{t[n/v]}{\epsilon[n/v]} }{\effect{k}{\epsilon[n/v] \cup \epsilon[r/\rcl{v}]}} }
        { \judgeThree{\Gamma,\ v : |ListPtr D|}{\Psi}{\effect{t}{\epsilon}} }
    \end{mathpar}
    Without this rule, a recursive program defined with $\mu$ can only satisfy $\effect{\cdot}{\epsilon}$ if $\Omega \in \epsilon$ (See Scott-induction in Chapter 9 of paper~\cite{Pretnar2010}).
    This rule allows a program that is a structural recursion along some linked list to satisfy predicate $\effect{\cdot}{\epsilon}$ without including $\Omega$ in $\epsilon$, as if it is not a recursive program.
    \begin{example}\label{ex:foldrl}
      Without this rule, we can only derive $\effect{|foldrl f e l|}{\set{get_\rcl{l}, \Omega}}$ using Scott-induction.
      With this, we can derive
      \begin{equation*}
        \inferrule{\inferrule{|foldrl f e Nil = return ()| \\ \effect{|return ()|}{\set{get_\rcl{l}}}}{\judgeThree{f, e, l}{l = |Nil|}{\effect{|foldrl f e Nil|}{\set{get_\rcl{l}}}}} \\ \textcircled{1} \\ \textcircled{2}
              }{\judgeThree{f, e, l}{ }{\effect{|foldrl f e l|}{\set{get_\rcl{l}}}}}
      \end{equation*}
      where $\textcircled{1}$ is
      \begin{gather*}
        \judgeThree{f, e, l, r}{l = |Ptr r|}{|foldrl f e l| = |{(a, n) <- get r; K}| } \\
        K =_{\mathtt{def}} |{b <- foldrl f e n; return f a b}|
      \end{gather*}
      and $\textcircled{2}$ is
      \begin{align*}
        \inferrule{ \cdots }{ \judgeThree{f, e, l, r, a, n}{l = |Ptr r|, \effect{|foldrl f e n|}{\set{|get|_\rcl{n}}}}{\effect{K}{\set{|get|_r, |get|_\rcl{n}}}}}
      \end{align*}
    \end{example}
\end{itemize}


An obvious difference of our effect predicates from existing type-and-effect system is that we only have inference rules for effect related language constructs, because other language constructs can be handled by \textsc{R-Eq} and corresponding elimination rules for the construct of the logic.
\begin{example}
  Letting |P| denote |case b of {True -> op1; False -> op2}|, we can derive
  \begin{align*}
    \inferrule{
    \inferrule{
      \textcircled{1}\\
      \textcircled{2}}
    {\judgeThree{b : |Bool|}{|b = False| \vee |b = True|}{\effect{|P|}{\set{|op1|, |op2|}}}}}
  { \judgeThree{b : Bool}{}{\effect{|P|}{\set{|op1|, |op2|}}}} (\textsc{ ExM-Bool})
  \end{align*}
  where \textsc{ExM-Bool} is the rule in the logic saying that $b : |Bool|$ is either |True| or |False|, $\textcircled{1}$ is
  \begin{equation*}
    \inferrule{\judgeThree{b : |Bool|}{b = |True|}{P = |op1|} \\ \inferrule{\judgeThree{}{}{\effect{|op1|}{\set{|op1|}}}}{\judgeThree{b : |Bool|}{b = |True|}{\effect{|op1|}{\set{|op1|, |op2|}}}} }{\judgeThree{b : |Bool|}{|b = False|}{\effect{|P|}{\set{|op1|, |op2|}}}}
  \end{equation*}
  and similarly $\textcircled{2}$ is
  \begin{equation*}
    \inferrule{\judgeThree{b : |Bool|}{b = |False|}{P = |op2|} \\ \inferrule{\judgeThree{}{}{\effect{|op2|}{\set{|op2|}}}}{\judgeThree{b : |Bool|}{b = |False|}{\effect{|op2|}{\set{|op1|, |op2|}}}} }{\judgeThree{b : |Bool|}{|b = False|}{\effect{|P|}{\set{|op1|, |op2|}}}}
  \end{equation*}
\end{example}

\Zhixuan{An example demonstrating the assumption of disjointness of regions by these rules.}

\section{Semantics}\label{subsec:sem}
Now let us formalise our intuitive semantics of effect predicate $\effect{t}{\epsilon}$: when regions mentioned in $\epsilon$ are disjoint and have finite cells, $t$ is a computation only using the operations contained in $\epsilon$ and $t$ is also finite.
Recall that the semantics of $t : \mathbf{F}A$ is an equivalence class of trees whose internal nodes are labeled with operation symbols and leaves are labeled with $|return v|$ for some $v \in \sembrk{A}$.
Trees in $\sembrk{t}$ are equal in the sense that anyone of them can be rewritten to another by the equations of the effect theory~\cite{Bauer2018}.
Therefore if we can define a denotational semantics $\sembrk{\epsilon}$, presumably to be the set of operations available to $t$, then $\sembrk{\effect{t}{\epsilon}}$ can be defined to mean that $\sembrk{t}$ has some element $T$ whose operations is a subset of $\sembrk{\epsilon}$ and $T$ is a well-founded tree.

However, how to interpret $\epsilon$ in the framework of algebraic effects is not straightforward.
For $|op|$, $|get|_l$ and $|put|_l$ in $\epsilon$, they can be easily interpreted by corresponding operations |op|, $|get|_{\sembrk{l}}$ and $|put|_{\sembrk{l}}$.
For $|get|_{\rcl{l}}$ (and $|put|_{\rcl{l}}$), we want to interpret it as a set of operations $\set{|get|_{\sembrk{l}}, |get|_{r_1}, |get|_{r_2}, \dots}$ where ${\sembrk{l}}$ points to $r_1$, $r_1$ points to $r_2$ in the memory, etc.
However, in the semantics of algebraic effects, there is no explicit representation for the memory so that we do not immediately know what $r_1$, $r_2$, \dots are.
(For comparison, the semantics of $t$ in other approaches is usually a function $|Mem -> (sem(A), Mem)|$ which has an explicit |Mem|.)

This problem may be tackled by the coalgebraic treatment of effects~\cite{PlotkinPower2008}, but here we adopt a simple workaround:
Although we do not have an explicit representation of memory to work with, we do have an operation |get| to probe the memory---if $|get r|$ returns $v$, we know memory cell $r$ currently stores value $v$.
Hence if $\sguard{\rcl{v}}$ is a program traversing linked list $v$ and returns the set of references to the nodes of the list, then we can interpret $\effect{t}{\set{|get|_{\rcl{v}}}}$ in this way: in program $|{r <- sg( _r( v ) ); t}|$, $t$ only reads the references in $r$.
And as we mentioned in \autoref{subsec:inf}, predicate $\effect{t}{\set{|get|_{r_1}, |put|_{r_2}}}$ implicitly assumes that $r_1$ and $r_2$ are disjoint, so to interpret this predicate, we want $\sguard{r_1 * r_2}$ not only returns the references in $r_1$ and $r_2$ but also checks they are disjoint.

Now let us define such programs more formally, which collect references to cells of memory regions and check disjointness.
Following the notation of separation logic~\cite{Reynolds2002}, we write $\phi = l_1 * l_2 * \cdots * l_n$ to denote a list of separate regions.
Here $l_i$ is either an expression of type |Ref D| or expression $\rcl{v}$ for some $v$ of type |ListPtr D|.
We add a new kind of term $\sguard{\phi}$ in the language, which we call \emph{separation guards}.
It has type $\mathbf{F}|MemSnap|$, where type |MemSnap| abbreviates
\[|FinMap (Ref (a ** ListPtr a)) (Set (Ref (a ** ListPtr a)))|\]
Thus |x : MemSnap| is finite map from references to sets of references.
The semantics of $\sguard{\phi}$ is the computation denoted by the following program
\begin{code}
  sem(sg(phi)) = sepChk phi eset eset

  sepChk [] x rcs = return rcs
  sepChk (v * phi) x rcs = if l `elem` x then fail else sepChk phi (x union l) rcs
  sepChk (_r(v) * phi) x rcs = {  x' <- tvsList v;
                                  if x' intersect x /= eset
                                     then fail
                                     else sepChk phi (x' union x) (rcs union { v {-"\mapsto"-} x'})}

  tvsList Nil = return eset
  tvsList (Ptr r) =  {(a, n) <- get p; rs <- tvsList n; return (r union rs)}
\end{code}
Thus $\sguard{\phi}$ traverses each region $r \in \phi$ one by one and checks their cells are disjoint, otherwise it calls |fail|.
When it terminates, it returns a finite map $rcs$ mapping every region $r$ in $\phi$ to the set of its cells, which can be thought as a snapshot of the current memory.

By probing the memory with separation guards, we can define the semantics of effect predicates now.
For any effect set $\epsilon$, let $R_\epsilon = \set{l \mid |put|_l \in \epsilon} \cup \set{\rcl{p} \mid |get|_\rcl{p} \in \epsilon}$.
Then take $\phi_\epsilon$ to be an arbitrary $*$-sequence of all the elements of |R|.
We define the semantics of judgement $\Gamma \vdash \effect{t}{\epsilon}$ to be the set of $\gamma \in \sembrk{\Gamma}$ such that $\sembrk{|{sg(phieps); t}|}_\gamma$ has an element $T$, which is a tree satisfying:
\begin{itemize}
  \item there is some $T_1 \in \sembrk{|sg(phieps)|}_\gamma$ and for any leaf node of $T_1$ label with |return x|, there is a computation tree $T_x$, such that $T$ is equal to the tree obtained by replacing every leaf node |return x| of $T_1$ with corresponding $T_x$;
  \item every $T_x$ is well-founded and every operation in $T_x$ is either: (i) $|op v|$ for some $|op| \in \epsilon$, (ii) $|get v|$ for some $|get|_l \in \epsilon$ and $|v| = \sembrk{l}_\gamma$, (iii) $|put (v,d)|$ for some $|put|_l \in \phi$ and $|v| = \sembrk{l}_\gamma$, (iv) |get v| for some $|get|_\rcl{r}$ and $|v| \in x(\sembrk{r}_\gamma)$, and (v) |put (v,d)| for some $|put|_\rcl{r}$ and $|v| \in x(\sembrk{r}_\gamma)$.
\end{itemize}

\begin{proposition}[Soundness] If $\judgeThree{\Gamma}{\psi_1, \ldots, \psi_n}{\phi}$ is derivable from the rules in \autoref{subsec:inf}, then
  \[\bigcap_{1 \leq i \leq n} \sembrk{\Gamma \vdash \psi_i} \subseteq \sembrk{\Gamma \vdash \phi}\]
\end{proposition}

\chapter{Program Equivalences}\label{sec:eq}
With effect predicates and separation guards, we can formulate the program transformation we wanted in \autoref{subsec:ve}.
For any effect predicate $\epsilon$, let $R_\epsilon = \set{r \mid |put|_r \in \epsilon \vee |get|_r \in \epsilon }$ be the regions used in $\epsilon$, and $\phi_\epsilon$ be an arbitrary sequence of the elements of $R_\epsilon$ joined by `$*$'.
For two effect predicates $\epsilon_1$ and $\epsilon_2$, if their operations (excluding $|get|_r$ and $|put|_r$) are pairwise commutative, i.e.\ any $op_1 \in \epsilon_1$ and $op_2 \in \epsilon_2$ that are not $|get|_r$ or $|put|_r$ satisfy
\[|{x <- op1 u; y <- op2 v; k}| = |{ y <- op2 v; x <- op1 u; k}|\]
then we have:
\begin{equation}
  \inferrule{\judgeOneDef{\effect{t_i}{\epsilon_i}} \quad (i = 1, 2)}{\judgeOneDef{\preEq{\sguard{\phi_{\epsilon_1} * \phi_{\epsilon_2}}}{|{x <- t1; y <- t2; k}|}{|{ y <- t2; x <- t1; k}|}}} \tag{Eq-Com} \label{eq:commu}
\end{equation}
where $\preEq{c}{a}{b}$ abbreviates $|{c;a}| \eqA |{c;b}|$.
\begin{proof}
  \Zhixuan{This should easily follow the semantics of $\effect{t_i}{\epsilon_i}$}.
\end{proof}

\section{Equational Rules for Separation Guards}

The consequence of \ref{eq:commu} has separation guards serving as the precondition for the equality, and therefore to finally use this equality in equational reasoning, we need to know when this precondition is satisfied.
This is accomplished by the following equational rules for separation guards.

  \begin{mathpar}
    \inferrule{ }{ \judgeThree{\Gamma}{}{\preEq{|sg(phi)|}{|new t|}{|{l <- new t; sg(phi * l); return l}|}}} \textsc{ Sep-RefIntro}
    \and
    \inferrule{\judgeThree{\Gamma}{\Psi, l_1 \neq l_2}{t_1 \eqA t_2}}{ \judgeOneDef{\preEq{\sguard{l_1 * l_2}}{t_1}{t_2}} }\textsc{ Sep-RefElim}
  \end{mathpar}
  \textsc{Sep-RefIntro} adds a cell into the separation guards, provided that the cell is newly generated.
  The validity of this rule comes from \ref{law:disj} saying that the result of |new| is always different previous values.
  Conversely, \textsc{Sep-RefElim} says that the separation guard $\sguard{l_1 * l_2}$ (for $l_1$ and $l_2$ of type $|Ref D|$) provides an assumption $l_1 \neq l_2$ for further equational reasoning.

\begin{mathpar}
  \inferrule{ }{\judgeThree{\Gamma}{}{\sguard{\phi} = \sguard{\phi * \rcl{|Nil|}}}}\textsc{ Sep-RcIntro1}
  \and
  \inferrule{ }{ \judgeThree{\Gamma}{}{\preEq{\sguard{\phi * \rcl{p} * l}}{|put (l, p)|}{|{put (l, p); sg(phi * _r((Ptr l)))}|}}}\textsc{ Sep-RcIntro2}
\end{mathpar}
\textsc{Sep-RcIntro1} and \textsc{Sep-RcIntro2} introduce a reachable closure in the separation guards, and then it can be eliminated by the following inductive principle for linked lists.
\begin{mathpar}
  \inferrule{ \judgeTwoDef{\Psi, p \eqA |Nil|}{\preEq{\sguard{\phi}}{t_1}{t_2}} \\ \texttt{InductiveCase}}{ \judgeOneDef{\preEq{\sguard{\rcl{p} * \phi}}{t_1}{t_2}}} \textsc{ ListInd}
\end{mathpar}
where $\texttt{InductiveCase}$ is 
\[
  \judgeThree{\Gamma, l}{p \eqA |Ptr l|,\ \texttt{hyp}}{\preEq{|{(a, n) <- get l; sg(l * _r(n) * phi)}|}{t_1}{t_2}}
\]
and $\texttt{hyp}$ is $\preEq{\sguard{\rcl{n} * \phi}}{t_1}{t_2}$.
And we have some simple structural rules for separation guards:
\begin{mathpar}
  \inferrule{ }{\judgeTwoDef{}{\sguard{ \phi_1 * \phi_2 } \eqA \sguard{ \phi_2 * \phi_1 }}}
\and
  \inferrule{ }{\judgeTwoDef{}{\sguard{ (\phi_1 * \phi_2) * \phi_3} \eqA \sguard{  \phi_1 * (\phi_2 * \phi_3) }}}
\and
  \inferrule{ }{\judgeThree{}{}{\sguard{\ } \eqA |return ()|}}
\and
  \inferrule{ }{\judgeTwoDef{}{\sguard{\phi_1 * \phi_2} \eqA \{\sguard{\phi_1 * \phi_2}; \sguard{\phi_1}\}}}
\and
  \inferrule{ }{\judgeTwoDef{}{\{\sguard{\phi_1}; \sguard{\phi_2}\} \eqA \{\sguard{\phi_2}; \sguard{\phi_1}\}}}
\end{mathpar}
and the commutativity of separation guards with |get| and |put|:
\begin{mathpar}
  \inferrule{ }{\judgeThree{\Gamma}{}{ |{a <- get l; sg(phi); k}| = |{sg(phi); a <- get l; k}|}}
  \and
  \inferrule{ }{\judgeThree{\Gamma}{}{ |{put (l, a); sg(l * phi); k}| = |{sg(l * phi); put (l, a); k}|}}

\end{mathpar}

At last, we have the following rule corresponding to the frame rule of separation logic:
\[
  \inferrule{\judgeOneDef{\effect{t}{\overline{\phi_1}}} \\ \judgeOneDef{\preEq{\sguard{\phi_1}}{t}{|{x <- t; sg(phi2); return x}|}}}{\judgeOneDef{\preEq{\sguard{\phi_1 * \psi}}{t}{|{x <- t; {-"\sguard{\phi_2 * \psi} "-}; return x}|}}}
\]

\begin{proposition}
  The inference rules above are sound with respect to the semantics.
\end{proposition}


\section{Verifying |foldrlsw|, Resumed}\label{sec:case}
Now we have enough weapons to complete our equational proof for |foldrlsw| in \autoref{subsec:ve}---effect predicates for proving commutativity of non-interfering computations and an inductive principle \textsc{ListInd} for finite linked list.

First, we change our proof goal \autoref{equ:hyp} to have a precondition that |v| is a finite list:
\[\forall p.\ \preEq{\sguard{\rcl{|v|}}}{|{ b <- foldrl f e v; bwd f b p v }|}{|fwd f e p v|}\]
Then we use \textsc{ListInd} to prove it by induction on |v|.
The base case is still straightforward.
The inductive case is to prove
\begin{equation}\label{equ:indgoal}
\preEq{|{(a, n) <- get r; sg(l * _r(n))}|}{|{ b <- foldrl f e v; bwd f b p v }|}{|fwd f e p v|}
\end{equation}
under the assumption that |v = Ptr r| and inductive hypothesis
\[\forall p.\ \preEq{\sguard{\rcl{|n|}}}{|{ b <- foldrl f e n; bwd f b p n }|}{|fwd f e p n|}\]
This is shown by equational reasoning:
\begin{code}
     {(a, n) <- get r; sg(r * _r(n)); fwd f e p v}
  = {-"\hint{Expanding $\mathit{fwd}$}"-}
     {(a, n) <- get r; sg(r * _r(n)); (a, n) <- get r; _dots }
  = {-"\hint{Commutativity of $\mathit{get}$ and $\sguard{l * \rcl{n}}$}"-}
     {(a, n) <- get r; (a, n) <- get r; sg(l * _r(n)); _dots }
  = {-"\hint{Two consecutive $\mathit{get}\;r$}"-}
     {(a, n) <- get r; sg(r * _r(n)); put (r, (a, p)); fwd f e v n }
  =  {(a, n) <- get r; put (r, (a, p)); sg(r * _r(n)); fwd f e v n }
  = {-"\hint{$\sguard{r * \rcl{n}} = \{\sguard{r * \rcl{n}};\;\sguard{\rcl{n}}\}$ }"-}
     {(a, n) <- get r; put (r, (a, p)); sg(r * _r(n)); sg(_r(n)); fwd f e v n }
\end{code}
Now we can apply our inductive hypothesis to |{sg(_r(n)); fwd f e v n}| by instantiating $p = |v|$, and we get: %
%format ABOVE = "\text{Above program}"
\begin{code}
     ABOVE
  =  {(a, n) <- get r; put (r, (a, p)); sg(r * _r(n)); sg(_r(n)); b <- foldrl f e n; bwd f b p n}
  = {-"\hint{Expanding $\mathit{bwd}$}"-}
     {  (a, n) <- get r; put (r, (a, p)); sg(r * _r(n)); b <- foldrl f e n;
        (a, p) <- get r; put (r, (a, n)); bwd f (f a b) p v}
\end{code}
This time we can use~\ref{eq:commu} to show that |foldrl f e n| and |{(a, p) <- get r; put (r, (a, n))}| are commutative.
It is straightforward to derive
\[ \judgeThree{r, n}{}{\effect{|{(a, p) <- get r; put (r, (a, n))}|}{\set{|get|_r, |put|_r}}}\]
and in \autoref{ex:foldrl} we have derived $\judgeThree{f, e, n}{}{\effect{|foldrl f e n|}{\set{|get|_\rcl{n}}}}$, so by~\ref{eq:commu} we can proceed:
\begin{code}
     ABOVE
  =  {  (a, n) <- get r; put (r, (a, p)); sg(r * _r(n)); (a, p) <- get r; put (r, (a, n));
        b <- foldrl f e n; bwd f (f a b) p v}
  = {-"\hint{Commutativity of separation guards with $\mathit{get}$ and $\mathit{put}$}"-}
     {  (a, n) <- get r; put (r, (a, p)); (a, p) <- get r; put (r, (a, n)); 
        sg(r * _r(n)); b <- foldrl f e n; bwd f (f a b) p v}
  = {-"\hint{Simplifying $\mathit{get}$ and $\mathit{put}$}"-}
     {(a, n) <- get r; sg(r * _r(n)); b <- foldrl f e n; bwd f (f a b) p v}
  = {-"\hint{Contracting $\mathit{foldrl}$ and $\mathit{f\;a\;b}$}"-}
     {(a, n) <- get r; sg(r * _r(n)); b' <- foldrl f e v; bwd f b' p v}
\end{code}
This completes our equational proof for |foldrlsw|.


\chapter{Discussions}\label{sec:dis}

\section{Related work}
The correctness of the Schorr-Waite algorithm has been proved by different approaches: relational algebra~\cite{Moller1997}, data refinement~\cite{Butler}, separation logic~\cite{Reynolds2002} and equational reasoning~\cite{Bird2001}.
Among them, Bird's approach is most related to ours.
The fundamental difference between our work and his is that he worked with a fixed (purely-functional) model of memory, whereas we followed the axiomatic approach for equational reasoning \cite{Gibbons2011} so our reasoning only depends on algebraic axioms of effect operations.
Our work extends the approach by \citet{Gibbons2011} in the sense that we use an effect system for proving some equivalences instead of solely relying on equational axioms.
As we were developing the equational proof for the Schorr-Waite algorithm, we tried a proof using only equational axioms.
But we found the proof complicated and many of its steps too low-level if we could only work with primitive operations.
Thus we turned to use effect systems to prove important steps---commutativity of two non-interfering computations---in a more intuitive way.

Our separation guards are borrowed from separation logic~\cite{Reynolds2002} with extreme restriction on the forms of assertions, but we expect an extended version of our system may use a wider family of assertions as in separation logic.
Our work is different from separation logic in the way that our goal is to show two programs are observationally equivalent while separation logic shows a program establishes a post-condition described by a logic language.
The fundamental difference on the proof goal makes these two approaches useful in different settings.
However, the work by \citet{Nishimura2008} resembles our approach: they derived inequalities of separation assertions and program constructs on the semantic foundation of predicate transformers of separation logic, whereas our semantic foundation is algebraic effects.
Another closely related approach is relational separation logic~\cite{Yang2007}, which aims to show two programs executed respectively on two states satisfying a pre-relation produce two states satisfying a post-relation.
It is an interesting question to compare and establish the connection between our algebraic-effects-based approach and separation-logic-based approaches in the future, possibly through the connection between monads and predicate transformers established by \citet{Hasuo2015}.


Our work followed \citet{Kammar2012} to use an effect system to validate program transformations.
Their results are general to algebraic effects while we almost focused on the effect of mutable state, but as discussed in the \paperOrDissertation, our mutable region system is more flexible when dealing with mutable data structures.
Unlike theirs and most existing region systems, our mutable region system is defined as predicates in an logic for the programming language instead of within the type system for the language.
The advantage of our choice is that our inference rules only need to deal with language constructs related to effects and we get the ability to handle higher order functions almost for free.

\section{Conclusion}
Our work started from an attempt to prove the correctness of the Schorr-Waite algorithm by equational reasoning, and as in many previous research works, we observed that the key is to prove two computations do not interfere and thus can be executed in any order.
From the aspect of algebraic effects, non-interference means that these two computations use commutative effect operations, so the problem is reduced to track operations used by a computation, which is usually done with type-and-effect systems.
However, existing static-region-based effect systems are inadequate for the Schorr-Waite algorithm because the mutable nature of the algorithms demands different region partitioning at different stages.

To address this problem, we proposed a mutable region system in which regions are determined by the points-to structure of memory cells, so that regions partitioning naturally follows when the points-to structure in memory is modified.
Our system is formalised as effect predicates and separation guards.
Semantics and sound inference rules for them are given and they allow us to formulate and prove statements like: this program only reads the cell linked from pointer $p$, and the linked lists from $p_1$ and $p_2$ are disjoint.
With these tools, we can give an equational proof for the Schorr-Waite algorithm restricted to linked lists, which we think is intuitive and elegant.


\section{Future work}
The system described in this \paperOrDissertation is very restrictive and needs future development in many aspects:
\begin{itemize}
  \item We neglected effect handlers in this \paperOrDissertation and it is important to incorporate them into the mutable region system in the future.

  \item It is also very beneficial to generalise our system from local-state to other dynamically creatable effects.

  \item Although we presented our system with only linked lists, it should be able to be generalised to arbitrary tree-like data structures easily.
    However, how to deal with graphs in memory seems much more difficult.
    To prove the correctness of the Schorr-Waite algorithm on graphs using the method in \autoref{sec:case}, we need to formulate a statement that |traverse g| only reads the nodes reachable from node |g| and not marked visited.
    Therefore the possible effect operations used by |traverse g| not only depends on the points-to structure of memory cells but also some other mutable state (keeping track of which nodes are visited), so an important question is how to upgrade effect predicates to be more expressive to describe the possible effects used by programs like this.
    If we aim at generality, it seems that eventually we need some expressive programming language to describe effect usage of programs precisely.
\end{itemize}

%
% ---- Bibliography ----
%
% BibTeX users should specify bibliography style 'splncs04'.
% References will then be sorted and formatted in the correct style.
%
%\bibliographystyle{splncs04}
%\bibliographystyle{plain}
\bibliographystyle{ACM-Reference-Format}
\bibliography{sep.bib}

\end{document}
