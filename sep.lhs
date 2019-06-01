% This is samplepaper.tex, a sample chapter demonstrating the
% LLNCS macro package for Springer Computer Science proceedings;
% Version 2.20 of 2017/10/04
%
\documentclass[runningheads]{llncs}
%
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
\newcommand{\typing}[3]{#1 \vdash #2 : #3}
%\newcommand{\rcl}[1]{#1^{\rightarrow}}
\newcommand{\rcl}[1]{\mathbf{rc}\;#1}
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
%format union = "\cup"
%format eset = "\emptyset"
%format sg(x) = "\sguard{" x "}"
%format _r(x) = "\rcl{" x "}"
%format _F(x) = "\mathbf{F}" x
%format _U(x) = "\mathbf{U}" x
%format foldrlsw = "\mathit{foldrl}_{\mathit{sw}}"
%format _eqa = "\eqA"
%format _dots = "\ldots"
\begin{document}
%
\title{Equational Reasoning about Pointer Programs with Separation}
%
%\titlerunning{Abbreviated paper title}
% If the paper title is too long for the running head, you can set
% an abbreviated paper title here
%
\author{\today}
%\author{First Author\inst{1}\orcidID{0000-1111-2222-3333} \and
%Second Author\inst{2,3}\orcidID{1111-2222-3333-4444} \and
%Third Author\inst{3}\orcidID{2222--3333-4444-5555}}
%

%\authorrunning{F. Author et al.}

% First names are abbreviated in the running head.
% If there are more than two authors, 'et al.' is used.
%
%\institute{Princeton University, Princeton NJ 08544, USA \and
%Springer Heidelberg, Tiergartenstr. 17, 69121 Heidelberg, Germany
%\email{lncs@springer.com}\\
%\url{http://www.springer.com/gp/computer-science/lncs} \and
%ABC Institute, Rupert-Karls-University Heidelberg, Heidelberg, Germany\\
%\email{\{abc,lncs\}@uni-heidelberg.de}}
%
\maketitle              % typeset the header of the contribution
%
\begin{abstract}
  %Algebraic effects provide a uniform foundation for a wide range of computational effects, including local state, where programs can not only read and write memory cells but also create new ones at runtime.
  \Zhixuan[red]{This abstract is not very accurate. You can ignore it.}
  The equational theories of algebraic effects are natural tools for reasoning about programs using the effects, and some of the theories are proved to be complete, including the one of local state---the effect of mutable memory cells with dynamic allocation.
  Although being complete, reasoning about large programs with only a small number of equational axioms can sometimes be cumbersome and unscalable, as exposed in a case study of using the theory of local state to equationally reason about the Schorr-Waite traversal algorithm.
  Motivated by the recurring patterns in the case study, this papers proposes a conservative extension to the theory of local state called \emph{separation guards}, which is used to assert the disjointness of memory cells and allows local equational reasoning as in separation logic.

\keywords{Equational Reasoning \and Effect systems \and Program transformation \and Pointer programs \and Algebraic effects}
\end{abstract}
%
%
%
\section{Introduction}
\hide{Bullets:
\begin{enumerate}
  \item Algebraic effects provide a uniform way to model computational effects and the defining equational theories of algebraic effects are natural tools to reason about programs using algebraic effects---Plotkin and Pretnar's logic.
  Furthermore, some equational theories are showed to be complete, including the one of local state.

  \item Although being complete, doing equational reasoning with only basic equational axioms may be unscalable.
  For example, it is unpractical if we must always expand the definitions of two programs $f$ and $g$ to the level of basic operations to prove their algebraic properties such as commutativity $f; g = g;f$.

  \item A widely used solution is to track possible operations in a program with an \emph{effect system}.
    Exploiting the algebraic properties of operations performed by a program, many program transformation can be validated~\cite{Kammar2012,Kammar2014thesis}.
    For example, $f$ and $g$ commute if every operation possibly performed by $f$ commutes with every operation in $g$.

  \item However, for the effect of local state, existing region-based effect systems fail to precisely track which regions may be accessed by a program when a cell storing a reference value may point to---store references of---different regions at different stages of execution.
    This problem emerges in the equational reasoning about the Schorr-Waite traversal algorithm which traverses a pointer-based binary tree with only constant space by reusing the memory cells of the tree to control the recursion.
    During the traversal, the children pointers of a node of the tree may be modified to store references in different regions at different stages of execution.
    However, when those cells are read, existing region systems lose track of which region the stored reference precisely is in, disabling program transformations that we would like to use.

  \item To address this problem, we propose an alternative way to track which memory cells may be accessed by a program: instead of checking that a program only accesses a statically determined region, we check a program only accesses all cells reachable from a given pointer, which intuitively form a region but is not statically determined and whose cells may be different if the points-to structure of memory cells are changed at runtime.

    We also introduce a complementary construct of \emph{separation guard}, which is an operation checking some pointers or their reachable closures are disjoint, otherwise the guard fails and stops the execution of the program.
    With separation guard and our effect system, we can formulate some transformations of pointer-manipulating programs beyond the expressiveness of previous region systems.
    Using these transformations, we can equationally prove the correctness of the Schorr-Waite traversal algorithm (on binary trees) quite straightforwardly.
\end{enumerate}
}

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
In Section~\ref{sec:prob}, we show a concrete example of equational reasoning about a tree traversal program and why a static region system does not work.


%A notable example is the Schorr-Waite traversal algorithm~\cite{Schorr1967}, which traverses a pointer-based binary tree using only constant space by reusing the memory cells of the tree itself to control the recursion.
%During the traversal, the memory cells of the nodes of the tree may be modified to store references to different regions at different stages of execution.
%However, when those cells are read, existing effect systems fail to track to which region the stored reference precisely is, disabling program transformations that we would like to use.

The core of the problem is the assumption that every memory cell statically belongs to one region, but when the logical structure of memory is mutable (e.g.\ when a linked list is split into two lists), we also want regions to be mutable to reflect the structure of the memory (e.g.\ the region of the list is also split into two regions).
To mitigate this problem, we propose a \emph{mutable region system}.
In this system, a region is either (i) a single memory cell or (ii) all the cells reachable from a node of a recursive data structure along the points-to relation of cells.
For example, the judgement
\begin{equation}\label{equ:tvs}
l : \mathit{ListPtr} \; a \vdash t\; l : \mathbf{1} \bang \set{\mathit{get}_{\rcl{l}}}
\end{equation}
asserts the program $t\;l$ only reads the linked list starting from $l$, where the type $\mathit{ListPtr}\;a = \mathit{Nil} \mid \mathit{Ptr}\;(\mathit{Ref}\; (a,\,\mathit{ListPtr} \; a))$ is either $\mathit{Nil}$ marking the end of the list or a reference to a cell storing a payload of type $a$ and a $\mathit{ListPtr}$ to the next node of the list.
The cells linked from $l$ form a region $\rcl{l}$ but it is only dynamically determined, and therefore may consist of different cells if the successor field (of type $\mathit{ListPtr}\;a$) stored in $l$ is modified.

We also introduce a complementary construct called \emph{separation guards}, which are effectful programs checking some pointers or their reachable closures are disjoint, otherwise stopping the execution of the program.
For example,
\[l : \mathit{ListPtr}\;a,\ l_2 : \mathit{Ref}\; (a,\,\mathit{ListPtr} \; a) \vdash \sguard{\rcl{l} * l_2} : \mathbf{1}\]
can be understood as a program checking the cell $l_2$ is not any node of linked list $l$.
With separation guards and our effect system, we can formulate some program equations beyond the expressiveness of previous region systems.
For example, given judgement~(\ref{equ:tvs}), then
\[ \sguard{\rcl{l} * l_2};\mathit{put} \; l_2 \; v; t\; l \quad = \quad \sguard{\rcl{l} * l_2}; t\; l; \mathit{put} \; l_2 \; v  \]
says that if cell $l_2$ is not a node of linked list $l$, then modification to $l_2$ can be swapped with $t\;l$, which only accesses list $l$.
In Section~\ref{sec:case}, we demonstrate using these transformations, we can equationally prove the correctness of the Schorr-Waite traversal algorithm (on binary trees)~\cite{Schorr1967} quite straightforwardly.

\Zhixuan{Here will be a paragraph summarising contributions and the paper structure.}

\section{Limitation of Existing Region Systems}\label{sec:prob}
This section we show the limitation of static region systems with a practical example of equational reasoning: proving the straightforward recursive implementation of |foldr| for linked lists is semantically equivalent to an optimised implementation using only constant space.
The straightforward implementation is not tail-recursive and thus it uses space linear to the length of the list, whereas the optimised version cleverly eliminate the space cost by reusing the space of the linked list itself to store the information needed to control the recursion and restore the linked list after the process.
This optimisation is essentially the Schorr-Waite algorithm~\cite{Schorr1967} adapted to linked lists, whose correctness is far from obvious and has been used as a test for many approaches of reasoning about pointer-manipulating programs \Zhixuan[red]{Citations}.

In the following, we start with an attempt to an algebraic proof of the correctness of this optimisation---transforming the optimised implementation to the straightforward one with equational axioms of the programming language and its effect operations.
From this attempt, we can see the limitation of static region systems: we want the region partitioning to match the logical structure of data in memory, but when the structure is mutable, static region systems do not allow region partitioning to be mutable to reflect the change of the underlying structure.

\subsection{Motivating Example: Constant-time |foldr| for Linked Lists}
The straightforward implementation of folding (from the tail side) a linked list is simply
\begin{code}
foldrl : (A -> B -> B) -> B -> ListPtr A -> _F(B)
foldrl f e v =  case v of 
                  Nil    -> return e
                  Ptr r  -> {  (a, n) <- get r; b <- foldrl f e n;
                               return (f a b) }
\end{code}
where |_F(B)| is the type of computations of |B| values.
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

\subsection{Verifying |foldrlsw|: First Attempt}
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
Assuming we have some inductive principle allowing us to apply Equation~\ref{equ:hyp} to |fwd f e v n| since |n| is the tail of list |v| (We will discuss inductive principles later in Section~\ref{sec:sepinf}), we proceed:
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
The second problem happens in the type system: Now that the reference type is indexed by regions, the type of the $i$-th cell of a linked list may be upgraded to $|Ref|\ \epsilon_{i}\ (a,\,|ListPtr|_{i+1}\ a)$.
But this type signature prevents the second field of this cell pointing to anything but its successor, making programs changing the list structure like |foldrlsw| untypable.
This problem cannot be fixed by simply change the type of the second field to be the type of references to arbitrary region, because we will lose track of the region information necessary for our equational reasoning when reading from that field.

The failure of static region systems in this example is due to the fact that a static region system presumes a fixed region partitioning for a program.
While as we have seen in the example above, in different steps of our reasoning, we may want to partition regions in different ways:
it is not only because we need region partitioning to match the logic structure of memory cells which is mutable---as in the example above, a node of a list is modified to points to something else and thus should no longer be in the region of the list.
Even when all data are immutable, we may still want a more flexible notion of regions---in one part of a program, we probably reason at the level of lists and thus we want all the nodes of a list to be in the same region; while in another part of the same program, we may want to reason at the level of nodes, then we want different nodes of a list in different regions.

\section{Mutable Region System}
Our observations in the last section suggest us to develop a more flexible region system.
Our idea is to let the points-to structure of memory cells \emph{determine} regions: a region is either a single memory cell or all the cells reachable from one cell along the points-to structure of cells.
We found it is simpler to implement this idea in a logic system rather than a type system: we introduce effect predicates $\effect{(\cdot)}{\epsilon} $ on programs of computation types where $\epsilon$ is a list of effect operations in the language and two `virtual' operations $|get|_r$ and $|put|_r$ where $r$ is a region in the above sense.
The semantics of $\effect{t}{\epsilon}$ is that program $t$ only invokes the operations in $\epsilon$.
Inference rules for effect predicates are introduced.

\subsection{Preliminaries: the Language and Logic}
%\Zhixuan[red]{To write: this section fixes a programming language of algebraic effects and briefly describes an equational logic for it following \cite{Plotkin2008,Pretnar2010}.But we need to distinguish two equalities: $\eqC$ and $=_{\mathit{AE}}$.}

As the basis of discussion, we fix a small programming language with algebraic effects based on Levy's call-by-push-value calculus~\cite{Levy2012call}. 
For a more complete treatment of such a language, we refer the reader to Plotkin and Pretnar's work~\cite{Plotkin2008}. 
The syntax and typing rules of this language are listed in Figure~(\ref{lang-syn}) and Figure~(\ref{lang-typing}).
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
    && \mid\ & |\x : A . t| \mid |t v| \mid |force v| \mid |op v| \mid \mu x : \mathbf{U} \underline{A}.\ t \\
    &\text{Operations: } & |op| ::=\ & |fail| \mid |get| \mid |put| \mid |new| \mid \ldots 
  \end{align*}
  \caption{Syntax of the language.}\label{lang-syn}
\end{figure}

\begin{figure}
  \centering
  \Zhixuan{To be added}
  \caption{Typing rules of the language.}\label{lang-typing}
\end{figure}



We assume that the language includes the effect of failure and \emph{local state}~\cite{Staton2010}.
Failure has one nullary operation |fail| and no equations.
Local state has the following three operations:
\begin{align*}
  |get|_D &: |Ref D -> (udl(D))| \\
  |put|_D &: |(Ref D) ** D -> (udl(Unit))| \\
  |new|_D &: |D -> (udl(Ref D))|
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
\labelcodetag{New-Disj}{law:disj}
\vspace{-1cm}
\end{center}
which is a special case of the axiom schema $\text{B}3_n$ in~\cite{Staton2010} but is sufficient for our purposes.
\Zhixuan{In the standard treatment, these equations come with a context of free variables like $l_2$ in the last one. Do you find it strange if I omit them?}

Semantics ...

We also need an equational logic for reasoning about programs of this language.
We refer the reader to the papers~\cite{Pretnar2010,Plotkin2008} for a complete treatment of its semantics and inference rules.
Here we only record what is needed in this paper.
The formulas of this logic are:
\begin{align*}
  \phi ::=\  & t_1 \eqC t_2 \mid t_1 \eqA t_2 \mid \forall x : A.\ \phi \mid \forall x : \underline{A}.\ \phi \\
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
In this paper, we will only use the first three kinds of rules.

A difference from the logic defined in~\cite{Plotkin2008,Pretnar2010} is that we distinguish equivalences derived only from CBPV rules (written as $\eqC$) and those derived from both CBPV rules and effect theories (written as $\eqA$).
This is preferable for our purpose because we do not want to regard |{v <- get l; put l v}| and |return ()| as the same because they invoke different operations.

\subsection{Effect System as Logic Predicates}
%\Zhixuan{This subsection defines the well-formedness and semantics of predicates $\effect{t}{\epsilon}$: $t$ is a (possibly) infinite operation tree consisting only operations in $\epsilon$.}

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
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}{\typing{\Gamma}{\effect{t}{\epsilon, |op|}}{\mathbf{form}}}
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|Ref D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_v}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\and
  \inferrule{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}} \\ \typing{\Gamma}{v}{|ListPtr D|}}{\typing{\Gamma}{\effect{t}{\epsilon, o_{\rcl{v}}}}{\mathbf{form}}}\;(o \in \set{|get|,\;|put|})
\end{mathpar}

The intended meaning of the formula $\effect{t}{\epsilon}$ is that the computation $t$ only invokes operations in $\epsilon$.
Specially, $|get|_v$ and $|put|_v$ in $\epsilon$ mean reading and writing the reference $v : |Ref D|$, and $|get|_{\rcl{v}}$ and $|put|_{\rcl{v}}$ mean reading and writing all the cells linked from $v$ of type $|ListPtr D|$.

The semantics of $\sembrk{\typing{\Gamma}{\effect{t}{\epsilon}}{\mathbf{form}}}$ (abbreviated as $\sembrk{\effect{t}{\epsilon}}$ below) is a subset of $\sembrk{\Gamma}$ that is the \emph{least}-fixed-point solution of the following mutual-recursive equations.
\Zhixuan[red]{No, this definition is wrong.
A plausible definition: for all memory configuration (in which regions in $\epsilon$ are fintie), running $t$ (with get/put handled and other operations un-handled) only operates corresponding cells (and terminates).}
\begin{align*}
  &\sembrk{\effect{t}{\epsilon}} &= \set{ \gamma \in \sembrk{\Gamma} \mid \exists & \typing{\Gamma}{v}{A}.\ \sembrk{t}(\gamma) = \sembrk{|return v|}(\gamma)} \\
%
  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|op : B -> (udl(C))| \in \epsilon,\ \typing{\Gamma}{v}{B},\ \typing{(\Gamma, c : C)}{k}{\mathbf{F}A}.\\
  &&&\sembrk{t}(\gamma) = \sembrk{|c <- op v; k|}(\gamma) \wedge \forall v_c \in \sembrk{C}.\ (\gamma, v_c) \in \sembrk{\effect{k}{\epsilon}}} \\
%
  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|get|_v \in \epsilon,\ \typing{(\Gamma, c : D)}{k}{\mathbf{F}A}.\\
  &&&\sembrk{t}(\gamma) = \sembrk{|c <- get v; k|}(\gamma) \wedge \forall v_c \in \sembrk{D}.\ (\gamma, v_c) \in \sembrk{\effect{k}{\epsilon}}} \\
%
  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|put|_v \in \epsilon,\ \typing{\Gamma}{d}{D},\ \typing{\Gamma}{k}{\mathbf{F}A}.\\
  &&&\sembrk{t}(\gamma) = \sembrk{|put (v,d); k|}(\gamma) \wedge \gamma \in \sembrk{\effect{k}{\epsilon}}} \\
%
  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|get|_{\rcl{v}} \in \epsilon, \text{if } \sembrk{v}(\gamma) = \sembrk{|Nil|} \text{ then } \gamma \in \sembrk{\effect{t}{\epsilon \setminus \set{|get|_{\rcl{v}}, |put|_{\rcl{v}}}}} \\
  &&& \quad \text{otherwise } \exists\; l'.\  \sembrk{t}(\gamma) = \sembrk{|(d,n) <- get l'; k|}(\gamma) \\
  &&& \quad\wedge \forall v_d, v_n.\ (\gamma, v_d, v_n) \in \sembrk{\effect{k}{\epsilon[\rcl{n}/\rcl{v}] \cup \epsilon[l'/\rcl{v}]}}} \\
%
  &                              &\cup \set{ \gamma \in \sembrk{\Gamma} \mid \exists &|put|_{\rcl{v}} \in \epsilon, \text{if } \sembrk{v}(\gamma) = \sembrk{|Nil|} \text{ then } \gamma \in \sembrk{\effect{t}{\epsilon \setminus \set{|get|_{\rcl{v}}, |put|_{\rcl{v}}}}} \\
  &&& \quad \text{otherwise } \exists\; l',\; d,\; k.\  \sembrk{t}(\gamma) = \sembrk{|put (l',d); k|}(\gamma) \\
  &&& \quad\wedge \gamma \in \sembrk{\effect{k}{\epsilon[l'/\rcl{v}]}}}
\end{align*}
\subsection{Inference Rules}
\Zhixuan{It sounds worthwhile to to de-couple the inferences of terminance and possible operations }
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
We have the following rules to infer the possible operations used by a program.
\begin{mathpar}
  \inferrule{ }{\judgeThree{\Gamma}{\Psi}{\effect{|return x|}{\emptyset}}} \textsc{ R-Pure}
  \and
  \inferrule{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}} \\ \epsilon \subseteq \epsilon'}{\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon'}}} \textsc{ R-Sub}
  \and
  \inferrule{\judgeOneDef{t \eqC t' \;\wedge\; \effect{t'}{\epsilon}}}{\judgeOneDef{\effect{t}{\epsilon}}} \textsc{ R-Eq}
\end{mathpar}
and for any ${|op : A -> udl(B)| \in \epsilon}$ that is not $|get|/|put|_{\rcl{v}}$,
\begin{mathpar}
  \inferrule{\judgeThree{\Gamma, a : B}{\Psi}{\effect{|k|}{\epsilon}}}{\judgeOneDef{\effect{|(a <- op v; k)|}{\epsilon}}} \;  \textsc{ R-Op}
\end{mathpar}
\textsc{R-Sub} says if $t$ only operates on $\epsilon$ then it also operates on any larger $\epsilon'$.
\textsc{R-Eq} says the predicate $\effect{\cdot}{\epsilon}$ is compatible with CBPV-equivalence.
For example, since programs $|(if True then t1 else t2)| \eqC |t1|$, if $\effect{t_1}{\epsilon}$, we also have $\effect{|if True then t1 else t2|}{\epsilon}$.

\textsc{R-Op} deals with the case where the program invokes an operation in $\epsilon$.
It is worth mentioning that the rule \textsc{R-Op} requires $\effect{k}{\epsilon}$ for \emph{arbitrary} $a : B$ as the premise, even the effect theory for |op| may constrain the possible values for |a| returned by |op|.

If $\epsilon$ contains $|get|_{\rcl{v}}$ or $|put|_{\rcl{v}}$, the program can read or write the cells linked from $|v : ListPtr D|$.
When $|v = Nil|$, the program get no cells to access from $\rcl{v}$.
When $|v = Ptr v'|$, the program can read or write the cell |v'|, and if it reads it by |(a, n) <- get v'|, its allowed operation on $\rcl{v}$ is inherited by $\rcl{n}$ and $v'$, which is achieved by substituting $\rcl{n}$ for $\rcl{v}$ and $v'$ for $\rcl{v}$ in $\epsilon$ in the inference rules below.

\vspace{8pt}
If ${|get|_{\rcl{v}}} \in \epsilon$
\vspace{-12pt}
\begin{mathpar}
  \inferrule{\judgeOneDef{\effect{|t Nil|}{\epsilon \setminus \set{|get|_{\rcl{v}},\ |put|_{\rcl{v}}}}} \\ 
             \judgeThree{\Gamma, v'}{\Psi}{|t (Ptr v')| \eqC |{(a, n) <- get v'; k}|} \\
             \judgeThree{\Gamma, v', a, n}{\Psi,\ \effect{|t n|}{\epsilon[\rcl{n}/\rcl{v}]}}{\effect{k}{\epsilon[\rcl{n}/\rcl{v}] \cup \epsilon[v'/\rcl{v}]}}}
             {\judgeOneDef{\effect{|t v|}{\epsilon}}}
\end{mathpar}

If $|put|_{\rcl{v}} \in \epsilon$
\vspace{-12pt}
\begin{mathpar}
  \inferrule{ \judgeOneDef{\effect{|t Nil|}{\epsilon \setminus \set{|get|_{\rcl{v}},\ |put|_{\rcl{v}}}}} \\
             \judgeOneDef{|t (Ptr v')| \eqC |{put v' c; k}|} \\
             \judgeThree{\Gamma}{\Psi}{\effect{k}{\epsilon[v'/\rcl{v}]}}}
            {\judgeOneDef{\effect{|t v|}{\epsilon}}} 
\end{mathpar}
The inference rule for $|get|_{\rcl{v}}$ also encodes the inductive principle for (finite) linked list by adding $\effect{|t n|}{\epsilon[\rcl{n}/\rcl{l}]}$ to the assumption for $k$.
\Zhixuan[red]{It is obviously a very restrictive way because it restricts the recursive structure of |t| to be aligned with one list $\rcl{v}$.
As a consequence, this rule cannot deal with $\effect{|merge p q|}{\set{|get|_{\rcl{p}}, |put|_{\rcl{p}}, |get|_{\rcl{q}}, |put|_{\rcl{q}}}}$, the program merging two lists.

But I have no good idea how to work around.
Perhaps we need to upgrade predicates $(\effect{\cdot}{\epsilon})$---currently only on $\mathbf{F}A$---to higher order functions?}

\begin{theorem}[Soundness]
  If $\judgeThree{\Gamma}{\Psi}{\effect{t}{\epsilon}}$, then $\sembrk{\Psi} \subseteq \sembrk{\effect{t}{\epsilon}}$.
\end{theorem}
\begin{proof}
\Zhixuan{To add. Hopefully it will not be very difficult.}
\end{proof}

\section{Separation Guards}
\Zhixuan[red]{Given definition and semantics of separation guards.}

Our region predicates defined above can be used to show a program only operates on certain memory cells determined by some variables, but this information is useful only when we know the cells that two programs respectively operates on are disjoint.
Ultimately, disjointness comes from the \ref{law:disj} axiom of |new| saying that references returned by distinct |new| invocations are different.
But this axiom is too primitive for practical use.
In this section, we introduce \emph{separation guards} for tracking disjointness more easily at a higher level.

Following the notation of separation logic~\cite{Reynolds2002}, we write $\phi = l_1 * l_2 * \cdots * l_n$ to denote that cells described by $l_i$ are dijoint.
Here $l_i$ can be either a value of type |Ref D| or |_r(v)| for a value |v| of type |ListPtr D|.
A separation guard $\sguard{\phi}$ is a computation of type $\mathbf{F}|Unit|$:
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
\Zhixuan[red]{This definition may not be formal enough because we didn't assumed the language has a type |Set| to implement |x|, but we don't necessarily need to implement separation guards in the language, we can treat it as a new language construct and interpret it freely.}
|sg(phi)| checks cells described by $\phi$ are distinct.
For a |ListPtr D| element in $\phi$, the terminance of |sg(phi)| also implies this list in memory is finite.

Separation guards can be used to assert preconditions of some program equivalences.
For example, if |t| is a program traversing list |l : ListPtr D|, it is (algebraically) equivalent to |return ()| when |l| is a finite list:
\[ |sg(_r(l)); t| \quad\eqA\quad |sg(_r(l)); return ()| \]
The equality holds whenever |l| is finite or not: when |l| is infinite, |sg(_r(l))| diverges or fails.
In both cases, it is a left-zero of the sequencing operator ``$ \;;\; $'' and thus the equality holds.

\subsection{Inference Rules}\label{sec:sepinf}
Although separation guards can be defined as a concrete program as above, we intend them to be used abstractly with the following inference rules.
Define $\preEq{c}{a}{b}$ to be $(c;a) \eqA (c;b)$.
\begin{mathpar}
  \inferrule{ }{\preEq{|sg(phi)|}{|new t|}{|(l <- new t; sg(phi * l); return l)|}}
  \and
  \inferrule{\judgeThree{\Gamma}{\Psi, l_1 \neq l_2}{t_1 \eqA t_2}}{ \judgeOneDef{\preEq{\sguard{l_1 * l_2}}{t_1}{t_2}} }
  \and
  \inferrule{ }{|return Nil| \eqA |(l <- return Nil; sg(_r(l)); return l)|}
  \and
  \inferrule{ }{\preEq{\sguard{\rcl{l}}}{|new (Cell a l)|}{|(l' <- new (Cell a l); sg(_r(l')); return l')|}}
  \and
  \inferrule{ \texttt{base case} \\ \texttt{inductive case}}{ \judgeOneDef{\preEq{\sguard{\rcl{l} * \phi}}{t_1}{t_2}}} \quad(\textsc{ListInd})
\end{mathpar}
where \texttt{base case} is $\judgeTwoDef{\Psi, l \eqA |Nil|}{\preEq{\sguard{\phi}}{t_1}{t_2}}$ and \texttt{inductive case} is
\begin{gather*}
\judgeTwoDef{l \eqA |Ptr l'|, \texttt{hyp}}{\preEq{\left(|(Cell _, n) <- get l'; sg(l' * _r(n) * phi)|\right)}{t_1}{t_2}} \\
  \texttt{hyp} =_{\mathtt{def}} \preEq{\sguard{\rcl{n} * \phi}}{t_1}{t_2}
\end{gather*}
$\sguard{\cdot}$ has the following structural properties:
\begin{mathpar}
\inferrule{}{\sguard{ \phi_1 * \phi_2 } \eqA \sguard{ \phi_2 * \phi_1 }}
\and
\inferrule{}{\sguard{ (\phi_1 * \phi_2) * \phi_3} \eqA \sguard{  \phi_1 * (\phi_2 * \phi_3) }}
\and
\inferrule{}{\sguard{\top} \eqA |return ()|}
\and
\inferrule{}{\sguard{\phi_1 * \phi_2} \eqA (\sguard{\phi_1 * \phi_2}; \sguard{\phi_1})}
\and
\inferrule{}{(\sguard{\phi_1}; \sguard{\phi_2}) \eqA (\sguard{\phi_2}; \sguard{\phi_1})}
\end{mathpar}

\begin{proposition}
The inference rules above are sound.
\end{proposition}
\begin{proof}
  \Zhixuan{It'll be a large verifying proof.}
\end{proof}

\subsection{Effect-dependent Transformations}
A frame rule:
\[
\inferrule{\judgeOneDef{\effect{t_1}{\overline{\phi_1}}} \\ \judgeOneDef{\preEq{\sguard{\phi_1}}{t_1}{t_2}}}{\judgeOneDef{\preEq{\sguard{\phi_1 * \phi_2}}{t_1}{(t_2;\sguard{\phi_2})}}}
\]

Commutativity lemma
\[
\inferrule{\judgeOneDef{\effect{t_i}{\overline{\phi_i}}} \; (i = 1, 2) }{\judgeOneDef{\preEq{\sguard{\phi_1 * \phi_2}}{(t_1; t_2)}{(t_2; t_1)}}}
\]

\begin{proof}
\Zhixuan{Proving the above two rules using the inference rules of separation guards and effect predicate.}
\end{proof}

\section{Case Study: Equational Reasoning about Schorr-Waite Traversal}\label{sec:case}

\section{Related Work}
Algebraic effects:~\cite{Plotkin2002}

Effect systems:~\cite{Lucassen1988,Talpin1992,Marino2009}

\section{Conclusion}
%
% ---- Bibliography ----
%
% BibTeX users should specify bibliography style 'splncs04'.
% References will then be sorted and formatted in the correct style.
%
\bibliographystyle{splncs04}
\bibliography{sep.bib}

\end{document}
