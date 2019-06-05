% =========================================================================
%  PhD thesis template for pdflatex
%   First version by Atsushi Koike on Mar. 26 2015
%
%    This file specifies the following:
%        - Font
%        - Appearance of Text (Hyphenation and Letter-spacing)
%        - Page Layout
%        - Theorem Environments
%        - Header and Footer
%        - Chapter Header
%        - Table of Contents
%        - Clickable PDF
%        - Title Page and PDF-title
%
%    NOTE:
%        - Don't use TeX+DVI (dvipdfm), or microtype doesn't work.
%
% =========================================================================

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{sokendai_thesis}[2015/11/22 v1.4]
\LoadClass[12pt,twoside]{book}


% =====================================================
%  Packages
% =====================================================

% \usepackage{amsmath}
\usepackage{latexsym}
%\usepackage{ascmac}
\usepackage{graphicx}
\usepackage[font=small, labelfont=bf]{caption}

% Pseudo codes
%\usepackage[ruled,vlined,linesnumbered]{algorithm2e}
\usepackage[chapter]{algorithm}
\usepackage{algpseudocode}
\renewcommand{\thealgorithm}{\arabic{chapter}.\arabic{algorithm}}

% Dummy text (for testing)
%\usepackage{lipsum}
% \usepackage{blindtext}
%\usepackage{kantlipsum}


% =====================================================
%  Font
% =====================================================

% Support Japanese Text
% \usepackage[utf8]{inputenc}
\usepackage[whole]{bxcjkjatype}
%\usepackage[whole,ipaex]{bxcjkjatype}


\usepackage[T1]{fontenc}

% ------------------------------------------------------
%  Choose one line of the following
% ------------------------------------------------------

% \usepackage{mathptmx} % standard font
%\usepackage{stix}
\usepackage{libertine} \usepackage[libertine]{newtxmath}
%\usepackage{newtxtext,newtxmath}
%\usepackage{mathpazo}
%\usepackage{kpfonts}
%\usepackage{txfonts}
%\usepackage{lmodern}


% =====================================================
%  Appearance of Text (Hyphenation and Letter-spacing)
% =====================================================

%\usepackage{microtype}
%\usepackage[final, stretch=30, shrink=60]{microtype}
\usepackage[final, stretch=60, shrink=20]{microtype}


% =====================================================
%  Page Layout
% =====================================================

\usepackage{setspace}
\onehalfspacing % one and half space
%\doublespacing % double space
%\renewcommand{\baselinestretch}{1.2}

\usepackage[hmarginratio=1:1]{geometry}
\usepackage{aliascnt}

% =====================================================
%  Theorem Environments
% =====================================================

% \newtheorem{theorem}{Theorem}[chapter]
% \newtheorem{lemma}[theorem]{Lemma}
% \newcommand{\sq}{\hbox{\rlap{$\sqcap$}$\sqcup$}}
% \newcommand{\qed}{\hspace*{\fill}\sq}
% \newenvironment{proof}{\noindent {\bf Proof.}\ }{\qed\par\vskip 4mm\par}
% \newtheorem{define}[theorem]{Definition}
% \newtheorem{problem}[theorem]{Problem}

\AtEndPreamble{%
  \@ifundefined{theorem}{%
  \newtheorem{theorem}{Theorem}[section]
  }{}
  \@ifundefined{conjecture}{%
  \newaliascnt{conjecture}{theorem}
  \newtheorem{conjecture}[conjecture]{Conjecture}
  \aliascntresetthe{conjecture}
  }{}
  \@ifundefined{proposition}{%
  \newaliascnt{proposition}{theorem}
  \newtheorem{proposition}[proposition]{Proposition}
  \aliascntresetthe{proposition}
  }{}
  \@ifundefined{lemma}{%
  \newaliascnt{lemma}{theorem}
  \newtheorem{lemma}[lemma]{Lemma}
  \aliascntresetthe{lemma}
  }{}
  \@ifundefined{corollary}{%
  \newaliascnt{corollary}{theorem}
  \newtheorem{corollary}[corollary]{Corollary}
  \aliascntresetthe{corollary}
  }{}
  \@ifundefined{example}{%
  \newaliascnt{example}{theorem}
  \newtheorem{example}[example]{Example}
  \aliascntresetthe{example}
  }{}
  \@ifundefined{definition}{%
  \newaliascnt{definition}{theorem}
  \newtheorem{definition}[definition]{Definition}
  \aliascntresetthe{definition}
  }{}
  \@ifundefined{notation}{%
  \newaliascnt{notation}{theorem}
  \newtheorem{notation}[notation]{Notation}
  \aliascntresetthe{notation}
  }{}

  \newtheorem{prereq}{Prerequisites}

  \let\citeN\cite
  \let\cite\citep
  \let\citeANP\citeauthor
  \let\citeNN\citeyearpar
  \let\citeyearNP\citeyear
  \let\citeNP\citealt
  \DeclareRobustCommand\citeA
     {\begingroup\NAT@swafalse
       \let\NAT@ctype\@ne\NAT@partrue\NAT@fullfalse\NAT@open\NAT@citetp}%
  \providecommand\newblock{}%
% \newcommand\shortcite[2][]{%
%   \ifNAT@numbers\cite[#1]{#2}\else\citeyearpar[#1]{#2}\fi}
% \def\bibliographystyle#1{%
%   \ifx\@begindocumenthook\@undefined\else
%     \expandafter\AtBeginDocument
%   \fi
%     {\if@filesw
%        \immediate\write\@auxout{\string\bibstyle{#1}}%
%      \fi}}
% \RequirePackage{graphicx}
% \RequirePackage[prologue]{xcolor}
% \definecolor[named]{ACMBlue}{cmyk}{1,0.1,0,0.1}
% \definecolor[named]{ACMYellow}{cmyk}{0,0.16,1,0}
% \definecolor[named]{ACMOrange}{cmyk}{0,0.42,1,0.01}
% \definecolor[named]{ACMRed}{cmyk}{0,0.90,0.86,0}
% \definecolor[named]{ACMLightBlue}{cmyk}{0.49,0.01,0,0}
% \definecolor[named]{ACMGreen}{cmyk}{0.20,0,1,0.19}
% \definecolor[named]{ACMPurple}{cmyk}{0.55,1,0,0.15}
% \definecolor[named]{ACMDarkBlue}{cmyk}{1,0.58,0,0.21}
}

% =====================================================
%  Header and Footer
% =====================================================

\usepackage{fancyhdr}
\addtolength{\headheight}{\baselineskip}
\pagestyle{fancy}
\renewcommand{\chaptermark}[1]{\markboth{\chaptername\ \thechapter.\ #1}{}} % corresponding to \rightmark
\renewcommand{\sectionmark}[1]{\markright{\thesection\ \ #1}{}} % corresponding to \leftmark
\fancyhf{} % clear all header and footer fields
\fancyhead[LE,RO]{\bfseries \thepage} % left field of even pages and right field of odd pages
\fancyhead[LO]{\bfseries \nouppercase \rightmark} % left field of odd pages
\fancyhead[RE]{\bfseries \nouppercase \leftmark} % right field of even pages
\fancypagestyle{plain}{%
  \fancyhf{} % get rid of header and footer fields
  \renewcommand{\headrulewidth}{0pt} % get rid of the line
  \fancyhead[LE,RO]{\bfseries \thepage} % left field of even pages and right field of odd pages
}

% Get rid of page numbers on empty pages before chapters
\makeatletter
\def\cleardoublepage{\clearpage\if@twoside \ifodd\c@page\else
  \hbox{}
  \thispagestyle{empty}
  \newpage
  \if@twocolumn\hbox{}\newpage\fi\fi\fi}
\makeatother


% =====================================================
%  Chapter Header
% =====================================================

%Options: Sonny, Lenny, Glenn, Conny, Rejne, Bjarne, Bjornstrup
%\usepackage[Lenny]{fncychap}

% Options:
\usepackage[palatino]{quotchap}

% =====================================================
%  Table of Contents
% =====================================================

% Go along with these packages
\usepackage[nottoc]{tocbibind}
\usepackage[title,titletoc]{appendix}


% =====================================================
%  Clickable PDF
% =====================================================

\usepackage{color}
\definecolor{scarlet}{RGB}{ 141, 27, 53}
\definecolor{steelblue}{RGB}{ 11, 65, 108}
\usepackage[titles]{tocloft}
\usepackage{hyperref}
\hypersetup{
  unicode,
  bookmarks=true,
  bookmarksnumbered=true,
  bookmarksopen=true,
  linktocpage,
  colorlinks=true,
  citecolor=scarlet,
  linkcolor=steelblue,
  urlcolor=steelblue,
  setpagesize=false,
  linktoc=all
}
\urlstyle{same}

% PDF-title and PDF-author are set in "maketitle" (using \hypersetup)


% =====================================================
%  Title Page and PDF-title
% =====================================================

\makeatletter % make @ symbol a letter (usually one cannot use @ as a letter)

\newcommand{\@crest}{}
\newcommand{\crest}[1]{\renewcommand{\@crest}{\includegraphics[pagebox=trimbox,width=0.7\textwidth]{#1}}}

\newcommand{\@keywords}{}
\newcommand{\keywords}[1]{\renewcommand{\@keywords}{#1}}


% ------------------------------------------------------
%  New maketitle
% ------------------------------------------------------

\renewcommand{\maketitle}{

% PDF title
\hypersetup{
  pdftitle={\@title},
  pdfauthor={\@author},
  pdfsubject={PhD Thesis},
  pdfkeywords={\@keywords}
}

\begin{spacing}{2}
\centering
{\Huge \bfseries \@title}
\par
\vskip 1.5ex
\par
{\large by}
\par
\vskip 1ex
{\Large \bfseries \@author}
\par
\vskip 8ex
{\Large \bfseries Master Dissertation}
\end{spacing}

\vskip 1ex
\begin{spacing}{1.5}
\centering
\large
submitted to the Department of Informatics
%\par
%in partial fulfilment of the requirements for the degree of
%\par
\end{spacing}

% \vskip 6ex
% \begin{center}
% {\Large \bfseries \textit{Doctor of Philosophy}}
%\par
%\end{center}

\vskip 8ex
\begin{center}
\@crest
\end{center}

% \vfill

\vskip 7ex
\begin{spacing}{2}
\centering
{\large SOKENDAI (The Graduate University for Advanced Studies)}
\par
{\large \@date}
\par
\end{spacing}

\thispagestyle{empty}

%% Committee
%\newpage
%\begin{center}
%{\Large \bfseries Committee}
%\end{center}
%
%\begin{center}
%  \begin{tabular}{ll}
%    AAA BBB (Chair)      & National Institute of Informatics / Sokendai \\
%    CCC DDD              & EEE University \\
%    FFF GGG              & National Institute of Informatics / Sokendai
%  \end{tabular}
%\end{center}
%\thispagestyle{empty}


}
\makeatother



% =====================================================
%  TODO notes for draft version
% =====================================================

% \makeatletter
% \DeclareOption{todo}{\newcommand{\@displaytodo}{1}}
% \ProcessOptions
% \ifx\@displaytodo\undefined
% \usepackage[disable]{todonotes}
% \else
% \usepackage[draft,textwidth=2.7cm]{todonotes}
% \setlength{\marginparwidth}{2.7cm}
% \fi
% \makeatother
%
% \newcounter{todoListItems}
% \newcommand{\mytodo}[2][]
% {\addtocounter{todoListItems}{1}
% \todo[size=\footnotesize, color=green!40, caption={\protect\hypertarget{todo\thetodoListItems}{}\% thesection: #2}, #1]
% {\hyperlink{todo\thetodoListItems}{#2} }}


%
% How to use todo notes
%    - Final version
%        - \documentclass{sokendai_thesis}
%        - Todo notes are not printed
%    - Draft version
%        - \documentclass[todo]{sokendai_thesis}
%        - Todo notes are printed using the following command
%            - \mytodo[inline]{This is a inline todo note}
%            - \mytodo{This is a todo note at margin}
%





