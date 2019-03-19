%
%
%              |
%              |
%              |
%              |
%              |
%              |
%              v
%
% The Latex template is made out of parts found on overleaf.com, pretty much a mishmash of templates from other homeworks of both of us plus stuff found on the report example repository
% The ignore blocks contain haskell code that we want ghc to load but for it to not be visible in the report
%
%              ^
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |
%              |

\long\def\ignore#1{}
\documentclass[12pt,english]{article}
\usepackage[a4paper,bindingoffset=0.2in,%
            left=1in,right=1in,top=1in,bottom=1in,%
            footskip=.25in]{geometry}
\usepackage{pdflscape}

\usepackage{graphicx}
\usepackage{tikz}
\usepackage{amsmath,amsthm,amssymb}

\usepackage[T1]{fontenc} % better fonts

% Haskell code listings in our own style
\usepackage{listings,color}
\definecolor{lightgrey}{gray}{0.35}
\definecolor{darkgrey}{gray}{0.20}
\definecolor{lightestyellow}{rgb}{1,1,0.92}
\definecolor{dkgreen}{rgb}{0,.2,0}
\definecolor{dkblue}{rgb}{0,0,.2}
\definecolor{dkyellow}{cmyk}{0,0,.7,.5}
\definecolor{lightgrey}{gray}{0.4}
\definecolor{gray}{gray}{0.50}
\lstset{
  language        = Haskell,
  basicstyle      = \scriptsize\ttfamily,
  keywordstyle    = \color{dkblue},     stringstyle     = \color{red},
  identifierstyle = \color{dkgreen},    commentstyle    = \color{gray},
  showspaces      = false,              showstringspaces= false,
  rulecolor       = \color{gray},       showtabs        = false,
  tabsize         = 8,                  breaklines      = true,
  xleftmargin     = 8pt,                xrightmargin    = 8pt,
  frame           = single,             stepnumber      = 1,
  aboveskip       = 2pt plus 1pt,
  belowskip       = 8pt plus 3pt
}
\lstnewenvironment{code}[0]{}{}
\lstnewenvironment{showCode}[0]{\lstset{numbers=none}}{} % only shown, not compiled

\usepackage{biblatex}
\addbibresource{bibl.bib}

\begin{document}

%\begin{landscape}

%\pagenumbering{gobble}

\title{Model Checking on Succinct Epistemic Models}
\author{May Lee\\Dimitrios Koutsoulis} 
 
\maketitle

\ignore{
\begin{code}
module SuccinctDEL where
import Data.List
\end{code}
}

\begin{abstract}
    This paper documents our Haskell implementation for succinct epistemic models, as envisaged by Charrier and Schwartzenruber [2] and an algorithm for model checking given these models. The advantages of this representation is expected to be a more concise description of epistemic states and lower computational complexity during model checking.   
\end{abstract}

\tableofcontents

\pagebreak

\section{Introduction}
In the framework of Dynamic Epistemic Logic, the beliefs of agents under a given situation are encoded by Epistemic Models. 
The beliefs pertaining to events taking place are encoded by Event Models. 
The Product Update defined based on these two represents what the agents believe and how they would update their believes after an event has taken place. 

Model Checking is the process of verifying whether some proposition $\phi$ of the language of propositional epistemic logic $\mathcal{L}_{EL}$ holds true for a given Epistemic Model $M$, universally $M\vDash \phi$ or locally $M,w\vDash \phi $. 
When the Epistemic Model is a Kripke Model, this is done in accordance to the Kripke semantics. 
An Epistemic Kripke Model consists of a set of agents $I$, a set of worlds $W$, an accessibility relation $R_i$ for each of the agents $i \in I$ and a valuation function $V: W \rightarrow \mathcal{L}_{PL}$ where $\mathcal{L}_{PL}$ is the language of propositional logic. 

\section{Motivation}
Epistemic Models are usually expressed as Kripke Models. 
Alternative representations have been proposed that are purportedly more concise. 

One of them is the Knowledge Structure by J. V. Benthem, M. Gattinger et al. \cite{GattingerThesis2018} \cite{van2015symbolic} where worlds are encoded as subsets of some vocabulary $V$ that satisfy some state law $\theta $. The relation of each agent $i$ is represented by a subset of $V$ called the observable by $i$ variables $O_i$. 
An exponential increase in conciseness is achieved this way. 
It is not known whether model checking on Knowledge Structures can be done in PSPACE as is the case for Kripke Models.

We know this to be the case for another concise representation, namely the succinct one by T. Charrier and F. Schwarzentruber \cite{charrier:hal-01487001}. 
This is similar to Knowledge Structures but instead of subsets of observable variables we have a mental program, i.e. a recursively defined relation between subsets of $V$, $\pi_i$ in the notation of \cite{charrier:hal-01487001}, that encodes the accessibility relation for each agent $i$. 
This calls for a Haskell implementation of the aforementioned Succinct Epistemic Model and its model checking algorithm for the static part.

\section{Implementation}
	We implemented Kripke and Succinct Epistemic models. 
	We also implemented translation functions between the two. 
	Note that the translation from Kripke to Succinct models introduces nominal propositions whose sole purpose is to identify a world each. 
	Given that we represent agents, worlds and propositions of Kripke models as positive integers, we let the nominal propositions be the negations of the worlds they represent. 
	We presuppose that the worlds are identified by positive integers so that their nominal propositions do not conflict with the actual propositions. 
	As such translating back and forth from a  Kripke model gets us one whose universe of propositions is a strict superset of the original. 
	Still, if we restrict it to the original universe, it is isomorphic to the original Kripke model. 
	Finally we implemented Model Checking for both the Kripke and the Succinct models.

\section{Code}

\subsection{Propositional Logic}

\ignore{
\begin{code}
type Assignment = [Integer]
type Agent = Integer
\end{code}
}

Propositional logic related definitions adapted from the slides.

\begin{code}
type Proposition = Integer
data Form = P Proposition | Neg Form | Conj Form Form | Disj Form Form | Top | Bottom | Knows Agent Form deriving (Eq,Ord)

satisfies :: Assignment -> Form -> Bool
satisfies v (P k)       = k `elem` v
satisfies v (Neg f)     = not (satisfies v f)
satisfies v (Conj f g)  = satisfies v f && satisfies v g
satisfies v (Disj f g)  = satisfies v f || satisfies v g
satisfies _ Top         = True
satisfies _ Bottom      = False
satisfies _ (Knows _ _) = False
\end{code}

Function \texttt{makeBeta} that given $AP_M, AP_W$ and the valuations of all worlds, computes $\beta_M$ which we use to discard valuations that do not correspond to any possible world.

\begin{code}
makeBeta :: [Proposition] -> [Proposition] -> [(World, Valuation)] -> Form
makeBeta ap_M ap_W = makeBeta2 ap_M ap_W ap_W

makeBeta2 :: [Proposition] -> [Proposition] -> [Proposition] -> [(World, Valuation)] -> Form
makeBeta2 _ _  ap_W [] = uExists ap_W
makeBeta2 _ [] ap_W _  = uExists ap_W
makeBeta2 ap_M (prop_w:restProps) ap_W (val:valuations) = Conj (Disj (Neg (P prop_w)) (desc ap_M (snd val))) (makeBeta2 ap_M restProps ap_W valuations)
\end{code}

\begin{itemize}
  \item \texttt{uExists} constructs the formula that corresponds to the exclusive existential $!\exists$. $ap$ is the list of all propositions.
  \item \texttt{possibleWorld} is the conjunction of implications from nominal propositions to the descriptions of the world that they denote. So that if some $p_w$ is true for an interpretation $I$, then if $I$ is to satisfy the conjunct, it must also satisfy $V(w)$

\end{itemize}



\begin{code}
uExists :: [Proposition] -> Form
uExists ap = uExists2 [(x, remove x ap) | x <- ap]

uExists2 :: [(Proposition, [Proposition])] -> Form
uExists2 [] = Bottom
uExists2 ((active_prop, inactive_props):rest) = 
    Disj (possibleWorld active_prop inactive_props) (uExists2 rest)

possibleWorld :: Proposition -> [Proposition] -> Form
possibleWorld active_prop
  = foldr (Conj . Neg . P) (P active_prop)
\end{code}

The description \texttt{desc} of a valuation $V$ is the conjunction of the propositions true in $V$ along with the negations of those not true in $V$.

\begin{code}
desc :: [Proposition] -> [Proposition] -> Form
desc ap props = desc2 (nub ap \\ props) props

desc2 :: [Proposition] -> [Proposition] -> Form
desc2 out_props (in_prop:in_props) = Conj (P in_prop) (desc2 out_props in_props)
desc2 (out_prop:out_props) []      = Conj (Neg (P out_prop)) (desc2 out_props [])
desc2 [] []                        = Top
\end{code}

\ignore{
\begin{code}
allAssignmentsFor :: [Integer] -> [Assignment]
allAssignmentsFor []     = [ [] ]
allAssignmentsFor (p:ps) =
  [ p:rest | rest <- allAssignmentsFor ps ]
  ++ allAssignmentsFor ps
\end{code}
}

\subsection{Our implementation of the Mental Program.}
 Note that the \texttt{UniversalProgram} can reach any world from any world while the \texttt{IdleProgram} cannot reach anything. 
The universal program is meant to replace the \texttt{set} program as it appears on the paper. 
This optimization makes sense since the universal program when restricted to assignments over $ap$ equals the set program.

\begin{code}
data Program = AssignTo Proposition Form
              | Question Form
              | Semicolon Program Program
              | Cap Program Program
              | Cup Program Program
              | IdleProgram
              | UniversalProgram
              deriving (Eq)
\end{code}

\ignore{
\begin{code}
remove :: Eq a => a -> [a] -> [a]
remove element = filter (/=element)
\end{code}
}

The valuation function \texttt{runProgram} for programs follows below. 
The implementation follows closely the definitions in the paper. 
We were forced to optimize the \texttt{Semicolon} program in the case where either of its subprograms is a \texttt{Question}. Ignoring unequal arguments (assignments) to the \texttt{Question} program, which by its very definitions are automatically discarded, shaves off a considerable chunk of runtime. 
Note that in the general case only assignments that satisfy $\beta$ are considered as intermediate assignments.

\begin{code}
runProgram :: Form -> [Proposition] -> Program -> Assignment -> Assignment -> Bool
runProgram _ _ (AssignTo prop formula) a_1 a_2  | satisfies a_1 formula = 
    sort ( nub $ prop:a_1) == sort ( nub a_2)
                                                | otherwise             = 
    sort ( nub (remove prop a_1)) == sort ( nub a_2)
runProgram _ _ (Question formula) a_1 a_2         = 
    (sort ( nub a_1) == sort ( nub a_2)) && satisfies a_1 formula
runProgram beta ap (Semicolon (Question form) pi_2) a_1 a_2 =
    runProgram beta ap (Question form) a_1 a_1 && runProgram beta ap pi_2 a_1 a_2
runProgram beta ap (Semicolon pi_1 (Question form)) a_1 a_2 =
    runProgram beta ap pi_1 a_1 a_2 && runProgram beta ap (Question form) a_2 a_2
runProgram beta ap (Semicolon pi_1 pi_2) a_1 a_2     = 
    not (all (\x -> not (runProgram beta ap pi_1 a_1 x && runProgram beta ap pi_2 x a_2)) [ assignment | assignment <- allAssignmentsFor ap, satisfies assignment beta] )
runProgram beta ap (Cap pi_1 pi_2) a_1 a_2           = 
    runProgram beta ap pi_1 a_1 a_2 && runProgram beta ap pi_2 a_1 a_2
runProgram beta ap (Cup pi_1 pi_2) a_1 a_2           = 
    runProgram beta ap pi_1 a_1 a_2 || runProgram beta ap pi_2 a_1 a_2
runProgram _ _ IdleProgram _ _                    = False
runProgram _ _ UniversalProgram _ _               = True
\end{code}




\subsection{Succinct Epistemic Model}
\texttt{SuccEpistM} is our representation of a Succinct Epistemic Model and consists of a list of propositions $AP_M$, $\beta_M$ and a program for each agent $\pi_a$. 
\begin{code}
data SuccEpistM = Mo
       [Proposition]
       Form
       [(Agent, Program)]
       deriving (Eq)
\end{code}

Our implementation of model checking Succinct Epistemic Models, \texttt{modelCheck}. 
For the case of the knowledge operator we consider all assignments that correspond to a valid world of the original Kripke model (satisfy $\beta$). In the case of the knowledge operator, if there is no program for some agent then that agent vacuously knows everything. That's why when we \texttt{lookup} that agent in the program list and the lookup returns \texttt{Nothing}, we return \texttt{True}.
\begin{code}
modelCheck :: SuccEpistM -> Assignment -> Form -> Bool
modelCheck _ world (P k)            = k `elem` world
modelCheck model world (Neg f)          = 
    not (modelCheck model world f)
modelCheck model world (Conj f g)       = 
    modelCheck model world f && modelCheck model world g
modelCheck model world (Disj f g)       = 
    modelCheck model world f || modelCheck model world g
modelCheck (Mo ap beta programs) world (Knows agent f) = 
    case lookup agent programs of
         Just program_a -> all (\x -> not (runProgram beta ap program_a world  x)
                  || modelCheck (Mo ap beta programs) x f ) [ assignment | assignment <- allAssignmentsFor ap, satisfies assignment beta]
         Nothing -> True
modelCheck _ _ Top                      = True
modelCheck _ _ Bottom                   = False
\end{code}

A different interface \texttt{modelCheck2} takes as its second argument the actual world number instead of its corresponding assignment, like \texttt{modelCheck} does. This is meant to be more user friendly.
\begin{code}
modelCheck2 :: SuccEpistM -> World -> Form -> Bool
modelCheck2 (Mo props beta programs) world = 
    modelCheck (Mo props beta programs) assignment
    where assignment = head $ filter (\x -> -world `elem` x) [ assignment2 | assignment2 <- allAssignmentsFor props, satisfies assignment2 beta]
\end{code}
\pagebreak
\subsection{Kripke Model}

The Kripke Epistemic Model is represented by \texttt{KripkeM}. The internal representation of relations consists of a list of tuples of which the first element is a world and the second a list of its neighbors. 
A wrapping function \texttt{relationWrap}, that translates the more common 2-tuple list, relations to this representation is also provided. 
\begin{code}
data KripkeM = KMo 
       [(Agent, Relation)]
       [(World, Valuation)]
       deriving (Eq,Show)

type World = Integer
type Valuation = [Proposition]
type Relation = [(World, [World])]
\end{code}

We will be using the \texttt{dropWorlds} function to restrict attention to submodels. 
Its input is some Kripke Epistemic Model and a list of worlds to be disregarded.
\begin{code}
dropWorlds :: KripkeM -> [World] -> KripkeM
dropWorlds (KMo agentRelations worldValuations) worldsToDrop = 
    KMo
    [(agent, [(a,[b | b <- neighbors, b `notElem` worldsToDrop]) | (a,neighbors) <- relation, a `notElem` worldsToDrop]) | (agent, relation) <- agentRelations]
    [(world, valuation) | (world, valuation) <- worldValuations, world `notElem` worldsToDrop]
\end{code}

The Kripke Model Checking function \texttt{modelCheckKrpk}.
\begin{code}
modelCheckKrpk :: KripkeM -> World -> Form -> Bool
modelCheckKrpk (KMo _ valuations) world (P k) = 
    case lookup world valuations of
      Just valuation -> k `elem` valuation
      Nothing -> False
modelCheckKrpk model world (Neg f)          = 
    not (modelCheckKrpk model world f)
modelCheckKrpk model world (Conj f g)       = 
    modelCheckKrpk model world f && modelCheckKrpk model world g
modelCheckKrpk model world (Disj f g)       = 
    modelCheckKrpk model world f || modelCheckKrpk model world g
modelCheckKrpk (KMo relations valuations) world (Knows agent f) =
    case lookup agent relations of
         Just relation_a -> case lookup world relation_a of
            Just neighbors -> all (\x -> modelCheckKrpk (KMo relations valuations) x f ) neighbors
            Nothing -> True
         Nothing -> True
modelCheckKrpk _ _ Top                      = True
modelCheckKrpk _ _ Bottom                   = False
\end{code}

\texttt{kripkeToSuccinct} translates Kripke Epistemic Models to Succinct ones. 
Note that for each world the nominal proposition is given by negating the number representing the original world.
\begin{code}
kripkeToSuccinct :: KripkeM -> SuccEpistM
kripkeToSuccinct (KMo relations valuations) = 
    Mo ap beta programs
     where ap = sort (ap_M ++ ap_W)
           beta = makeBeta ap_M ap_W valuations
           programs = [(agent, relationToProgram1 relation) | (agent, relation) <- relations]
           ap_M = nub $ concat [snd x | x <- valuations]
           ap_W = [-(fst x) | x <- valuations]
\end{code}

\subsection{Model Translation Algorithms}

\texttt{succinctToKripke} translates Succinct Epistemic models to Kripke ones.
\begin{code}
succinctToKripke :: SuccEpistM -> KripkeM
succinctToKripke (Mo ap beta programs) = 
    KMo relations worldsAndAssignments
    where relations = [(agent, programToRelation program ap beta worldsAndAssignments) | (agent, program) <- programs]
          worldsAndAssignments = zip [1..(toInteger $ length assignments)] assignments
          assignments = [ assignment | assignment <- allAssignmentsFor ap, satisfies assignment beta]
\end{code}

\texttt{succinctToKripke2} is similar to the above with the added caveat that each assignment is interpreted as the world it represented in the original Kripke Model. This works under the guarantee that the Succinct model to be translated was constructed using \texttt{kripkeToSuccinct} and, as such, we have access to nominal propositions which are negatives of the original worlds. 
Therefore successive use of \texttt{KripkeToSuccinct} and \texttt{succinctToKripke2} on a Kripke Model $M$ nets the model $M$ itself (plus the nominal propositions).
\begin{code}
succinctToKripke2 :: SuccEpistM -> KripkeM
succinctToKripke2 (Mo ap beta programs) = 
    KMo relations worldsAndAssignments
    where relations = [(agent, programToRelation program ap beta worldsAndAssignments) | (agent, program) <- programs]
          worldsAndAssignments = [(negate $ minimum a, a) | a <- assignments]
          assignments = [ assignment | assignment <- allAssignmentsFor ap, satisfies assignment beta]
\end{code}

As the name suggets, \texttt{programToRelation} translates mental programs to relations of the neighbor representation. 
It is a recursive helper function of \texttt{succinctToKripke}.
\begin{code}
programToRelation :: Program -> [Proposition] -> Form -> [(World, Assignment)] -> Relation
programToRelation program ap beta worldsAndAssignments = programToRelation1 program ap beta worldsAndAssignments worldsAndAssignments

programToRelation1 :: Program -> [Proposition] -> Form -> [(World, Assignment)] -> [(World, Assignment)] -> Relation
programToRelation1 _ _ _ [] _ = []
programToRelation1 program ap beta ((world,assignment):rest) worldsAndAssignments = 
        (world, [vorld | (vorld, ass1) <- worldsAndAssignments, runProgram beta ap program assignment ass1]): programToRelation1 program ap beta rest worldsAndAssignments
\end{code}

\texttt{relationToProgram1} is the inverse of \texttt{programToRelation}.
\begin{code}
relationToProgram1 :: Relation -> Program
relationToProgram1 [] = IdleProgram
relationToProgram1 ((world, neighbors):rest) = 
   Cup (relationToProgram2 world neighbors) (relationToProgram1 rest)

relationToProgram2 :: World -> [World] -> Program
relationToProgram2 _ [] = IdleProgram
relationToProgram2 w_1 (w_2:rest) = 
    Cup ( Semicolon (Semicolon (Question (P (-w_1)) ) UniversalProgram) (Question (P (-w_2))) ) (relationToProgram2 w_1 rest)
\end{code}

As we mentioned earlier, \texttt{relationWrap} can be used to translate relations of the usual list of pairs representation to the neighbor representation used internally by our Kripke Models.
\begin{code}
relationWrap :: [(World, World)] -> [(World,[World])]
relationWrap relation = map (\x -> (x,nub [b |(a,b) <- relation, a == x])) worlds
                        where worlds = nub [a | (a,_) <- relation]
\end{code}

\ignore{
\begin{code}
reflexize :: [(World, World)] -> [(World, World)]
reflexize relation = zip worlds worlds ++ relation
                     where worlds = nub [a | (a,_) <- relation]

symmetrize :: [(World, World)] -> [(World, World)]
symmetrize relation = [(a,b) | (b,a) <- relation] ++ relation                       
\end{code}
}

\section{Model Checking Examples}
In this section we provide examples of Model Checking on Succinct Epistemic Models of puzzles taken from the Stanford Encyclopedia of Philosophy \cite{sep-dynamic-epistemic}.

\subsection{Cheryl's Birthday}

Let's have a look at Cheryl's Birthday Puzzle. We encode the initial arrangement given by Cheryl to Albert (1) and Bernard (2) as the following Kripke Model.
\begin{center}
\begin{tikzpicture}[scale=0.2]
\tikzstyle{every node}+=[inner sep=0pt]
\draw [black] (19,-13.4) circle (3);
\draw (19,-13.4) node {$515$};
\draw [black] (36.2,-6.2) circle (3);
\draw (36.2,-6.2) node {$516$};
\draw [black] (75.6,-13.4) circle (3);
\draw (75.6,-13.4) node {$519$};
\draw [black] (36.2,-28.7) circle (3);
\draw (36.2,-28.7) node {$716$};
\draw [black] (6.3,-28.7) circle (3);
\draw (6.3,-28.7) node {$714$};
\draw [black] (6.3,-42.8) circle (3);
\draw (6.3,-42.8) node {$814$};
\draw [black] (19,-37.1) circle (3);
\draw (19,-37.1) node {$815$};
\draw [black] (49.1,-42.8) circle (3);
\draw (49.1,-42.8) node {$817$};
\draw [black] (49.1,-20.9) circle (3);
\draw (49.1,-20.9) node {$617$};
\draw [black] (64,-20.9) circle (3);
\draw (64,-20.9) node {$618$};
\draw [black] (19,-16.4) -- (19,-34.1);
\fill [black] (19,-34.1) -- (19.5,-33.3) -- (18.5,-33.3);
\draw (18.5,-25.25) node [left] {$2$};
\draw [black] (19,-34.1) -- (19,-16.4);
\fill [black] (19,-16.4) -- (18.5,-17.2) -- (19.5,-17.2);
\draw [black] (9.3,-28.7) -- (33.2,-28.7);
\fill [black] (33.2,-28.7) -- (32.4,-28.2) -- (32.4,-29.2);
\draw (21.25,-29.2) node [below] {$1$};
\draw [black] (33.2,-28.7) -- (9.3,-28.7);
\fill [black] (9.3,-28.7) -- (10.1,-29.2) -- (10.1,-28.2);
\draw [black] (9.04,-41.57) -- (16.26,-38.33);
\fill [black] (16.26,-38.33) -- (15.33,-38.2) -- (15.74,-39.11);
\draw (13.63,-40.46) node [below] {$1$};
\draw [black] (16.26,-38.33) -- (9.04,-41.57);
\fill [black] (9.04,-41.57) -- (9.97,-41.7) -- (9.56,-40.79);
\draw [black] (6.3,-39.8) -- (6.3,-31.7);
\fill [black] (6.3,-31.7) -- (5.8,-32.5) -- (6.8,-32.5);
\draw (6.8,-35.75) node [right] {$2$};
\draw [black] (6.3,-31.7) -- (6.3,-39.8);
\fill [black] (6.3,-39.8) -- (6.8,-39) -- (5.8,-39);
\draw [black] (52.1,-20.9) -- (61,-20.9);
\fill [black] (61,-20.9) -- (60.2,-20.4) -- (60.2,-21.4);
\draw (56.55,-21.4) node [below] {$1$};
\draw [black] (61,-20.9) -- (52.1,-20.9);
\fill [black] (52.1,-20.9) -- (52.9,-21.4) -- (52.9,-20.4);
\draw [black] (49.1,-23.9) -- (49.1,-39.8);
\fill [black] (49.1,-39.8) -- (49.6,-39) -- (48.6,-39);
\draw (48.6,-31.85) node [left] {$2$};
\draw [black] (49.1,-39.8) -- (49.1,-23.9);
\fill [black] (49.1,-23.9) -- (48.6,-24.7) -- (49.6,-24.7);
\draw [black] (46.15,-42.24) -- (21.95,-37.66);
\fill [black] (21.95,-37.66) -- (22.64,-38.3) -- (22.83,-37.32);
\draw (34.57,-39.36) node [above] {$1$};
\draw [black] (21.95,-37.66) -- (46.15,-42.24);
\fill [black] (46.15,-42.24) -- (45.46,-41.6) -- (45.27,-42.58);
\draw [black] (21.77,-12.24) -- (33.43,-7.36);
\fill [black] (33.43,-7.36) -- (32.5,-7.21) -- (32.89,-8.13);
\draw (28.57,-10.31) node [below] {$1$};
\draw [black] (33.43,-7.36) -- (21.77,-12.24);
\fill [black] (21.77,-12.24) -- (22.7,-12.39) -- (22.31,-11.47);
\draw [black] (39.15,-6.74) -- (72.65,-12.86);
\fill [black] (72.65,-12.86) -- (71.95,-12.23) -- (71.77,-13.21);
\draw (55.4,-10.39) node [below] {$1$};
\draw [black] (72.65,-12.86) -- (39.15,-6.74);
\fill [black] (39.15,-6.74) -- (39.85,-7.37) -- (40.03,-6.39);
\draw [black] (22,-13.4) -- (72.6,-13.4);
\fill [black] (72.6,-13.4) -- (71.8,-12.9) -- (71.8,-13.9);
\draw (47.3,-13.9) node [below] {$1$};
\draw [black] (72.6,-13.4) -- (22,-13.4);
\fill [black] (22,-13.4) -- (22.8,-13.9) -- (22.8,-12.9);
\draw [black] (9.3,-42.8) -- (46.1,-42.8);
\fill [black] (46.1,-42.8) -- (45.3,-42.3) -- (45.3,-43.3);
\draw (27.7,-43.3) node [below] {$1$};
\draw [black] (46.1,-42.8) -- (9.3,-42.8);
\fill [black] (9.3,-42.8) -- (10.1,-43.3) -- (10.1,-42.3);
\draw [black] (36.2,-9.2) -- (36.2,-25.7);
\fill [black] (36.2,-25.7) -- (36.7,-24.9) -- (35.7,-24.9);
\draw (35.7,-17.45) node [left] {$2$};
\draw [black] (36.2,-25.7) -- (36.2,-9.2);
\fill [black] (36.2,-9.2) -- (35.7,-10) -- (36.7,-10);
\end{tikzpicture}
\end{center}
The reflexive edges on each world are hidden towards a clearer picture.
\begin{code}
birthdayModel :: KripkeM
birthdayModel = KMo
                [(1, relationWrap $ nub $ reflexize $ symmetrize [(515, 516), (515,519), (516,519), (714,716), (617,618), (814,815), (815,817), (814,817)]),
                 (2, relationWrap $ nub $ reflexize $ symmetrize [(714,814), (515,815), (516,716), (617,817), (519,519), (618,618)])]
                (zip worlds [[a] | a <- worlds])
                where worlds = [515,516,519,714,716,617,618,814,815,817]
\end{code}
Each world corresponds to a date with the first digit being the month and the following two the day of the month. 
The valuation of each world contains only one nominal proposition. 
Worlds corresponding to dates that some agent is not able to discern, e.g. two dates in May for Albert are paired in that agent's relation.

The function \texttt{knowsDate} takes as input an agent and generates a proposition that states that the given agent knows the date.
\begin{code}
knowsDate :: Agent -> Form
knowsDate agent = foldr (\x y -> Disj y $ Knows agent $ P x) Bottom [515,516,519,714,716,617,618,814,815,817]
\end{code}

As the puzzle prescribes, Albert starts by publicly announcing that he knows that Bernard does not know the date of Cheryl's birthday. 
This is evaluated as true in worlds 714, 716, 814, 815, 817.
\begin{showCode}
all (\world -> modelCheck2 (kripkeToSuccinct birthdayModel)  world $ Knows 1 $ Neg $ knowsDate 2 ) [714,716,814,815,817]
True
\end{showCode}
and false in the others
\begin{showCode}
not $ all (\world -> modelCheck2 (kripkeToSuccinct birthdayModel)  world $ Neg $ Knows 1 $ Neg $ knowsDate 2 ) [515,516,519,617,618]
False
\end{showCode}
Note that the above computations take considerable time to execute. In the following steps where we deal with a submodel of \texttt{birthdayModel} after dropping some worlds, execution times drop dramatically.\\
Bernard taking into account the public announcement just now, restricts his attention to the worlds for which the above statement holds. 
He then publicly announces that he now knows the date. 
Turns out this can be the case only in 716, 815 and 817.
\begin{showCode}
all (\world -> modelCheck2 (kripkeToSuccinct $ dropWorlds birthdayModel [515,516,519,617,618])  world $ knowsDate 2 ) [716,815,817]
True
\end{showCode}
While it fails on 714 and 814.
\begin{showCode}
not $ all (\world -> modelCheck2 (kripkeToSuccinct $ dropWorlds birthdayModel [515,516,519,617,618])  world $ Neg $ knowsDate 2 ) [714,814]
False
\end{showCode}
Finally Albert states that he does know the date too. 
This holds true only on 716.
\begin{showCode}
all (\world -> modelCheck2 (kripkeToSuccinct $ dropWorlds birthdayModel [515,516,519,617,618,714,814])  world $ knowsDate 1 ) [716]
True

not $ all (\world -> modelCheck2 (kripkeToSuccinct $ dropWorlds birthdayModel [515,516,519,617,618,714,814])  world $ Neg $ knowsDate 1 ) [815,817]
False
\end{showCode}
Therefore Cheryl's birthday is on the 16th of July.
\pagebreak
\subsection{Muddy Children}



Below is the initial arrangement of 3 muddy children with all possible combinations of muddy (1) and not muddy (0).
\begin{center}
\begin{tikzpicture}[scale=0.2]
\tikzstyle{every node}+=[inner sep=0pt]
\draw [black] (29.1,-8.5) circle (3);
\draw (29.1,-8.5) node {$1:010$};
\draw [black] (57,-8.5) circle (3);
\draw (57,-8.5) node {$2:110$};
\draw [black] (29.1,-33.6) circle (3);
\draw (29.1,-33.6) node {$5:000$};
\draw [black] (57,-33.6) circle (3);
\draw (57,-33.6) node {$6:100$};
\draw [black] (18.6,-48.7) circle (3);
\draw (18.6,-48.7) node {$8:001$};
\draw [black] (18.6,-20.5) circle (3);
\draw (18.6,-20.5) node {$3:011$};
\draw [black] (47.2,-20.5) circle (3);
\draw (47.2,-20.5) node {$4:111$};
\draw [black] (47.2,-48.7) circle (3);
\draw (47.2,-48.7) node {$7:101$};
\draw [black] (57,-11.5) -- (57,-30.6);
\fill [black] (57,-30.6) -- (57.5,-29.8) -- (56.5,-29.8);
\draw (56.5,-21.05) node [left] {$2$};
\draw [black] (57,-30.6) -- (57,-11.5);
\fill [black] (57,-11.5) -- (56.5,-12.3) -- (57.5,-12.3);
\draw [black] (32.1,-8.5) -- (54,-8.5);
\fill [black] (54,-8.5) -- (53.2,-8) -- (53.2,-9);
\draw (43.05,-9) node [below] {$1$};
\draw [black] (54,-8.5) -- (32.1,-8.5);
\fill [black] (32.1,-8.5) -- (32.9,-9) -- (32.9,-8);
\draw [black] (32.1,-33.6) -- (54,-33.6);
\fill [black] (54,-33.6) -- (53.2,-33.1) -- (53.2,-34.1);
\draw (43.05,-33.1) node [above] {$1$};
\draw [black] (54,-33.6) -- (32.1,-33.6);
\fill [black] (32.1,-33.6) -- (32.9,-34.1) -- (32.9,-33.1);
\draw [black] (29.1,-30.6) -- (29.1,-11.5);
\fill [black] (29.1,-11.5) -- (28.6,-12.3) -- (29.6,-12.3);
\draw (28.6,-21.05) node [left] {$2$};
\draw [black] (29.1,-11.5) -- (29.1,-30.6);
\fill [black] (29.1,-30.6) -- (29.6,-29.8) -- (28.6,-29.8);
\draw [black] (21.6,-48.7) -- (44.2,-48.7);
\fill [black] (44.2,-48.7) -- (43.4,-48.2) -- (43.4,-49.2);
\draw (32.9,-48.2) node [above] {$1$};
\draw [black] (44.2,-48.7) -- (21.6,-48.7);
\fill [black] (21.6,-48.7) -- (22.4,-49.2) -- (22.4,-48.2);
\draw [black] (18.6,-45.7) -- (18.6,-23.5);
\fill [black] (18.6,-23.5) -- (18.1,-24.3) -- (19.1,-24.3);
\draw (19.1,-34.6) node [right] {$2$};
\draw [black] (18.6,-23.5) -- (18.6,-45.7);
\fill [black] (18.6,-45.7) -- (19.1,-44.9) -- (18.1,-44.9);
\draw [black] (47.2,-45.7) -- (47.2,-23.5);
\fill [black] (47.2,-23.5) -- (46.7,-24.3) -- (47.7,-24.3);
\draw (46.7,-34.6) node [left] {$2$};
\draw [black] (47.2,-23.5) -- (47.2,-45.7);
\fill [black] (47.2,-45.7) -- (47.7,-44.9) -- (46.7,-44.9);
\draw [black] (44.2,-20.5) -- (21.6,-20.5);
\fill [black] (21.6,-20.5) -- (22.4,-21) -- (22.4,-20);
\draw (32.9,-20) node [above] {$1$};
\draw [black] (21.6,-20.5) -- (44.2,-20.5);
\fill [black] (44.2,-20.5) -- (43.4,-20) -- (43.4,-21);
\draw [black] (20.58,-18.24) -- (27.12,-10.76);
\fill [black] (27.12,-10.76) -- (26.22,-11.03) -- (26.97,-11.69);
\draw (24.39,-15.95) node [right] {$3$};
\draw [black] (27.12,-10.76) -- (20.58,-18.24);
\fill [black] (20.58,-18.24) -- (21.48,-17.97) -- (20.73,-17.31);
\draw [black] (55.1,-10.82) -- (49.1,-18.18);
\fill [black] (49.1,-18.18) -- (49.99,-17.87) -- (49.22,-17.24);
\draw (52.66,-15.93) node [right] {$3$};
\draw [black] (49.1,-18.18) -- (55.1,-10.82);
\fill [black] (55.1,-10.82) -- (54.21,-11.13) -- (54.98,-11.76);
\draw [black] (27.39,-36.06) -- (20.31,-46.24);
\fill [black] (20.31,-46.24) -- (21.18,-45.87) -- (20.36,-45.29);
\draw (24.45,-42.51) node [right] {$3$};
\draw [black] (48.83,-46.18) -- (55.37,-36.12);
\fill [black] (55.37,-36.12) -- (54.51,-36.52) -- (55.35,-37.06);
\draw (51.48,-39.83) node [left] {$3$};
\draw [black] (55.37,-36.12) -- (48.83,-46.18);
\fill [black] (48.83,-46.18) -- (49.69,-45.78) -- (48.85,-45.24);
\end{tikzpicture}
\end{center}
The reflexive edges on each world are hidden towards a clearer picture.\\
\begin{code}
mdModel :: KripkeM
mdModel = KMo
            [(1, relationWrap $ nub $ reflexize $ symmetrize [(1,2), (3,4), (5,6), (8,7)]),
             (2, relationWrap $ nub $ reflexize $ symmetrize [(1,5), (2,6), (3,8), (4,7)]),
             (3, relationWrap $ nub $ reflexize $ symmetrize [(1,3), (2,4), (5,8), (6,7)])]
            [(1,[2]), (2,[1,2]), (3,[2,3]), (4,[1,2,3]), (5, []), (6,[1]), (7, [1,3]), (8,[3])]
\end{code}

At first the father announces that there is at least one muddy child. 
This means that world 5 is to be dropped. 
The next public announcement amounts to no child knowing whether their forehead is muddy. 
This is true on worlds 2, 3, 4 and 7.
\begin{showCode}
all (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5] )   (fst x) $ Neg (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [2,3,4,7], y <- [1,2,3]]
True

all (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5] )   (fst x) $ Neg (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [1], y <- [1,2,3]]
False

all (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5] )   (fst x) $ Neg (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [6], y <- [1,2,3]]
False

all (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5] )   (fst x) $ Neg (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [8], y <- [1,2,3]]
False
\end{showCode}
\pagebreak
We can then drop worlds 1, 6 and 8. 
The next announcement conveys that there is a child that now knows their forehead to be dirty. 
\begin{showCode}
any (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5,1,6,8] )   (fst x) (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [2], y <- [1,2,3]]
True

any (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5,1,6,8] )   (fst x) (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [3], y <- [1,2,3]]
True

any (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5,1,6,8] )   (fst x) (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [7], y <- [1,2,3]]
True

any (\x -> modelCheck2 (kripkeToSuccinct $ dropWorlds mdModel [5,1,6,8] )   (fst x) (Knows (snd x)  (P (snd x))) ) [(x,y) | x <- [4], y <- [1,2,3]]
False
\end{showCode}
Looking at the valuations of worlds 2, 3 and 7 it becomes clear that there are exactly two muddy children in any case.

\section{Translating to and back from a Succinct Model}

Using \texttt{kripkeToSuccinct} to translate some Kripke model $M$ to a Succinct model $N$ and then \texttt{succinctToKripke2} on $N$ gives us back $M$. 
Note that the final result contains the nominal propositions which were not present in the original $M$. 
Below are example executions on the Muddy children and Cheryl's birthday Kripke models.
\begin{showCode}
succinctToKripke2 $ kripkeToSuccinct  mdModel
KMo [(1,[(8,[8,7]),(7,[8,7]),(6,[6,5]),(5,[6,5]),(4,[4,3]),(3,[4,3]),(2,[2,1]),(1,[2,1])]),(2,[(8,[8,3]),(7,[7,4]),(6,[6,2]),(5,[5,1]),(4,[7,4]),(3,[8,3]),(2,[6,2]),(1,[5,1])]),(3,[(8,[8,5]),(7,[7,6]),(6,[7,6]),(5,[8,5]),(4,[4,2]),(3,[3,1]),(2,[4,2]),(1,[3,1])])] [(8,[-8,3]),(7,[-7,1,3]),(6,[-6,1]),(5,[-5]),(4,[-4,1,2,3]),(3,[-3,2,3]),(2,[-2,1,2]),(1,[-1,2])]

succinctToKripke2 $ kripkeToSuccinct birthdayModel
KMo [(1,[(817,[817,815,814]),(815,[817,815,814]),(814,[817,815,814]),(716,[716,714]),(714,[716,714]),(618,[618,617]),(617,[618,617]),(519,[519,516,515]),(516,[519,516,515]),(515,[519,516,515])]),(2,[(817,[817,617]),(815,[815,515]),(814,[814,714]),(716,[716,516]),(714,[814,714]),(618,[618]),(617,[817,617]),(519,[519]),(516,[716,516]),(515,[815,515])])] [(817,[-817,817]),(815,[-815,815]),(814,[-814,814]),(716,[-716,716]),(714,[-714,714]),(618,[-618,618]),(617,[-617,617]),(519,[-519,519]),(516,[-516,516]),(515,[-515,515])]
\end{showCode}
If we disregard the nominal propositions, these are identical to the original models.

\section{Conclusion}
The model checking on the examples of the previous sections gives the expected results. Therefore, our implementation of the translation from Kripke to Succinct and our model checking algorithm for succinct models is likely to be correct.

Translating a Kripke to Succinct and then back to Kripke gives us the original model plus the nominal propositions so our claim that we get an isomorphic model holds. 

\section{Further work}
A natural extension would be the implementation of the Succinct Event Model, the Product Update and the model checking algorithm thereof. To that end, the current design with the nominal propositions being negations of the world numbers should be swapped for a more robust one, which does not depend on the sign of the integers. 
This is because the current approach would not generalize well if we had to apply successive product updates.

\addcontentsline{toc}{section}{References}
\printbibliography

\end{document}