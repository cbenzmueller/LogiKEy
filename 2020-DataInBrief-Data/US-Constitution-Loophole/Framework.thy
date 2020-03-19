(*<*)
theory Framework
imports Main
begin
(*>*)

section\<open>{On the framework used \label{sec:Framework}}\<close>

text\<open>\noindent %
To start off, we shall give an overview on the framework this thesis was written in, that is,
enlist the relevant software components used and explain the core features of Isabelle/HOL since it is the most important component. \<close>
             
subsection\<open>{The components \label{subsec:Components}}\<close>
text\<open>
There are three main tools used to write this thesis:
\begin{description}
\item [Isabelle/HOL] A proof assistant that provides an environment to axiomatize and utilize deduction systems with which one can formulate 
theorems and prove them. It was used to represent the Constitution's model on the computer and conduct reasoning with it.
\item [\LaTeX] A typesetting software. It is very convenient for mathematical formulas. Isabelle has an inbuilt tool to use \LaTeX. This was used
to typeset the code written with Isabelle.
\item [Git] Version control software to keep track of changes and return to older versions where necessary. 
\end{description}
\<close>


subsection\<open>{Short introduction to Isabelle/HOL \label{subsec:Isabelle}}\<close>

text\<open>\noindent %
 Depending on the context, the way Isabelle is used can vary greatly. The following shall illustrate how we will be using it%
\footnote{For a general introduction see the manual \cite{isabelle-reference}}.
First we give an outline of the steps taken and then illustrate those with examples.

\noindent Here is the outline:
\begin{enumerate}
\item Provide definitions of types, concepts, operators used.
\item State all assumptions in the form of axioms.
\item State theorems.
\item Test your theory by trying to refute/prove the theorems. Use tools Sledgehammer and Nitpick%
\footnote{See also the manuals on Sledgehammer \cite{isabelle-sledgehammer} and on Nitpick \cite{isabelle-nitpick}} to do so.
\end{enumerate}
\<close>

text\<open>\noindent %
 \textbf{ 1. Provide definitions of types, concepts, operators used.}

\noindent We can define our own data types or work with predefined ones. Here we introduce a data type @{text "bvg"} (\emph{beverage}) and a type
@{text "temp"} (\emph{temperature}). The latter is just a synonym for predefined type @{text "int"}.
\<close>
datatype bvg = tea | coffee | juice
type_synonym temp="int"

text\<open>\noindent %
 Next we define predicates and operators.\<close>

consts tempOf::"bvg\<Rightarrow>temp"     
  \<comment> \<open>determines temperature of bvg\<close>

definition totalTemp::"temp"
  where "totalTemp \<equiv> (tempOf tea) + (tempOf coffee) + (tempOf juice)"
  \<comment> \<open>determines total temperature of all bvg-instances\<close>

definition tooHot::"bvg\<Rightarrow>bool"
  where "tooHot b \<equiv> if(b=juice)then(tempOf b > 5) else (tempOf b > 20)" 
  \<comment> \<open>determines if a beverage is too hot. For @{text "juice"} this is the case iff its temperature is @{text ">5"}, for @{text "tea"} 
and @{text "coffee"} iff the temperature is @{text ">20"}\<close>

text\<open>\noindent %
 \textbf{2. State all assumptions in the form of axioms.}

\noindent Note that we introduce a contradiction with the two axioms @{text "teaHot tea"} and @{text "tempOf tea = 10"}
\<close>

axiomatization where
teaHot:     "tooHot tea"         and
teaTemp10:  "(tempOf tea)=10"    and
coffeeTemp5:"(tempOf coffee)=5"  and
juiceTemp2: "(tempOf juice)=2"


text\<open>\noindent %
 \textbf{3. State theorems and 4. Test your theory by trying to refute/prove the theorems.}

\noindent These steps have to be conducted together since Isabelle requires theorems to be proven. It is not possible
to enumerate theorems without proofs unless you use keyword @{command "oops"} to signify that a theorem has not been proven yet.\\

\noindent \emph{Sledgehammer} can be used to find proofs and \emph{Nitpick} to find counter models and satisfying models.
\<close>

theorem totalTemp17:"totalTemp = 17" sledgehammer
  by (simp add: coffeeTemp5 juiceTemp2 teaTemp10 totalTemp_def)

lemma basic_unsat:"False" using teaHot teaTemp10 tooHot_def sledgehammer 
  by simp

lemma basic_sat:"True" nitpick[show_all,user_axioms] oops

text\<open>\noindent %
Note that our axioms are inconsistent, so we can prove @{text "basic_unsat"}. Nitpick can neither find a counter model nor a satisfying one.
However, if we remove axiom @{text "teaHot"} or @{text "teaTemp10"} lemma @{text "basic_unsat"} becomes unprovable and Nitpick will find a 
satisfying model for lemma @{text "basic_sat"}. To look for a satisfying model rather than a refuting one, we simply add option 
@{text "satifsy"}.
   \<close>

(*<*)
end
(*>*)
