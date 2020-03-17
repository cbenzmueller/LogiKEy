(*<*)
theory NotToDo
imports Main
begin
(*>*)
subsection \<open>{What to avoid when modelling \label{subsec:Avoid}}\<close>

subsubsection\<open>{Data type @{text "time"} as @{text "int"} \label{subsubsec:TimeInt}}\<close>
text\<open>\noindent %
 The initial idea for the Constitution's model was to map everything possible to the computer, including concepts like
\begin{quote}
The House of Representatives shall be [...] chosen every second Year[...].\footnote{See \usc{I}{2}{1}} 
\end{quote}
Isabelle offers a rich theory on \emph{integers}. It thus seemed to be a good idea to work with @{text "int"} as basis
 for data type @{text "time"} defined thus:
\<close>

type_synonym time="int" 

text\<open>\noindent %
 One could then have identified year $n$ with @{text "int"} $n$ and expressed a two-year election cycle the following way:\<close>
(*<*)
typedecl h                 \<comment> \<open>Type for humans\<close>
  typedecl s                 \<comment> \<open>Type for states\<close>
  typedecl g                 \<comment> \<open>Type for government institutions\<close>
  (*type_synonym g = "h set" \<comment> \<open>Type for government institutions\<close>*)
  typedecl r                 \<comment> \<open>Type for rights\<close>
typedecl e                 \<comment> \<open>Type for elections\<close>
type_synonym \<sigma>="time\<Rightarrow>bool"
locale timeInt=
  fixes
 cw :: time and
 E_HoR :: "e" \<comment> \<open>Election for the House of Representatives\<close> and
 T_lastE :: "time\<Rightarrow> \<sigma>"                    \<comment> \<open>last election of kind e was at time\<close>and
 T_nextE :: "time\<Rightarrow> \<sigma>"                    \<comment> \<open>next election of kind e will be at time\<close>
  assumes true:"True"
begin
type_synonym \<sigma>="(time\<Rightarrow>bool)" \<comment> \<open>Type of time dependant formulas - point of time: world in Kripke semantics\<close> 
  type_synonym \<alpha>="(time\<Rightarrow>time\<Rightarrow>bool)" \<comment> \<open>Type of accessibility relations between points of time.\<close>
definition mtop :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv>\<lambda>t. True" 
  definition mbot :: "\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv>\<lambda>t. False" 
  definition mneg :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>t. \<not>\<phi> (t)" 
  definition mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>t. \<phi>(t)\<and>\<psi>(t)"   
  definition mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv>\<lambda>t. \<phi>(t)\<or>\<psi>(t)"   
  definition mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<longrightarrow>"49) where "\<phi>\<^bold>\<longrightarrow>\<psi> \<equiv>\<lambda>t. \<phi>(t)\<longrightarrow>\<psi>(t)"  
  definition mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<longleftrightarrow>"48) where "\<phi>\<^bold>\<longleftrightarrow>\<psi> \<equiv>\<lambda>t. \<phi>(t)\<longleftrightarrow>\<psi>(t)"
  definition meq :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr"\<^bold>="40) where "\<phi>\<^bold>=\<psi> \<equiv>\<lambda>t. \<phi>=\<psi>"
  definition mneq :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr"\<^bold>!="40) where "\<phi>\<^bold>!=\<psi> \<equiv>\<lambda>t.\<not>( \<phi>=\<psi>)"
  definition mgeq :: "int\<Rightarrow>int\<Rightarrow>\<sigma>" (infixr"\<^bold>\<ge>"42) where "t1\<^bold>\<ge>t2 \<equiv>\<lambda>t. (t1\<ge>t2)"
definition mleq :: "int\<Rightarrow>int\<Rightarrow>\<sigma>" (infixr"\<^bold>\<le>"42) where "t1\<^bold>\<le>t2 \<equiv>\<lambda>t. (t1\<ge>t2)"  
definition mall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>t.\<forall>x. \<Phi>(x)(t)" 
  definition mallB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
(**)
  definition mexi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>t.\<exists>x. \<Phi>(x)(t)"
definition mexiB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
definition global_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>t. \<phi> t"
  end

locale timeInt2= timeInt +
assumes(*>*)
elections_2yearCycle:"\<lfloor>\<^bold>\<forall>t.(T_lastE t)\<^bold>\<longrightarrow>(T_nextE (t+2))\<rfloor>" 


text\<open>\noindent %
 where @{text "T_lastE"} and @{text "T_nextE"} are predicates on whether or not the last election was at @{text "t"} and whether
or not the next election
will be at @{text "t+2"} respectively.

Unfortunately working with integers like this renders Isabelle's tools more or less unusable. This is because Isabelle must then
provide a theory to work with integers which makes the tools very slow to respond, 
if they do not run out of time, altogether. Especially Nitpick%
\footnote{S. \cite{isabelle-nitpick}} is not helpful anymore since now it has to provide
infinite models at which it generally fails.

Since neither the rich theory of integers nor an infinite number of time instances were necessary in our case, 
dispensing with command @{text "time=int"} in favour of helpful versions of Nitpick and Sledgehammer%
\footnote{S. \cite{isabelle-sledgehammer}}
 was the appropriate choice.
\<close>

subsubsection\<open>{Functions instead of relations \label{subsubsec:FunRel}}\<close>

text\<open>\noindent %
In order to be able to introduce next operator @{text "\<^bold>X"}, a successor function is necessary that provides exactly one successor for each time instance.
This was done with a \emph{relation} in our model. Given that the mapping of @{text "(succ t)"} to @{text "t"} is unique, one could also consider using 
a function, rather than a relation. This way the definition would be shorter as one wouldn't have to specify whether 
two instances are related or not for each pair of time instances.

\noindent A function and corresponding @{text "\<^bold>X"} could be defined as follows:
\<close>
(*<*)
locale funrel=
  assumes
axi:"True"
begin
datatype time = t\<^sub>1 |t\<^sub>2 |t\<^sub>3 |t\<^sub>e 
type_synonym \<sigma>="time\<Rightarrow>bool"
(*>*)
function succ::"time\<Rightarrow>time"  where
   "succ t\<^sub>1 = t\<^sub>2"
  |"succ t\<^sub>2 = t\<^sub>3"
  |"succ t\<^sub>3 = t\<^sub>e"      
  |"succ t\<^sub>e = t\<^sub>e"
  by pat_completeness auto

definition tnext :: " \<sigma>\<Rightarrow> \<sigma>" ("\<^bold>X_")
  where "\<^bold>X\<phi> \<equiv> (\<lambda>t. \<forall>t'. ((succ(t) = t') \<longrightarrow> \<phi> t'))"
(*<*)
end
(*>*)

text\<open>\noindent %
 Observe that requirement @{text "(succ t t')"} has now been replaced with @{text "succ(t) = t'"}
in the definition of @{text "tnext"}.

Now why is the function not a desirable option? As with @{text "int"} for @{text "time"} the tools grew very slow or not usable at all
when using the function.
Presumably, that is because of the comprehensive theory that comes with functions. Its provision makes Isabelle slow.

Furthermore, the functions themselves are somewhat cumbersome to work with. For example, consider line
@{command "by"} @{method "pat_completeness"} @{method "auto"}. If the domain 
is a recursively defined data type the definition of a function requires a proof that it will terminate. Of course, our data type @{text "time"}
 has not been defined recursively. However, its definition uses the same 
syntax as a recursive data type would. Therefore, a proof of the function's termination on arbitrary elements of the domain is necessary
for the function to be well-defined.

Taking into account that we do not need this theory, we might as well dispense with it.
\<close>


subsubsection\<open>{Numerous type declarations \label{subsubsec:TypeDecl}}\<close>

text\<open>\noindent %
 As mentioned in \ref{subsubsec:TimeInt} the original goal was to represent as many notions of the Constitution as possible.
This meant that distinguishing a fair amount of different types of topics was necessary. The most straightforward way to do this
seemed to be to introduce various data types. See below for an example.
\<close>
(*<*)
locale dTypes = 
assumes 
truth:"True"
begin
(*>*)
typedecl h                 \<comment> \<open>Type for humans\<close>
typedecl s                 \<comment> \<open>Type for states\<close>
typedecl g                 \<comment> \<open>Type for government institutions\<close>
typedecl r                 \<comment> \<open>Type for rights\<close>
typedecl e                 \<comment> \<open>Type for elections\<close>
typedecl time             \<comment> \<open>Type for time\<close>
type_synonym \<sigma>="(time\<Rightarrow>bool)"
(*<*)
end
(*>*)

 text\<open>\noindent %
 Unfortunately, this made the domain for finding (counter-)models a complex field to navigate. While the numerous data types made it easy
to accurately distinguish between different notions and express formulas, the computer did not know about appropriate cardinalities for the
declared data types.

\noindent Take for example the following proposition:

\begin{center}
@{text "\<lfloor>\<^bold>\<forall>h. (h memOf Senate) \<^bold>\<leftrightarrow> "}\\
@{text "((\<^bold>\<exists>el.( el elecFor E_Senate)\<^bold>\<and>(elects el h E_Senate)))\<rfloor>"}
\end{center}

\noindent based on constants \<close>(*<*)

locale varDTypes =
  fixes
(*>*)
Senate :: "g"
(*<*)and(*>*)

E_Senate :: "e"
(*<*)and(*>*)

memOf :: "h \<Rightarrow> g \<Rightarrow> \<sigma>" ("_ memOf _") (*<*)and(*>*)

elecFor :: "h\<Rightarrow>e\<Rightarrow>\<sigma>"  ("_ elecFor _") 
(*<*)and(*>*)

elects :: "h\<Rightarrow>h\<Rightarrow>e\<Rightarrow>\<sigma>" ("elects _ _ _")

text\<open>\noindent %
It is meant to express that senators are elected by electors\footnote{cf. \uscx{XVII}{1}{}}
 or put differently, that a human @{text "h"} is a member of @{text "Senate"}
 iff there is another human
@{text "el"} that is an elector for election of type @{text "E_Senate"} and elects @{text "h"} at that election.

This proposition requires reasoning on data types @{text "g"},@{text "e"},@{text "h"} and @{text "time"} (because of
 @{text "\<sigma>=(time\<Rightarrow>bool)"}).
If no cardinalities are given for the respective types, Nitpick will try to combine all kinds of combinations of cardinalities when looking
for a model. The number of different cardinality combinations grows exponentially with the number of data types rendering Nitpick useless.

A partial solution for this is to introduce finite data types where possible and determine the cardinalites when calling Nitpick, as
it will try to cover all of these combinations with the limited computation time it has. 
See for example:
\<close>

(*<*)
locale finiteDTypes = 
assumes 
truth:"True"
begin
(*>*)
typedecl h                 \<comment> \<open>Type for humans\<close>
typedecl s                 \<comment> \<open>Type for states\<close> 
datatype g =                 \<comment> \<open>Type for government institutions\<close>
             Congress        \<comment> \<open>Congress of the US\<close>
           | HoR             \<comment> \<open>House of Representatives\<close>
           | Senate          \<comment> \<open>Senate\<close>

typedecl r                 \<comment> \<open>Type for rights\<close>
datatype e =                 \<comment> \<open>Type for elections\<close>
             E_HoR           \<comment> \<open>elections for the HoR\<close>
           | E_Senate        \<comment> \<open>elections for the Senate\<close>
typedecl time             \<comment> \<open>Type for time\<close>
type_synonym \<sigma>="(time\<Rightarrow>bool)"
(*<*)
end
(*>*)

text\<open>\noindent %
 with @{text "Nitpick[card g= 3,card e=2]"}.

\noindent The disadvantage here is that introducing finite types is not always possible which means the problem can only be solved partially.

Furthermore, the finite data types reduce flexibility in the modelling or at least require repeated adjustments when they do not suffice
for the currently modelled concepts anymore. This makes their use prone to inconsistencies and errors in general.\<close>


subsubsection\<open>{Polymorphism \label{subsubsec:Polym}}\<close>

text\<open>\noindent %
 A similar problem to the one discussed in \ref{subsubsec:TypeDecl} is the one polymorphism poses.
Take for example the following alternative definition of @{text "memOf"}.
\<close>

(*<*)
locale polymorphism1 =
  fixes
(*>*)
memOf :: "'a\<Rightarrow> 'b \<Rightarrow> \<sigma>" ("_ memOf _")

text\<open>\noindent %
 It is elegant since it would allow for an instance of any type @{text "'a"} to be declared a member of an instance of any type 
@{text"'b"}. It is not necessary to specify types @{text "'a"} and @{text "'b"} upon defining @{text "memOf"}.

As with the unknown cardinalities in \ref{subsubsec:TypeDecl} however, Isabelle's tools need to guess the required specific type.
This means trying all possibilities until a suitable one is found. This takes time and thus makes this theoretically elegant concept
an inconvenient one in practice.

Notice that the problem becomes even more pronounced when working with quantifiers, such as 

\<close>
(*<*)
locale polymorphism2 =
assumes
truth:"True"
begin

definition (*>*)tall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>t.\<forall>x. \<Phi>(x)(t)"  
(*<*)definition tallB:: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>\<phi>. \<Phi>(\<phi>) \<equiv> \<^bold>\<forall>\<Phi>"
end(*>*)

text\<open>\noindent %
In this case Isabelle has to find the right type for @{text "'a"} as well as check for all instances of the presumable type whether @{text "\<Phi>"}
holds true of it.

Incidentally, this is why we introduce operators @{text "\<^bold>\<forall>\<^sub>g"} and @{text "\<^bold>\<forall>\<^sub>\<sigma>"} in \ref{subsec:HOTL}.
Knowing that types @{text "g"} and @{text "\<sigma>"} are the only ones that will be quantified over, it is sensible to introduce these instead of a 
polymorphic version as given above. This spares Isabelle the work
of searching for the right type and thus leads to quicker response times of its tools. Also, it forces us to be precise with our formulas, which in turn 
contributes to cleaner code and a better understanding of the concepts involved.\<close>

subsubsection\<open>{Higher order quantification and the Frame Problem \label{subsubsec:HOQu}}\<close>
text\<open>\noindent %
This section is somewhat more extensive than its predecessors of \ref{subsec:Avoid} since we are going to look into two
different topics.

In the \hyperref[HOQu]{first} part the eponymous higher order quantification will be discussed. The reason there is a second part is that 
the exemplary formulas given are an attempt at solving the so called
 Frame Problem\footnote{S. \cite{sep-frame-problem}}. This Frame Problem is of significance not only to
AI in general, but for finding a good model of our time dependant Constitution in particular and shall therefore be presented as well.
This will be the \hyperref[FrameProblem]{second} part.\\

\phantomsection
\label{HOQu}  
\noindent As mentioned in \ref{subsubsec:t1} it would be convenient to only have to make statements about what changes when transitioning
 from one time instance to the next without mentioning everything that stays the same. This would allow us to introduce amendments and thus make changes 
to the Constitution without having to state explicitly which of the currently valid properties will still be valid.

A possible way to realize this, is by using an axiom that states the following two properties:
\begin{itemize}
\item If @{text "\<phi>"} is valid at @{text "t\<^sub>i"} with successor @{text "t\<^sub>i\<^sub>+\<^sub>1"} and there is no @{text "\<psi>"} contradicting @{text "\<phi>"}, valid
at @{text "t\<^sub>i\<^sub>+\<^sub>1"}, then @{text "\<phi>"} stays valid at @{text "t\<^sub>i\<^sub>+\<^sub>1"}.
\item If @{text "\<phi>"} is valid at @{text "t\<^sub>i"} with successor @{text "t\<^sub>i\<^sub>+\<^sub>1"} and there is a @{text "\<psi>"} contradicting @{text "\<phi>"}, valid
at @{text "t\<^sub>i\<^sub>+\<^sub>1"}, then @{text "\<phi>"} is not valid at @{text "t\<^sub>i\<^sub>+\<^sub>1"}.
\end{itemize}

\noindent With a very rudimentary notion of what it means when ``@{text "\<psi>"} contradicts @{text "\<phi>"}", we could express these
 points as follows:
\<close>

definition isNeg ::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool"
  where "isNeg \<phi> \<psi> \<equiv> \<forall>t. (\<phi> t) \<longleftrightarrow> (\<not>(\<psi> t))"

(*<*)
locale strongAx =
  fixes
 succ::"time\<Rightarrow>time\<Rightarrow>bool"
assumes(*>*)

axiom1: 
"\<forall>\<phi>. \<forall>t2. ((\<exists>t1. (succ t1 t2) \<and> (\<phi> t1)\<and>(\<forall>\<psi>. \<not>((isNeg \<phi> \<psi>) \<and> (\<psi> t2))))\<longrightarrow>(\<phi> t2))"
 and
axiom2: 
"\<forall>\<phi>. \<forall>t2. ((\<exists>t1. (succ t1 t2) \<and> (\<phi> t1)\<and>(\<exists>\<psi>. ((isNeg \<phi> \<psi>) \<and> (\<psi> t2))))\<longrightarrow>\<not>(\<phi> t2))" 

text\<open>\noindent %
Unfortunately, these axioms are not well suited to actually help with modelling the amendment process.

One reason is, of course, that @{text "isNeg"} is a very simple way of checking for contradictions in @{text "\<phi>"} and @{text "\<psi>"}.
It only verifies whether the negation of one evaluates the same way as the other does. This does not take their respective composition
into account. What if @{term "\<psi> \<equiv> \<psi>\<^sub>1 \<and> \<psi>\<^sub>2"} and only @{text "\<psi>\<^sub>2"} contradicted @{text "\<phi>"} or what if @{text "\<phi>"} was a tautology and
 @{text "\<psi>"} inherently contradictory?
While not a trivial task, one could improve @{text "isNeg"} e.g. by analysing @{text "\<phi>"} and @{text "\<psi>"} in a
 recursive manner and comparing their respective components. The check for contradictions shall not be the centre of our attention, however.
Let us instead turn to @{text "axiom1"} and @{text "axiom2"}.

Another reason why these axioms are only marginally helpful, is that they quantify over formulas. This makes them
rather strong axioms which, in theory, should make them very useful, but in practice makes them inconvenient to work with.

The reason is that in order to use them for a proof, Isabelle will have to check the premises of the implications given, including
the verification of
\begin{itemize}
 \item @{term "\<forall>\<psi>. \<not>((isNeg \<phi> \<psi>) \<and> (\<psi> t2))"} and 
 \item @{term "\<exists>\<psi>. ((isNeg \<phi> \<psi>) \<and> (\<psi> t2))"}
\end{itemize}
respectively.
This a very difficult task since the verification of neither of these terms is decidable. \\
For the former to be verified, Isabelle would have to check all possible formulas @{text "\<psi>"} for contradictions to @{text "\<phi>"}
with the number of formulas being infinite.\\
For the latter, potentially infinitely many formulas have to be assessed with termination once a suitable @{text "\<psi>"}
has been found. Hence, checking the second term is at least semi-decidable, but not decidable.

In both cases, reasoning will be very slow since Isabelle will try to check all available candidates for @{text "\<psi>"}.
Since @{text "axiom1"} and @{text "axiom2"} are given as axioms, Isabelle will try to use them whenever
trying to find a proof and in attempting to verify the axioms' left-hand sides run out of computation time. One could, of course, increase
the available computation time for tools such as Sledgehammer but given that the verification is not decidable, this is not likely to help.

Consequently, it is best to avoid axioms like the above. One should note here that higher order quantification per se is not an evil 
to be avoided at all costs. Higher order logic is very expressive and can make it easy to formulate concepts in a very concise manner. 
This is why we have used it throughout the simulation. There are two differences between the above quantification and the ones we have used.

The first is that quantifiers used, almost always occurred at the beginning of a
formula, not as just a component of a bigger formula. So, unless there was reasoning about the entire formula ``@{text "\<forall>\<phi>. \<Phi>(\<phi>)"}",
there was no need to reason about the quantifiers.

The second is that all quantification over formulas, as opposed to quantification over constants, was always time-dependant. So if such 
quantification was used in an axiom, it still wasn't universally valid but only for certain instances of time. This resulted in these axioms
not being used in proofs by default.

All in all, higher order quantification can be very helpful but has to be used adequately.\\

\phantomsection
\label{FrameProblem}
\noindent Let us now turn to the Frame Problem. We shall determine what it is, how it is related to our model and how it is connected
to legal texts in general.

There are different notions of what the Frame Problem is. Its more narrow, technical version originated in logic-based AI and 
was then taken up by philosophers who interpreted it in a more general way and extended the question%
\footnote{S. \cite{sep-frame-problem}-``Introduction"}. We will only be concerned with the former.

The Frame Problem was first presented by McCarthy and Hayes in 1969\footnote{S. \cite{mccarthy1969},``4.3. The Frame Problem"}.
They observed that for any program to successfully interact with its environment, it needed an internal representation of its environment.
This would allow for example a robot to judge whether an action was successful or not.
 Simply stating which actions resulted in which changes of the environment was not enough, however. 
To see why, consider the following example.

\noindent There is a tea cup @{text "cup"} on which the following actions can be performed:
\begin{enumerate}
\item @{text "fill(cup)"}
\item @{text "move(cup,position)"}
\end{enumerate}
You could describe the state of @{text "cup"} by giving information on its position and on whether or not it is full.
Upon conducting an action the parameters of @{text "cup"} are changed as follows:
\begin{enumerate}
\item After @{text "fill(cup)"} the cup is full.
\item After @{text "move(cup,position)"} the cup is at @{text "position"}.
\end{enumerate}
Assume that @{text "cup"} is empty and at position @{text "x"}. If @{text "fill(cup)"} and @{text "move(cup,y)"} are conducted consecutively, 
we assume @{text "cup"} to be full and at @{text "y"}.
However, this does not have to be the outcome. What if moving the cup also meant tilting it, so that something poured out?
Both states ``@{text "full"} and @{text "y"}" and ``@{text "empty"} and @{text "y"}"
are conceivable. It is therefore necessary to also consider the \emph{non-effects} of each action.
We could determine them as follows:
\begin{enumerate}
\item After @{text "fill(cup)"} the cup is at position @{text "x"}, if its original position was @{text "x"}.
\item After @{text "move(cup,position)"} the cup is full, if it was full before the move and empty otherwise.\\
Here we assume that @{text "move(cup,position)"} will not result in spilled tea.
\end{enumerate}
These additional assumptions would allow for only one state after conducting  @{text "fill(cup)"} and @{text "move(cup,y)"}
It is the expected ``@{text "full"} and @{text "y"}".

Stating all effects and non-effects requires many statements.
Assuming that there are $n$ actions to be conducted in the environment and $m$ properties of the environment, we would have to state
$n \cdot m$ assumptions. Solving the Frame Problem means to give an adequate description of the environment without having to use
$n \cdot m$ statements. ``Frame" refers to the description of the environment.\\

\noindent In the following, we shall determine how the Frame Problem is connected to modelling the Constitution in HOL.

Since we are interested in verifying an argument about amending and thus changing the Constitution, we are faced
with finding a solution to the Frame Problem. If there were no changes, we wouldn't need to consider their effects, after all.
In our case, an \emph{action} is the introduction of an amendment and the \emph{environment} to be described is the Constitution itself.

There are two factors that make our task more complicated than the standard Frame Problem.

The \textbf{first} is that the ratification of each amendment poses a different action since the amendments are all different
and thus warrant different changes. Here we assume that the legislative would not make the effort of ratifying an amendment 
 more than once.
With each amendment representing a different action, one can only describe the Constitution and its changes if all amendments are known
from the beginning. If that is not the case the Frame Problem extends to also accommodate changing actions. 

In our specific case, the amendments were known from the beginning. Nonetheless this was only partially helpful
due to the \textbf{second} factor. As mentioned in \ref{subsubsec:pre} when defining @{text "rv"} we blend the \emph{contents} of 
amendments with the logic used to \emph{argue about} them. This results in an action not only changing the environment, but also
the scope for actions.
Hence, even with the actions known, we cannot state their effects globally, i.e. for all time instances since the effects
themselves depend on the instance.

To solve the Frame Problem  we chose to explicitly state all effects and non-effects by determining which properties
 will be valid at which time instance.
This was feasible as the number of parameters to describe each instance was low, as were the number of actions performed and the number
of points in time.
Recall that we only had the properties defined at \ref{subsubsec:pre}, such as @{text "oap"},  @{text "rv"} or @{text "Dictatorship"}.
The actions we conducted were the respective ratifications of @{text "amd1a"}, @{text "amd1b"} and @{text "amd2"}.\\

\noindent To conclude this section, let us consider one final connection between modelling the Constitution and the Frame Problem. 
It is the so called legal convention of \emph{lex posterior derogat legi priori} (\emph{lex posterior}).

\noindent According to Parry \& Grant%
\footnote{S. \cite{parry2009}, p.346} it is the principle ``that a later legal rule prevails over 
a prior inconsistent legal rule". This is in effect what @{text "axiom1"} and @{text "axiom2"} in the \hyperref[HOQu]{first}
 part of this section were meant to express.

Finding a good representation of \emph{lex posterior} is another facet of finding a solution to the Frame Problem. Because, if we
do not want to manually go through all rules that are potentially valid at a certain time to then discard the ones that contradict newer rules,
we are forced to use suitable meta rules for reasoning about the rules in question. Solutions to the Frame Problem might provide such 
meta rules.

We mention this last point since finding a good representation of \emph{lex posterior} is an important task for any automated 
legal reasoning based on legal texts that are inconsistent due to their gradual development over time. This also holds
for the Constitution and its amendments. For example \usc{I}{3}{1} states that senators shall be elected by the \emph{legislatives}
 of their home states
while \uscx{XVII}{}{1} states that senators shall be elected by the \emph{people} of their home states. Today only Amend. XVII is used as basis
for state senator elections and yet Art. I remains unchanged. 

With this in mind the narrow version of the Frame Problem needs to be extended to accommodate \emph{lex posterior} in legal contexts.

\<close>

(*<*)
end
(*>*)