(*<*)
theory HOTL imports Main
begin (*An Embedding of Higher-Order Temporal Logic (HOTL) in HOL *)
(*>*)
subsection \<open>HOTL - Higher order temporal logic \label{subsec:HOTL}\<close>

text\<open>
This section introduces the logical operators and data types we will be working with in \hyperref[subsec:Simulation]{Simulation}.
\<close>
subsubsection\<open>Data types \label{subsubsec:types}\<close>

text\<open>
There are two new data types @{text "g"} @{text "time"} and one derived data type @{text "\<sigma>"}.
\<close>

text\<open>% 
\noindent Type @{text "g"} is for governmental institutions, with @{text "Congress"} being Congress, @{text "P"} being the President and @{text "Courts"}
 being the Supreme Court as well as other courts set up by Congress. The legislative, executive 
and judicial powers shall later be bestowed upon these three instances of @{text "g"}. We use @{text "Courts"} rather than
just the Supreme Court since Art. III, \S 1. states that the ``judicial Power 
[...] shall be vested in one supreme Court, and in such inferior Courts as the Congress may [...] ordain and establish."
\<close>

datatype g = Congress | P | Courts

text\<open>
\noindent There are four instances of time: @{text "t\<^sub>1"}-@{text "t\<^sub>3"} as in \ref{subsubsec:time} and @{text "t\<^sub>e"}, the  instance that marks 
the end of time.
At @{text "t\<^sub>1"} the 1947 version of the Constitution is valid.  @{text "t\<^sub>2"} holds the version with an amended Art. V that allows for
amendments that do not maintain states' suffrage and  @{text "t\<^sub>3"} with the Constitution upholding dictatorship.

Note that there is a fourth instance  @{text "t\<^sub>e"}. We need this for technical reasons. Since we want to use an operator  @{text "\<^bold>X"}
that carries a formula from one instance to its successor, it is convenient to have a successor for each instance of time used.
Unless we define a circular successor relation we need a further instance of time that can be the successor of  @{text "t\<^sub>3"} to
avoid inconsistencies. We shall point out where  @{text "t\<^sub>e"} prevents inconsistencies when it becomes relevant below.
\<close>

datatype time = t\<^sub>1 |t\<^sub>2 |t\<^sub>3 |t\<^sub>e 

text\<open>
\noindent Since we will only consider a formula's validity at a certain point in time we need a 
time dependant type for them, as well as operators lifted to that type.

See the following definition of a time dependant formula's type. We will use it to explain what a lifted operator is
and as a basis for our lifted operators.\<close>

type_synonym \<sigma>="(time\<Rightarrow>bool)"(*Type of time dependant formulas *)

text\<open>\noindent %
Assume you have operator
\[\text{ @{text "op::'a\<Rightarrow>bool"}}\]
 where @{text "'a"} is an arbitrary type and @{text "bool"} is Isabelle's version of the boolean type.
 A lifted version 
\[\text{@{text "op\<^sub>l::'a\<Rightarrow>\<sigma>"}}\] of @{text "op"} would be an operator such that for any argument @{text "arg::'a"}
\[\text{@{text "op\<^sub>l arg \<equiv> \<Phi>(op)(arg)"}}\]
 with @{text "\<Phi>::('a\<Rightarrow>bool)\<Rightarrow>'a\<Rightarrow>\<sigma>"} being a suitable function to translate the notion of what @{text "op"} does to a notion
of what it does at a particular instance of time.
What this function @{text "\<Phi>"} looks like depends on @{text "op"}. See below how it is done for the operators we require.
\<close>


(*Lifted HOTL connectives: they operate on time dependant formulas(truth sets).*)
subsubsection\<open>Lifted operators \label{subsubsec:op}\<close>
text\<open>
\noindent
The following are lifted versions for standard logical operators @{text "{\<not>,\<and>,\<or>,\<longrightarrow>.\<longleftrightarrow>}"}, as well as
for @{text "{=,!=}"} and for quantifiers @{text "{\<forall>,\<exists>}"}. 

Observe that the quantifiers lifted may each only be
used for one type of argument. We shall go into detail about polymorphism in \ref{subsubsec:Polym}.

Note also that they need an additional binding for the form we are used to. This is because
the initial definition actually refers to operator $\Pi_{(\alpha \Rightarrow bool)\Rightarrow bool}$ which 
allows us to define a lifted @{text "\<forall>"} using only lambda abstraction%
\footnote{S. \cite{sep-type-theory-church},``1.1 Fundamental Ideas"}.
\<close>

definition tneg :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>t. \<not>\<phi>(t)"
definition tand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>t. \<phi>(t)\<and>\<psi>(t)"   
definition tor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>t. \<phi>(t)\<or>\<psi>(t)"   
definition timp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<longrightarrow>"49) where "\<phi>\<^bold>\<longrightarrow> \<psi> \<equiv> \<lambda>t. \<phi>(t)\<longrightarrow>\<psi>(t)"  
definition tequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<longleftrightarrow>"48) where "\<phi>\<^bold>\<longleftrightarrow>\<psi> \<equiv> \<lambda>t. \<phi>(t)\<longleftrightarrow>\<psi>(t)"
(**)
definition teq :: "g\<Rightarrow>g\<Rightarrow>\<sigma>" (infixr"\<^bold>="40) where "\<phi>\<^bold>=\<psi> \<equiv> \<lambda>t. \<phi>=\<psi>"
definition tneq :: "g\<Rightarrow>g\<Rightarrow>\<sigma>" (infixr"\<^bold>!="40) where "\<phi>\<^bold>!=\<psi> \<equiv> \<lambda>t.\<not>(\<phi>=\<psi>)"
(**)
definition tall_g :: "(g\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sub>g") where "\<^bold>\<forall>\<^sub>g\<Phi> \<equiv> \<lambda>t.\<forall>x. \<Phi>(x)(t)" 
definition tallB_g:: "(g\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>\<^sub>g"[8]9) where "\<^bold>\<forall>\<^sub>gx. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sub>g\<phi>"
(**)
definition texi_g :: "(g\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sub>g") where "\<^bold>\<exists>\<^sub>g\<Phi> \<equiv> \<lambda>t.\<exists>x. \<Phi>(x)(t)"
definition texiB_g:: "(g\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>\<^sub>g"[8]9) where "\<^bold>\<exists>\<^sub>gx. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sub>g\<phi>" 
 (**)
definition tall_s :: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sub>\<sigma>") where "\<^bold>\<forall>\<^sub>\<sigma>\<Phi> \<equiv> \<lambda>t.\<forall>\<phi>. \<Phi>(\<phi>)(t)" 
definition tallB_s:: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>\<^sub>\<sigma>"[8]9) where "\<^bold>\<forall>\<^sub>\<sigma>\<phi>. \<Phi>(\<phi>) \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<Phi>"
(**)
definition texi_s :: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sub>\<sigma>") where "\<^bold>\<exists>\<^sub>\<sigma>\<Phi> \<equiv> \<lambda>t. \<exists>\<phi>. \<Phi>(\<phi>)(t)"
definition texiB_s:: "(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>\<^sub>\<sigma>"[8]9) where "\<^bold>\<exists>\<^sub>\<sigma>\<phi>. \<Phi>(\<phi>) \<equiv> \<^bold>\<exists>\<^sub>\<sigma>\<Phi>"

text\<open>
\noindent The last operator we want to introduce is @{text "\<^bold>X"}. This requires a precedence relation.
To stress the fact that we are talking about a \textit{future} instance of time when using @{text "\<^bold>X"} we
call the relation @{text "succ"} for successor, rather than @{text "pred"} for predecessor. 
\<close>

consts  succ::"time\<Rightarrow>time\<Rightarrow>bool"
axiomatization where
  t1_s_t2: "succ t\<^sub>1 t\<^sub>2"     and
  t2_s_t3: "succ t\<^sub>2 t\<^sub>3"     and
  t3_s_te: "succ t\<^sub>3 t\<^sub>e"     and
  te_s_te: "succ t\<^sub>e t\<^sub>e"     and
  Nt1_s_t1: "\<not>(succ t\<^sub>1 t\<^sub>1)" and 
  Nt1_s_t3: "\<not>(succ t\<^sub>1 t\<^sub>3)" and
  Nt1_s_te: "\<not>(succ t\<^sub>1 t\<^sub>e)" and
  Nt2_s_t1: "\<not>(succ t\<^sub>2 t\<^sub>1)" and 
  Nt2_s_t2: "\<not>(succ t\<^sub>2 t\<^sub>2)" and 
  Nt2_s_te: "\<not>(succ t\<^sub>2 t\<^sub>e)" and
  Nt3_s_t1: "\<not>(succ t\<^sub>3 t\<^sub>1)" and
  Nt3_s_t2: "\<not>(succ t\<^sub>3 t\<^sub>2)" and
  Nt3_s_t3: "\<not>(succ t\<^sub>3 t\<^sub>3)" and
  Nte_s_t1: "\<not>(succ t\<^sub>e t\<^sub>1)" and 
  Nte_s_t2: "\<not>(succ t\<^sub>e t\<^sub>2)" and 
  Nte_s_t3: "\<not>(succ t\<^sub>e t\<^sub>3)"  

text\<open>
\noindent So in Kripke semantics%
\footnote{S. \cite{sep-logic-modal}}
 a visualisation of the instances with @{text "succ"} as accessibility 
relation would look as follows:
\begin{center}
\begin{tikzpicture}[scale=0.2]
\tikzstyle{every node}+=[inner sep=0pt]
\draw [black] (11.3,-8.6) circle (3);
\draw (11.3,-8.6) node {$t_1$};
\draw [black] (23.9,-8.6) circle (3);
\draw (23.9,-8.6) node {$t_2$};
\draw [black] (36.7,-8.6) circle (3);
\draw (36.7,-8.6) node {$t_3$};
\draw [black] (48.9,-8.6) circle (3);
\draw (48.9,-8.6) node {$t_e$};
\draw [black] (39.7,-8.6) -- (45.9,-8.6);
\fill [black] (45.9,-8.6) -- (45.1,-8.1) -- (45.1,-9.1);
\draw [black] (51.407,-6.973) arc (150.70984:-137.29016:2.25);
\fill [black] (51.72,-9.6) -- (52.17,-10.43) -- (52.66,-9.56);
\draw [black] (26.9,-8.6) -- (33.7,-8.6);
\fill [black] (33.7,-8.6) -- (32.9,-8.1) -- (32.9,-9.1);
\draw [black] (14.3,-8.6) -- (20.9,-8.6);
\fill [black] (20.9,-8.6) -- (20.1,-8.1) -- (20.1,-9.1);
\end{tikzpicture}
\end{center}\<close>

text\<open>\noindent %
 Based on @{text "succ"} we can then define @{text "\<^bold>X"}.\<close>

definition tnext :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>X_") where "\<^bold>X\<phi> \<equiv> (\<lambda>t. \<forall>t'. ((succ t t') \<longrightarrow> \<phi> t'))"

 (*Global and local validity of lifted formulas*)
subsubsection\<open>Validity \label{subsubsec:val}\<close>
text\<open>\noindent %
Lastly, we want to define a notion of \textit{validity}. We distinguish between global and local validity.
 
A formula shall be globally valid when it is valid independently of the the current time. This is
useful for universally valid definitions such as what we mean by \textit{dictatorship}.
A formula shall be locally valid for a specific @{text "t"} if it is valid at that instance of time.
 \<close>
definition global_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>t. \<phi> t"
definition local_valid :: "\<sigma>\<Rightarrow>time \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>_"[9]10) where "\<lfloor>\<phi>\<rfloor>\<^sub>t \<equiv> \<phi> t"

text\<open>\noindent %
We conclude this section with checking satisfiability and enlisting all definitions in @{text "Defs"}
so we may access them conveniently in proofs later on.

Lemmas used to test the modelling begin with a @{text "T"} to signify that they are testing lemmas.
The check for satisfiability is one such testing lemma.
\<close>

lemma T_basic_sat_HOTL:"True" nitpick[satisfy,user_axioms,show_all]oops
(*
Introducing "Defs" as the set of the above definitions; useful for convenient unfolding.*)
named_theorems Defs declare
  tneg_def[Defs] tand_def[Defs] 
  tor_def[Defs] timp_def[Defs] tequ_def[Defs] 
  teq_def[Defs] tneq_def[Defs]
  tall_g_def[Defs] tallB_g_def[Defs] 
  texi_g_def[Defs] texiB_g_def[Defs]
  tall_s_def[Defs] tallB_s_def[Defs]
  texi_s_def[Defs] texiB_s_def[Defs] 
  tnext_def[Defs]
  global_valid_def[Defs] local_valid_def[Defs]

(*<*)
end 
(*>*)