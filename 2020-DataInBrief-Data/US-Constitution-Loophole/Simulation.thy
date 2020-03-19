(*<*)
theory Simulation imports HOTL
begin
(*>*)
subsection \<open>Simulation \label{subsec:Simulation}\<close>

text\<open>\noindent %
This section is made up of four parts. 
In \ref{subsubsec:pre} basic notions are defined that will be
used throughout the remainder of the section.
Part \ref{subsubsec:t1} gives an axiomatization of what is valid at @{text "t\<^sub>1"} and some proofs on
the basis of those axioms. 
The same holds for \ref{subsubsec:t2} and \ref{subsubsec:t3}, only they describe
the state at @{text "t\<^sub>2"} and @{text "t\<^sub>3"} respectively. \<close>

(* Preliminaries *)
subsubsection \<open> Preliminaries \label{subsubsec:pre}\<close>

text\<open>\noindent %
We begin with definitions for governmental institutions @{text "g"}. They express that @{text "g"} is a certain branch of government.

This is a very simplified version of the Constitution, stripped off anything not relevant to the argument.
For instance, rather than saying that some @{text "g"} has executive powers and is thus entitled to command the army,
grant and reprieve pardons\footnote{S. \usc{2}{2}{}}, we simply state that @{text "g"} \emph{is} the executive.\<close>
consts (*predicates for branches of government *)
       is_leg::"g\<Rightarrow>\<sigma>"     \<comment> \<open>g is the legislative\<close>
       is_exe::"g\<Rightarrow>\<sigma>"     \<comment> \<open>g is the executive\<close>
       is_jud::"g\<Rightarrow>\<sigma>"     \<comment> \<open>g is the judiciary\<close>

text\<open>\noindent %
We require the branches to be unique, i.e. each branch has to have a unique governmental institution associated with it.

One could imagine a distribution of one branch over several governmental institutions. In fact, governmental institution
@{text "Courts"} represents a collection of courts and thus several different governmental institutions. To Isabelle, however, 
it is a single instance of type @{text "g"}. Only we know that @{text "Courts"} isn't just one institution.

We choose to demand uniqueness because it keeps the model simple without taking
away any concepts necessary to the argument. If we didn't demand uniqueness, we would have to explicitly state which
institutions represent which branches \emph{and} which they do not represent. Otherwise, the fact that for example @{text "Congress"}
is legislative would not imply that @{text "P"} isn't. So @{text "P"} could be both legislative and executive. To then prove
 non-dictatorship for @{text "t\<^sub>1"} and @{text "t\<^sub>2"} would be impossible since any institution could be all of the branches.

Given that we do not need to model an institution representing several branches we may as well simplify things and demand uniqueness.
\<close>

axiomatization where
       unique_is_leg: "\<lfloor>\<^bold>\<forall>\<^sub>gg1. \<^bold>\<forall>\<^sub>gg2. (((is_leg g1)\<^bold>\<and>(is_leg g2))\<^bold>\<longrightarrow>(g1 \<^bold>= g2))\<rfloor>" and
       unique_is_exe: "\<lfloor>\<^bold>\<forall>\<^sub>gg1. \<^bold>\<forall>\<^sub>gg2. (((is_exe g1)\<^bold>\<and>(is_exe g2))\<^bold>\<longrightarrow>(g1 \<^bold>= g2))\<rfloor>" and
       unique_is_jud: "\<lfloor>\<^bold>\<forall>\<^sub>gg1. \<^bold>\<forall>\<^sub>gg2. (((is_jud g1)\<^bold>\<and>(is_jud g2))\<^bold>\<longrightarrow>(g1 \<^bold>= g2))\<rfloor>" 
(*<*)
named_theorems Unique declare unique_is_leg[Unique] unique_is_exe[Unique] unique_is_jud[Unique]
(*>*)

text\<open>\noindent %
 There is a dictatorship at @{text "t"} if at that instance of time a dictator @{text "d"} exists that represents
all branches of government.\<close>

definition Dictatorship::"\<sigma>" 
  where "Dictatorship \<equiv> \<lambda>t. \<exists>d. \<lfloor>(is_leg d) \<^bold>\<and> (is_exe d) \<^bold>\<and> (is_jud d)\<rfloor>\<^sub>t"

text\<open>\noindent %
Below follow some predicates for formulas @{text "\<phi>::\<sigma>"}. Based on these we also define predicates that are only dependant on time, and thus
are either valid or not valid for a certain instance of time. These will serve as properties of the Constitution at different points in time.
\<close>

consts  (*predicates for branches of government *)
      is_amd::"\<sigma>\<Rightarrow>\<sigma>"       \<comment> \<open>@{text "\<phi>"} is an amendment\<close>
      is_prop::"\<sigma>\<Rightarrow>\<sigma>"       \<comment> \<open>@{text "\<phi>"} is proposed\<close>
      is_rat::"\<sigma>\<Rightarrow>\<sigma>"         \<comment> \<open>@{text "\<phi>"} is ratified\<close>
      sup_prop::"g\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" \<comment> \<open>@{text "\<phi>"} has support by @{text "g"} to be proposed\<close>
      sup_rat::"\<sigma>\<Rightarrow>\<sigma>"       \<comment> \<open>@{text "\<phi>"} has support to be ratified\<close>
      maint_suf::"\<sigma>\<Rightarrow>\<sigma>"   \<comment> \<open>@{text "\<phi>"} maintains suffrage in Senate for all states\<close>

text\<open>\noindent %
We shall now define the following concepts:
\begin{labeling}{@{text "omsp"}}
\item[@{text "oap"}] Only amendments may be proposed. \\This time dependant formula is used for technical reasons.
It helps to distinguish between generic formulas @{text "\<phi>"} of type @{text "\<sigma>"} and what we call amendment. For example
@{text "oap"} itself may not be proposed if it isn't also declared an amendment.
\item[@{text "osp"}] Only if an amendment has the support of the legislative, can it be proposed. 
\\This is a simplified version of what Art. V says. Basically @{text "osp"} requires an amendment to have support by two thirds
of both houses of Congress. As mentioned above we omit the option of support by a specific convention, so we can concentrate solely on
horizontal division of power.\\
Another reason why this simplified version is preferable is because it is more generic and allows for a change of interpretation. That is, 
 we can make a statement about the legislative supporting an amendment, no matter if the current constitution stipulates
Congress to be the legislative or not.
\item[@{text "omsp"}] Only amendments that maintain suffrage may be proposed.
\item[@{text "opr"}] Only proposed amendments may be ratified at the next time instance.  
\item[@{text "osr"}] Only if an amendment has the support for ratification, can it be ratified in the future.
\item[@{text "psr"}] If an amendment is proposed and has the support for ratification, it will be ratified at the next
time instance.\\
This will be used to show that an amendment proposed at @{text "t\<^sub>i"} is ratified and thus valid at @{text "t\<^sub>i\<^sub>+\<^sub>1"}, given that
it also has support for ratification at @{text "t\<^sub>i"}.
\\Note that together with @{text "opr"} this makes proposition and ratification of an amendment a two-step process. 
\item[@{text "rv"}] If an amendment is ratified, it is also valid.
\\Here the framework for reasoning about amendments is entwined with the the content of the amendments. In combination with @{text "psr"} this property is a
 precarious one to work with for, as soon as @{text "rv"} is declared to be valid for some @{text "t"}, 
it will be possible to prove anything as long as it has been proposed with support for ratification in the preceding instance of time.
\end{labeling}\<close>

abbreviation oap::"\<sigma>"
  where "oap \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(is_amd \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(is_prop \<phi>))" 
(**)
abbreviation osp::"\<sigma>" 
  where "osp \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. \<^bold>\<forall>\<^sub>gg.(is_leg g)\<^bold>\<longrightarrow>((\<^bold>\<not>(sup_prop g \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(is_prop \<phi>)))"
(**)
abbreviation omsp::"\<sigma>"
  where "omsp \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(maint_suf \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(is_prop \<phi>))"
(**)
abbreviation opr::"\<sigma>" 
  where "opr \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(is_prop \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(\<^bold>X(is_rat \<phi>)))"
(**)
abbreviation osr::"\<sigma>"
  where "osr \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. \<^bold>\<forall>\<^sub>gg. (\<^bold>\<not>(sup_rat \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(\<^bold>X(is_rat \<phi>)))"
(**)
abbreviation psr::"\<sigma>"
  where "psr \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (is_prop \<phi> \<^bold>\<and> (sup_rat \<phi>))\<^bold>\<longrightarrow> (\<^bold>X(is_rat \<phi>))"
(**)
abbreviation rv::"\<sigma>"
  where "rv \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (is_rat \<phi>) \<^bold>\<longrightarrow> \<phi>"


(* Time instance t1*)
subsubsection \<open> Time instance @{term "t\<^sub>1"} \label{subsubsec:t1}\<close>
text\<open>\noindent %
 The following section starts with an axiomatic description of the Constitution's state at @{text "t\<^sub>1"}. This also includes
some preparation for @{text "t\<^sub>2"}, namely defining amendment @{text "amd1"} and giving axioms on what ought to be valid
at @{text "t\<^sub>2"}.

Before proceeding to @{text "t\<^sub>2"}, we will prove some properties valid at @{text "t\<^sub>1"}, in particular that there is no dictatorship
at @{text "t\<^sub>1"} with the given axioms.
\<close> 
(* State of constitution at t1*)
text\<open>\noindent %
 At @{text "t\<^sub>1"} @{text "Congress"} is the legislative, the @{text "President"} is the executive and the @{text "Courts"} are the judiciary.
We write @{text "President"} for constant @{text "P"} in continuous text for better readability but use @{text "P"} in commands to keep names
short.
\<close>
axiomatization where
    Con_Leg_t1: "\<lfloor>is_leg Congress\<rfloor>\<^sub>t\<^sub>1" and
    P_Exe_t1: "\<lfloor>is_exe P\<rfloor>\<^sub>t\<^sub>1" and
    Cou_Jud_t1: "\<lfloor>is_jud Courts\<rfloor>\<^sub>t\<^sub>1" 

text\<open>\noindent %
All of the above defined properties for an instance of time are valid at @{text "t\<^sub>1"}.\<close>
axiomatization where
    oap_t1: "\<lfloor>oap\<rfloor>\<^sub>t\<^sub>1" and 
    osp_t1: "\<lfloor>osp\<rfloor>\<^sub>t\<^sub>1" and
    omsp_t1:"\<lfloor>omsp\<rfloor>\<^sub>t\<^sub>1" and
    opr_t1: "\<lfloor>opr\<rfloor>\<^sub>t\<^sub>1" and
    rv_t1:  "\<lfloor>rv\<rfloor>\<^sub>t\<^sub>1" and
    osr_t1: "\<lfloor>osr\<rfloor>\<^sub>t\<^sub>1" and
    psr_t1: "\<lfloor>psr\<rfloor>\<^sub>t\<^sub>1"


(*Preparation for t2 *)

text\<open>\noindent %
 Here are two suggestions of what @{text "amd1"} might look like.\<close>

definition amd1a::\<sigma>
  where "amd1a \<equiv> \<^bold>\<exists>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(maint_suf \<phi>))\<^bold>\<and>((is_prop \<phi>))"
definition amd1b::\<sigma>
  where "amd1b \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (is_prop \<phi>)\<^bold>\<longrightarrow> ((maint_suf \<phi>) \<^bold>\<or> \<^bold>\<not>(maint_suf \<phi>))"

text\<open>\noindent %
 Neither are optimal solutions.
Indeed, there is no optimal solution for the presented framework.

This is because what we want @{text "amd1"} to say is that it is not necessary for all proposed amendments 
to maintain all states' suffrage in Senate.
In other words we want condition 
\[ \text{@{text "omsp \<equiv> \<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(maint_suf \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(is_prop \<phi>))"}} \]
to be omitted at @{text "t\<^sub>2"}.
This, however is not the same as requiring the amendment to be the negation of @{text "osmp"} as @{text "amd1a"} does.
The negation would require at least one @{text "\<phi>::\<sigma>"} to expressly \emph{not} maintain suffrage rights for some state \emph{and} 
be proposed. Yet, it were acceptable both if such a @{text "\<phi>"} existed and if it didn't. We do not want to demand
such a @{text "\<phi>"} into existence.

One could therefore choose to use @{text "amd1b"} that states a proposed @{text "\<phi>"} may either satisfy the @{text "maint_suf"}
condition or it may not. Unfortunately, this is a tautology since @{term "a \<longrightarrow> b"} is always true if @{text "b"} is always true.
The @{text "b"} in this case is tautology @{text "(maint_suf \<phi>) \<^bold>\<or> \<^bold>\<not>(maint_suf \<phi>)"} and thus always true.

Although the suggested amendments do not constitute ideal amendments for the desired outcome, we shall still use them.
They help to illustrate how one can reason about amendments within this framework.

Notice that one could introduce deontic logic%
\footnote{For an overview of deontic logic, see \cite{sep-logic-deontic}}
 to argue about the \emph{necessity} of @{text "omsp"}. We choose not to do this
in order to avoid inadvertent errors due to a mixture of deontic and temporal logic.
\<close>

text\<open>\noindent %
 Next there are a few axioms that pave the way for the state at @{text "t\<^sub>2"}.\<close>

text\<open>\noindent %
 Amendments @{text "amd1a"} and @{text "amd1b"} are both proposed and have support for ratification at @{text "t\<^sub>1"}, so
they may be ratified at the next instance.
\<close>
axiomatization where
  amd1a_prop_t1:    "\<lfloor>is_prop amd1a\<rfloor>\<^sub>t\<^sub>1" and
  amd1a_sup_rat_t1: "\<lfloor>sup_rat amd1a\<rfloor>\<^sub>t\<^sub>1" and
  amd1b_prop_t1:    "\<lfloor>is_prop amd1b\<rfloor>\<^sub>t\<^sub>1" and
  amd1b_sup_rat_t1: "\<lfloor>sup_rat amd1b\<rfloor>\<^sub>t\<^sub>1"  

text\<open>\noindent %
 The distribution of powers stays the same at the next instance: @{text "Congress"} is the legislative,
the @{text "President"} the executive and @{text "Courts"} are the judiciary.\<close>
axiomatization where
  XCon_Leg_t1: "\<lfloor>\<^bold>X(is_leg Congress)\<rfloor>\<^sub>t\<^sub>1" and
  XP_Exe_t1:   "\<lfloor>\<^bold>X(is_exe P)\<rfloor>\<^sub>t\<^sub>1"         and
  XCou_Jud_t1: "\<lfloor>\<^bold>X(is_jud Courts)\<rfloor>\<^sub>t\<^sub>1" 

text\<open>\noindent %
 All properties defined in \ref{subsubsec:pre} are valid next time, except for @{text "maint_suf"}. This is
to ensure that we can introduce an amendment at @{text "t\<^sub>2"} that does not satisfy @{text "maint_suf"}.

\noindent In a way the amendment to Art. V is implemented by simply not using @{text "\<lfloor>\<^bold>X omsp\<rfloor>\<^sub>t\<^sub>1"} as axiom, 
rather than by working with one of the above suggested amendments @{text "amd1a"} and @{text "amd1b"}.

One could criticize two aspects of this approach. \textbf{Firstly}, the fact that not an actual amendment
is used to bring about the change but rather the lack of an axiom. As argued above this is not possible, however.
\textbf{Secondly}, it shouldn't be necessary for us to explicitly state which axioms to keep and which to give up when transitioning to
the next time point. It would be preferable if the logical system automatically kept all axioms that do not lead to contradictions 
and discarded the problematic ones. We will see in \ref{subsubsec:HOQu} why this is not easily done and content ourselves with 
the solution at hand.

Observe that our logic is suitable to express this problem in the sense that we would run into inconsistencies, 
were we to keep condition @{text "omsp"} for @{text "t\<^sub>2"} and also introduce an amendment @{text "amd2"} with @{text "\<^bold>\<not>(maint_suf amd2)"}. 

\<close>
axiomatization where
  Xoap_t1:"\<lfloor>\<^bold>X oap\<rfloor>\<^sub>t\<^sub>1" and
  Xosp_t1:"\<lfloor>\<^bold>X osp\<rfloor>\<^sub>t\<^sub>1" and
  Xopr_t1:"\<lfloor>\<^bold>X opr\<rfloor>\<^sub>t\<^sub>1" and
  Xrv_t1: "\<lfloor>\<^bold>X rv\<rfloor>\<^sub>t\<^sub>1"  and
  Xosr_t1:"\<lfloor>\<^bold>X osr\<rfloor>\<^sub>t\<^sub>1" and
  Xpsr_t1:"\<lfloor>\<^bold>X psr\<rfloor>\<^sub>t\<^sub>1" 

(* No dictatorship at t1*)
text\<open>\noindent %
 Using the axioms provided above, we shall prove that there is no dictatorship at @{text "t\<^sub>1"}.
This requires the proof of facts @{text "only_g_power_t1"} meaning that @{text "g"}  is the only governmental
institution with @{text "power"}(legislative, executive, judicial) at @{text "t\<^sub>1"}. Since @{text "g"} is different for each @{text "power"}
 no dictatorship can be in place at @{text "t\<^sub>1"}. 
\<close>

lemma only_Con_Leg_t1: "\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_leg g)\<^bold>\<longrightarrow>(g \<^bold>= Congress)\<rfloor>\<^sub>t\<^sub>1" 
  unfolding Defs using unique_is_leg Con_Leg_t1
  by (simp add: global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)

lemma only_P_Exe_t1:"\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_exe g)\<^bold>\<longrightarrow>(g \<^bold>= P)\<rfloor>\<^sub>t\<^sub>1"
  unfolding Defs using unique_is_exe P_Exe_t1 
  by (simp add: global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)

lemma only_Cou_Jud_t1:"\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_jud g)\<^bold>\<longrightarrow>(g \<^bold>= Courts)\<rfloor>\<^sub>t\<^sub>1"
  unfolding Defs using unique_is_jud Cou_Jud_t1
  by (simp add: global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)

text\<open>\noindent %
 With these we can prove theorem @{text "noDictatorship_t1"}.\<close>

theorem noDictatorship_t1: "\<lfloor>\<^bold>\<not> Dictatorship\<rfloor>\<^sub>t\<^sub>1" 
  unfolding Defs using only_Con_Leg_t1 only_P_Exe_t1 only_Cou_Jud_t1
  by (metis (no_types, lifting) Dictatorship_def g.distinct(1) local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)(*

 List of theorems at  t1*)
(*<*)
named_theorems t1_state and t1_prep_t2  declare 
 (* t1_state -ax *) Con_Leg_t1[t1_state] P_Exe_t1[t1_state] Cou_Jud_t1[t1_state]
                oap_t1[t1_state] osp_t1[t1_state] omsp_t1[t1_state] opr_t1[t1_state] rv_t1[t1_state] osr_t1[t1_state] psr_t1[t1_state] 
 (* t1_state -derived *) noDictatorship_t1[t1_state]
 (* t1_prep_t2 *) amd1b_prop_t1[t1_prep_t2] amd1b_sup_rat_t1[t1_prep_t2] Xoap_t1[t1_prep_t2] Xosp_t1[t1_prep_t2] Xopr_t1[t1_prep_t2] Xrv_t1[t1_prep_t2] Xosr_t1[t1_prep_t2] Xpsr_t1[t1_prep_t2]
(*>*)(*
*)(*<*)
 (*just some tests for t1*)
lemma T_is_prop_cond: "\<lfloor>\<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>((is_amd \<phi>) \<^bold>\<and> (maint_suf \<phi>) \<^bold>\<and> (sup_prop Congress \<phi>)))\<^bold>\<longrightarrow>(\<^bold>\<not>(is_prop \<phi>))\<rfloor>\<^sub>t\<^sub>1"
  using oap_t1 osp_t1 omsp_t1 unfolding Defs 
  using Con_Leg_t1 local_valid_def by blast
  \<comment> \<open>can axioms for proposition-conditions be generalised to one?\<close>
lemma T_is_rat_cond: "\<lfloor>\<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>((is_prop \<phi>) \<^bold>\<and> (sup_rat \<phi>)))\<^bold>\<longrightarrow>(\<^bold>\<not>(\<^bold>X(is_rat \<phi>)))\<rfloor>\<^sub>t\<^sub>1"
  using oap_t1 opr_t1 osr_t1 unfolding Defs
  by blast
  \<comment> \<open>can axioms for ratification-conditions be generalised to one?\<close>
lemma T_is_rat_ind_cond: "\<lfloor>\<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>((is_amd \<phi>) \<^bold>\<and> (maint_suf \<phi>) \<^bold>\<and> (sup_prop Congress \<phi>)))\<^bold>\<longrightarrow>(\<^bold>\<not>(\<^bold>X(is_rat \<phi>)))\<rfloor>\<^sub>t\<^sub>1" 
  using oap_t1 opr_t1 osp_t1 omsp_t1 unfolding Defs
  using Con_Leg_t1 local_valid_def by blast
  \<comment> \<open>are prop-conditions also X-rat-conditions? They should be since rat only possible if prop.\<close>
lemma T_amd1b_is_amd:"\<lfloor>is_amd amd1b\<rfloor>\<^sub>t\<^sub>1" 
  unfolding Defs using oap_t1 amd1b_prop_t1
  using local_valid_def tallB_s_def tall_s_def timp_def tneg_def by auto
lemma T_amd1b_sup_prop:"\<lfloor>sup_prop Congress amd1b\<rfloor>\<^sub>t\<^sub>1" 
  unfolding Defs using osp_t1 amd1b_prop_t1 Con_Leg_t1
  using local_valid_def tallB_s_def tall_s_def tallB_g_def tall_g_def tand_def timp_def tneg_def by auto
lemma T_amd1b_maint_suf:"\<lfloor>maint_suf amd1b\<rfloor>\<^sub>t\<^sub>1" 
  unfolding Defs using omsp_t1 amd1b_prop_t1
  using local_valid_def tallB_s_def tall_s_def timp_def tneg_def by auto                                    
(*>*)(*
*)
text\<open>\noindent %
 Finally we check whether the axioms so far are even satisfiable by asking Nitpick to find a satisfiable model for @{text "True"},
 which it does.\<close>
lemma T_basic_sat_t1: "True" nitpick[satisfy,user_axioms,show_all,card time = 4]oops

(* Time instance t2*)
subsubsection \<open>Time instance @{term "t\<^sub>2"} \label{subsubsec:t2}\<close>
text\<open>\noindent %
 As before there are three parts to @{text "t\<^sub>2"}. This time they differ a little in structure.

The description of the current state is not given by a set of axioms but rather conclusions drawn from the preparation
at @{text "t\<^sub>1"}. This also includes proofs for the validity of @{text "amd1a"} and @{text "amd1b"}.
The preparation for the next instance of time introduces the new amendment @{text "amd2"}.
The proof for the non-existence of dictatorship at @{text "t\<^sub>2"} is practically the same as in @{text "t\<^sub>1"}.
\<close>
(* State of constitution at t2*)
text\<open>\noindent %
 Based on axioms @{text " XCon_Leg_t1"}, @{text "XP_Exe_t1"} and @{text "XCou_Jud_t1"} we can now deduct that @{text "Congress"} is still the 
legislative, the @{text "President"} the executive and @{text "Courts"} are the judiciary.\<close>
lemma Con_Leg_t2:"\<lfloor>is_leg Congress\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs
  using XCon_Leg_t1 local_valid_def tnext_def t1_s_t2 by auto

lemma P_Exe_t2:"\<lfloor>is_exe P\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs using tnext_def XP_Exe_t1
  using XP_Exe_t1 local_valid_def tnext_def t1_s_t2 by auto

lemma Cou_Jud_t2:"\<lfloor>is_jud Courts\<rfloor>\<^sub>t\<^sub>2"
  using XCou_Jud_t1 local_valid_def tnext_def t1_s_t2 by auto

text\<open>\noindent %
 Analogously, we can refer to axioms @{text "Xproperty_t1"} to conclude that @{text "property"} is valid at
@{text "t\<^sub>2"}. These are the same properties we had for @{text "t\<^sub>1"} with the exception of @{text "omsp"}.
\<close>
lemma oap_t2:"\<lfloor>oap\<rfloor>\<^sub>t\<^sub>2"
  using Xoap_t1 local_valid_def tnext_def t1_s_t2 by auto
lemma osp_t2:"\<lfloor>osp\<rfloor>\<^sub>t\<^sub>2"
  using Xosp_t1 local_valid_def tnext_def t1_s_t2 by auto
lemma opr_t2:"\<lfloor>opr\<rfloor>\<^sub>t\<^sub>2"
  using Xopr_t1 local_valid_def tnext_def t1_s_t2 by auto
lemma rv_t2:"\<lfloor>rv\<rfloor>\<^sub>t\<^sub>2"
  using Xrv_t1 local_valid_def tnext_def t1_s_t2 by auto
lemma osr_t2:"\<lfloor>osr\<rfloor>\<^sub>t\<^sub>2"
  using Xosr_t1 local_valid_def tnext_def t1_s_t2 by auto
lemma psr_t2:"\<lfloor>psr\<rfloor>\<^sub>t\<^sub>2"
  using Xpsr_t1 local_valid_def tnext_def t1_s_t2 by auto

(* amds now valid  t2*)
text\<open>\noindent %
Below are proofs for the amendments proposed previously.

As discussed above, the outline for a validity proof where an amendment @{text "amd"} is concerned is as follows:
\begin{center}
\begin{tabularx}{0.7\textwidth}{c  c}
$t_i$&  $t_{i+1}$ \\ \midrule
@{text "psr_t\<^sub>i"}& @{text "rv_t\<^sub>i\<^sub>+\<^sub>1"} \\ \hline
 @{text "is_prop amd"}& \rdelim\}{2}{1.8cm}[$\underset{\text{@{text "psr_t\<^sub>i"}}}{\Rightarrow}$ @{text "is_rat amd"} $~~~\underset{\text{@{text "rv_t\<^sub>i\<^sub>+\<^sub>1"}}}{\Rightarrow}$ @{text "amd"}]\\
@{text "sup_rat amd"} & \\
\end{tabularx}
\end{center}

\noindent This is exactly what we do with @{text "amd1a"}. Using @{text " amd1a_prop_t1"}, @{text " amd1a_sup_rat_t1"} and @{text "psr_t1"}
 we get that @{text "\<lfloor>\<^bold>X(is_rat amd1a)\<rfloor>\<^sub>t\<^sub>1"}. By definition of @{text "\<^bold>X"}
this means that @{text "\<lfloor>is_rat amd1a\<rfloor>\<^sub>t\<^sub>2"} is true and by @{text "rv_t2"} that @{text "\<lfloor>amd1a\<rfloor>\<^sub>t\<^sub>2"} is true.
\<close>

(*amd1a*)
lemma amd1a_val_t2:"\<lfloor>amd1a\<rfloor>\<^sub>t\<^sub>2"
proof -
  have "\<lfloor>\<^bold>X(is_rat amd1a)\<rfloor>\<^sub>t\<^sub>1"  
    using amd1a_prop_t1 amd1a_sup_rat_t1 psr_t1 local_valid_def tallB_s_def tall_s_def tand_def timp_def tnext_def 
    by auto
  thus "\<lfloor>amd1a\<rfloor>\<^sub>t\<^sub>2" 
    using local_valid_def tallB_s_def tall_s_def timp_def tnext_def rv_t2 t1_s_t2 
    by auto
qed

text\<open>\noindent %
See below that we can prove @{text "\<lfloor>amd1b\<rfloor>\<^sub>t\<^sub>2"} with or without these axioms.
 We do not need to use the deduction rules provided by our axioms because
 @{text "amd1b"} is a tautology. Indeed, we can also show @{text "amd1b"}'s validity for @{text "t\<^sub>1"} and its global validity.
This is not possible with @{text "amd1a"}.
 \<close>

(*amd1b*)
lemma amd1b_val_t2:"\<lfloor>amd1b\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs
  by (simp add: amd1b_def tallB_s_def tall_s_def timp_def tneg_def tor_def)

lemma amd1b_val_t2_2:"\<lfloor>amd1b\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs using amd1b_sup_rat_t1 amd1b_prop_t1 psr_t1 rv_t2
  by (simp add: amd1b_def tallB_s_def tall_s_def timp_def tneg_def tor_def)

lemma amd1b_val_t1:"\<lfloor>amd1b\<rfloor>\<^sub>t\<^sub>1"
  unfolding Defs 
  by (simp add: amd1b_def tallB_s_def tall_s_def timp_def tneg_def tor_def)

lemma amd1b_val:"\<lfloor>amd1b\<rfloor>"
  unfolding Defs 
  by (simp add: amd1b_def tallB_s_def tall_s_def timp_def tneg_def tor_def)

(*Preparation for t3 at t2*)

text\<open>\noindent %
 Now we introduce @{text "amd2"} which will transfer all governmental power to the @{text "President"}.
Technically @{text "amd2"} does not bereave any state of its votes in Senate and would thus satifsy @{text "maint_suf"}.
However, if Congress does not have any real power any more, then neither do its members, which would render any state's
votes inane. So, in effect, we have that @{text "\<not>(maint_suf amd2)"}.

Notice that we cannot declare @{text "\<not>(maint_suf amd2)"} to be globally valid since a state's votes in Senate depend on
what the Constitution currently looks like. Were we to consider predicate @{text "maint_suf"} for @{text "amd2"} at a time when
states have no suffrage in Senate  @{text "(maint_suf amd2)"} would be true.
\<close>

definition amd2::\<sigma> where " amd2 \<equiv> is_leg P \<^bold>\<and> is_exe P \<^bold>\<and> is_jud P"
axiomatization where
  amd2_prop_t2:"\<lfloor>is_prop amd2\<rfloor>\<^sub>t\<^sub>2" and
  amd2_sup_rat_t2:"\<lfloor>sup_rat amd2\<rfloor>\<^sub>t\<^sub>2" and
  amd2_not_maint_suf_t2:"\<lfloor>\<^bold>\<not>(maint_suf amd2)\<rfloor>\<^sub>t\<^sub>2" 

text\<open>\noindent %
 As before we intend to keep all time dependant conditions except for @{text "omsp"} when transitioning to @{text "t\<^sub>3"}.
\<close>

axiomatization where
  Xoap_t2:"\<lfloor>\<^bold>X oap\<rfloor>\<^sub>t\<^sub>2" and
  Xosp_t2:"\<lfloor>\<^bold>X osp\<rfloor>\<^sub>t\<^sub>2" and
  Xopr_t2:"\<lfloor>\<^bold>X opr\<rfloor>\<^sub>t\<^sub>2" and
  Xrv_t2:"\<lfloor>\<^bold>X rv\<rfloor>\<^sub>t\<^sub>2" and
  Xosr_t2:"\<lfloor>\<^bold>X osr\<rfloor>\<^sub>t\<^sub>2" and
  Xpsr_t2:"\<lfloor>\<^bold>X psr\<rfloor>\<^sub>t\<^sub>2"

text\<open>\noindent %
In \ref{subsubsec:types} we mentioned that we needed @{text "t\<^sub>e"} for technical reasons.
This is because we want to use above given axiom @{term "\<lfloor>\<^bold>X opr\<rfloor>\<^sub>t\<^sub>2"} without creating inconsistencies due to a missing successor for @{term "t\<^sub>3"}.
\begin{align*}
\text{@{term "\<lfloor>\<^bold>X opr\<rfloor>\<^sub>t\<^sub>2"}} &\Rightarrow \text{@{term "\<lfloor>opr\<rfloor>\<^sub>t\<^sub>3"}} \\
&\Leftrightarrow \text{@{text "\<lfloor>\<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>\<not>(is_prop \<phi>))\<^bold>\<longrightarrow>(\<^bold>\<not>(\<^bold>X(is_rat \<phi>)))\<rfloor>\<^sub>t\<^sub>3"}}\\
&\Leftrightarrow \text{@{text "\<lfloor>\<^bold>\<forall>\<^sub>\<sigma>\<phi>. (\<^bold>X(is_rat \<phi>))\<^bold>\<longrightarrow>(is_prop \<phi>)\<rfloor>\<^sub>t\<^sub>3"}} \\
&\Leftrightarrow \text{@{text "\<forall>\<phi>. ((\<^bold>X(is_rat \<phi>))t\<^sub>3)\<longrightarrow>(is_prop \<phi>) t\<^sub>3"}} \\
&\Leftrightarrow \text{@{text "\<forall>\<phi>. \<forall>t'.((succ t\<^sub>3 t')\<longrightarrow>(is_rat \<phi>) t')\<longrightarrow>(is_prop \<phi>) t\<^sub>3"}} \\
\end{align*}
If @{text "t\<^sub>3"} does not have a successor @{text "(succ t\<^sub>3 t')"} will always be false, making @{text "(succ t\<^sub>3 t')\<longrightarrow>(is_rat \<phi>) t'"}
always true which it shouldn't be. As soon as term @{text "(is_prop \<phi>) t\<^sub>3"} is not true for some @{text "\<phi>"}, axiom @{term "\<lfloor>\<^bold>X opr\<rfloor>\<^sub>t\<^sub>2"}
will cause an inconsistency.

We therefore want @{text "t\<^sub>3"} to have a successor. In order to avoid circular succession we introduce dummy instance @{text "t\<^sub>e"}.
\<close>

(* No dictatorship at  t2*)
text\<open>\noindent %
 Analogously to the proof at \ref{subsubsec:t1}, we prove properties @{text "only_g_power_t2"} for @{text "g"}, governmental institution
and @{text "power \<in> {legilslative power, executive power, judicial power}"} to use them in the proof for @{text "noDictatorship_t2"}.\<close>
lemma only_Con_Leg_t2:"\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_leg g)\<^bold>\<longrightarrow>(g \<^bold>= Congress)\<rfloor>\<^sub>t\<^sub>2" 
  using unique_is_leg Con_Leg_t2 global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def 
  by simp

lemma only_P_Exe_t2:"\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_exe g)\<^bold>\<longrightarrow>(g \<^bold>= P)\<rfloor>\<^sub>t\<^sub>2"
  unfolding Defs using unique_is_exe P_Exe_t2
  by (simp add: global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)

lemma only_Cou_Jud_t2:"\<lfloor>\<^bold>\<forall>\<^sub>gg. (is_jud g)\<^bold>\<longrightarrow>(g \<^bold>= Courts)\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs using unique_is_jud Cou_Jud_t2
  by (simp add: global_valid_def local_valid_def tallB_g_def tall_g_def tand_def teq_def timp_def)

theorem noDictatorship_t2: "\<lfloor>\<^bold>\<not> Dictatorship\<rfloor>\<^sub>t\<^sub>2" 
  unfolding Defs using only_Con_Leg_t2 only_P_Exe_t2 only_Cou_Jud_t2 Dictatorship_def
  by (metis (mono_tags, lifting) g.distinct(3) local_valid_def tallB_g_def tall_g_def  tand_def teq_def timp_def)

(* List of theorems at  t2*)
(*<*)
named_theorems t2_state and t2_prep_t3  declare 
 (* t2_state -derived *) Con_Leg_t2[t2_state] P_Exe_t2[t2_state] Cou_Jud_t2[t2_state]
                oap_t2[t2_state] osp_t2[t2_state] opr_t2[t2_state] rv_t2[t2_state] osr_t2[t2_state] psr_t2[t2_state]
                amd1b_val_t2[t2_state] amd1a_val_t2[t2_state] 
                only_Con_Leg_t2[t2_state] only_P_Exe_t2[t2_state] only_Cou_Jud_t2[t2_state]
                noDictatorship_t2[t2_state]
 (* t2_prep_t3 *) amd2_prop_t2[t2_prep_t3] amd2_sup_rat_t2[t2_prep_t3]  amd2_not_maint_suf_t2[t2_prep_t3] 
                Xoap_t2[t2_prep_t3]  Xopr_t2[t2_prep_t3] Xrv_t2[t2_prep_t3]  Xpsr_t2[t2_prep_t3]
(*>*)

text\<open>\noindent %
 Also, analogously we make sure that Nitpick can still find a satisfiable model for our axioms.\<close>
lemma T_basic_sat_t2: "True" nitpick[satisfy,user_axioms,show_all,card time = 4]oops

(* Time instance t3*)
subsubsection \<open>Time instance @{term "t\<^sub>3"} \label{subsubsec:t3}\<close>
(*State of constitution at t3*)

text\<open>\noindent %
 The remainder of this section is rather simple. We prove properties for new time instance @{text "t\<^sub>3"} using
previously provided axioms @{text "Xproperty_t2"}. We then proceed to show that @{text "amd2"} is valid with the
reasoning given above and use it to prove that there is now a dictatorship.
\<close>

lemma oap_t3:"\<lfloor>oap\<rfloor>\<^sub>t\<^sub>3" 
  using Xoap_t2 local_valid_def tnext_def t2_s_t3 by auto
lemma osp_t3:"\<lfloor>osp\<rfloor>\<^sub>t\<^sub>3" 
  using Xosp_t2 local_valid_def tnext_def t2_s_t3 by auto
lemma opr_t3:"\<lfloor>opr\<rfloor>\<^sub>t\<^sub>3"
  using Xopr_t2 local_valid_def tnext_def t2_s_t3 by auto
lemma rv_t3:"\<lfloor>rv\<rfloor>\<^sub>t\<^sub>3" 
  using Xrv_t2 local_valid_def tnext_def t2_s_t3 by auto
lemma osr_t3:"\<lfloor>osr\<rfloor>\<^sub>t\<^sub>3" 
  using Xosr_t2 local_valid_def tnext_def t2_s_t3 by auto
lemma psr_t3:"\<lfloor>psr\<rfloor>\<^sub>t\<^sub>3" 
  using Xpsr_t2 local_valid_def tnext_def t2_s_t3 by auto

lemma amd2_val_t3:"\<lfloor>amd2\<rfloor>\<^sub>t\<^sub>3" 
proof -
  have "\<lfloor>\<^bold>X(is_rat amd2)\<rfloor>\<^sub>t\<^sub>2"  
    using amd2_prop_t2 amd2_sup_rat_t2 local_valid_def tallB_s_def tall_s_def tand_def timp_def tnext_def psr_t2 
    by auto
  thus  "\<lfloor>amd2\<rfloor>\<^sub>t\<^sub>3" 
    using local_valid_def tallB_s_def tall_s_def timp_def tnext_def rv_t3 t2_s_t3 
    by auto
qed

(* Dictatorship at t3 *)

text\<open>\noindent %
Since @{text "amd2 \<equiv> is_leg P \<^bold>\<and> is_exe P \<^bold>\<and> is_jud P"} we can easily show that the condition for @{text "Dictatorship"}
is satisfied.
\<close>

theorem Dictatorship_t3:"\<lfloor>Dictatorship\<rfloor>\<^sub>t\<^sub>3"  
proof -
  have "\<lfloor>is_leg P \<^bold>\<and> is_exe P \<^bold>\<and> is_jud P\<rfloor>\<^sub>t\<^sub>3"
    using amd2_val_t3 amd2_def 
    by ( simp add: local_valid_def tand_def)
  thus "\<lfloor>Dictatorship\<rfloor>\<^sub>t\<^sub>3"
    by (meson Dictatorship_def local_valid_def)
qed

text\<open>\noindent %
To conclude we check for satisfiability again. 
\<close>

lemma T_basic_sat_t3: "True" nitpick[satisfy,user_axioms,show_all,card time = 4]oops

(*<*)
end
(*>*)