theory Extended_CJ_DDL                    (*David Fuenmayor and C. Benzmüller, 2019*)
  imports CJ_DDLplus
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3]


section \<open>Extending the Carmo and Jones DDL Logical Framework\<close>

subsection \<open>Context Features\<close>

(**To keep things simple (and relevant for our task) we restrict ourselves to representing a context c as the pair: @{text "\<langle>Agent(c), World(c)\<rangle>"}.
For this purpose we represent the functional concepts "Agent" and "World" as logical constants.*)
consts Agent::"c\<Rightarrow>e"  (**function retrieving the agent corresponding to context c*)   
consts World::"c\<Rightarrow>w"  (**function retrieving the world corresponding to context c*)

subsection \<open>Logical Validity\<close>

(**Kaplan's notion of (context-dependent) logical truth for a sentence corresponds to its (context-sensitive) formula
(of type @{text "c\<Rightarrow>w\<Rightarrow>bool"} i.e. m) being true in the given context and at its corresponding world.*)
abbreviation ldtruectx::"m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>_") where "\<lfloor>\<phi>\<rfloor>\<^sub>c \<equiv> \<phi> c (World c)"

(**Kaplan's LD notion of logical validity for a sentence corresponds to its being true in all contexts.
This notion is also known as indexical validity.*)
abbreviation ldvalid::"m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>D") where "\<lfloor>\<phi>\<rfloor>\<^sup>D \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sub>c"

(**Here we show that indexical validity is indeed weaker than its classical modal counterpart (truth at all worlds for all contexts):*)
lemma "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>A\<rfloor>\<^sup>D" by simp
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>A\<rfloor>" nitpick oops (**countermodel found*)

(**Here we show that the interplay between indexical validity and the DDL modal and deontic operators does not
result in modal collapse.*)
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>aP\<rfloor>\<^sup>D" nitpick oops
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aP\<rfloor>\<^sup>D" nitpick oops

(**Next we show that the necessitation rule does not work for indexical validity (in contrast to classical modal validity as defined for DDL).*)
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>\<^sup>D"  nitpick oops
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>pA\<rfloor>\<^sup>D" nitpick oops

(**The following operator above is not part of the original Kaplan's LD and has been added
by us in order to better highlight some semantic features of our formalisation of Gewirth's argument in the next section and to being able to
use the necessitation rule for some inference steps. This is used to model a kind of logical-indexical necessity in contrast
to the alethic necessity shown above.*)
abbreviation ldvalidbox :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sup>D_" [52]53) where "\<^bold>\<box>\<^sup>D\<phi> \<equiv> \<lambda>c w. \<lfloor>\<phi>\<rfloor>\<^sup>D" (**note the D superscript*)
lemma "\<lfloor>\<^bold>\<box>\<^sup>D\<phi>\<rfloor>\<^sub>C \<equiv> \<forall>c.\<lfloor>\<phi>\<rfloor>\<^sub>c" by simp (**works analogously to the box operator in modal logic S5*)

(**The necessitation rule works for the combination of indexical validity with the previous operator, as intended.*)
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sup>DA\<rfloor>\<^sup>D"  by simp

subsection \<open>Quantification\<close>
(** We also enrich our logic with (higher-order) quantifiers (using parameterized types).*)
abbreviation mforall::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>c w.\<forall>x. (\<Phi> x c w)"
abbreviation mexists::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>c w.\<exists>x. (\<Phi> x c w)"    
abbreviation mforallBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. (\<phi> x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexistsBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. (\<phi> x) \<equiv> \<^bold>\<exists>\<phi>"

(*<*)
end
(*>*)