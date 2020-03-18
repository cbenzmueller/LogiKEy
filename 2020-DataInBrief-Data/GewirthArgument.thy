theory GewirthArgument                    (* by David Fuenmayor and C. Benzmüller, 2019 *)
   imports Extended_CJ_DDL     
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3] 


section \<open>Gewith's Ethical Theory\<close>

type_synonym p = "e\<Rightarrow>m" (**Type for properties (function from individuals to sentence meanings)*)

(**ActsOnPurpose is a relational constant. (ActsOnPurpose A E) reads as "A is acting on purpose E":*)
consts ActsOnPurpose::"e\<Rightarrow>m\<Rightarrow>m" 
(**(NeedsForPurpose A P E) reads as "A needs to have property P in order to reach purpose E":*)
consts NeedsForPurpose::"e\<Rightarrow>p\<Rightarrow>m\<Rightarrow>m"

definition PPA:: "p" where "PPA a \<equiv> \<^bold>\<exists>E. ActsOnPurpose a E" (** Definition of PPA*)
axiomatization where essentialPPA: "\<lfloor>\<^bold>\<forall>a. PPA a \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>D(PPA a)\<rfloor>\<^sup>D" (**PPA is an essential property*)
lemma recognizeOtherPPA: "\<forall>c d. \<lfloor>PPA (Agent d)\<rfloor>\<^sub>d \<longrightarrow> \<lfloor>PPA (Agent d)\<rfloor>\<^sub>c" using essentialPPA by blast

consts Good::"e\<Rightarrow>m\<Rightarrow>m"
axiomatization where explGoodness1: "\<lfloor>\<^bold>\<forall>a P. ActsOnPurpose a P \<^bold>\<rightarrow> Good a P\<rfloor>\<^sup>D"
axiomatization where explGoodness2: "\<lfloor>\<^bold>\<forall>P M a. Good a P \<^bold>\<and> NeedsForPurpose a M P \<^bold>\<rightarrow> Good a (M a)\<rfloor>\<^sup>D"
axiomatization where explGoodness3: "\<lfloor>\<^bold>\<forall>\<phi> a. \<^bold>\<diamond>\<^sub>p\<phi> \<^bold>\<rightarrow> \<^bold>O\<langle>\<phi> | \<^bold>\<box>\<^sup>DGood a \<phi>\<rangle>\<rfloor>\<^sup>D"

consts FWB::"p" (**Enjoying freedom and well-being (FWB) is a property (i.e.~has type @{text "e\<Rightarrow>m"})*)

axiomatization where
explicationFWB1: "\<lfloor>\<^bold>\<forall>P a. NeedsForPurpose a FWB P\<rfloor>\<^sup>D"
axiomatization where explicationFWB2: "\<lfloor>\<^bold>\<forall>a. \<^bold>\<diamond>\<^sub>p FWB a\<rfloor>\<^sup>D"  
axiomatization where explicationFWB3: "\<lfloor>\<^bold>\<forall>a. \<^bold>\<diamond>\<^sub>p \<^bold>\<not>FWB a\<rfloor>\<^sup>D"  

lemma "\<lfloor>\<^bold>O\<^sub>i\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sub>p\<phi>\<rfloor>" using sem_5ab by simp
axiomatization where OIOAC: "\<lfloor>\<^bold>O\<^sub>i\<phi> \<^bold>\<rightarrow> \<^bold>O\<^sub>i(\<^bold>\<diamond>\<^sub>a\<phi>)\<rfloor>\<^sup>D"

consts InterferesWith::"e\<Rightarrow>m\<Rightarrow>m"
axiomatization where explicationInterference: "\<lfloor>(\<^bold>\<exists>b. InterferesWith b \<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<diamond>\<^sub>a\<phi>\<rfloor>"
lemma "\<lfloor>\<^bold>\<forall>a. (\<^bold>\<exists>b. InterferesWith b (FWB a)) \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<diamond>\<^sub>a(FWB a)\<rfloor>" using explicationInterference by blast
lemma InterferenceWithFWB: "\<lfloor>\<^bold>\<forall>a.  \<^bold>\<diamond>\<^sub>a(FWB a) \<^bold>\<leftrightarrow> (\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (FWB a))\<rfloor>" using explicationInterference by blast

definition RightTo::"e\<Rightarrow>(e\<Rightarrow>m)\<Rightarrow>m" where "RightTo a \<phi> \<equiv> \<^bold>O\<^sub>i(\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (\<phi> a))"

(**Axiom consistency checked: Nitpick finds a two-world model (card w=2)*)
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 2] oops

section \<open>Gewirth's Argument for the PGC\<close>

(**Following Beyleveld's summary, the main steps of the argument are (with original numbering): *)
(**(1) I act voluntarily for some (freely chosen) purpose E (equivalent --by definition-- to: I am a PPA).*)
(**(2) E is (subjectively) good (i.e.~I value E proactively).*)
(**(3) My freedom and well-being (FWB) are generically necessary conditions of my agency (i.e.~I need them to achieve any purpose whatsoever).*)
(**(4) My FWB are necessary goods (at least for me).*)
(**(5) I have (maybe nobody else does) a claim right to my FWB.*)
(**(13) Every PPA has a claim right to their FWB.*)

(**The following is a formalized proof for the main conclusion of Gewirth's argument, which 
asserts that the following sentence is valid from every PPA's standpoint: "Every PPA has a 
claim right to its freedom and well-being (FWB)" *)
theorem PGC: shows "\<lfloor>\<^bold>\<forall>x. PPA x \<^bold>\<rightarrow> (RightTo x FWB)\<rfloor>\<^sup>D"
proof - 
 {fix C::c (**'C' is some arbitrarily chosen context (agent's perspective)*)
   {fix I::"e" (**'I' is some arbitrarily chosen individual (agent's perspective)*)
     {fix E::m (**'E' is some arbitrarily chosen purpose*)
      { assume P1: "\<lfloor>ActsOnPurpose I E\<rfloor>\<^sub>C" (**(1) I act voluntarily on purpose E:*)
           (**(1a) I am a PPA:*)
        from P1 have P1a: "\<lfloor>PPA I\<rfloor>\<^sub>C" using PPA_def by auto
           (**(2) purpose E is good for me:*)
        from P1 have C2: "\<lfloor>Good I E\<rfloor>\<^sub>C" using explGoodness1 essentialPPA by meson       
           (**(3) I need FWB for any purpose whatsoever:*)
        from explicationFWB1 have C3: "\<lfloor>\<^bold>\<forall>P. NeedsForPurpose I FWB P\<rfloor>\<^sup>D" by simp
        hence "\<exists>P.\<lfloor>Good I P \<^bold>\<and> NeedsForPurpose I FWB P\<rfloor>\<^sup>D" 
             using explicationFWB2 explGoodness3 sem_5ab by blast
           (**FWB is (a priori) good for me (in a kind of definitional sense):*)
        hence "\<lfloor>Good I (FWB I)\<rfloor>\<^sup>D" using explGoodness2 by blast       
           (**(4) FWB is an (a priori) necessary good for me:*)
        hence C4: "\<lfloor>\<^bold>\<box>\<^sup>D(Good I (FWB I))\<rfloor>\<^sub>C" by simp  
         (**I ought to pursue my FWB on the condition that I consider it a necessary good:*)
        have "\<lfloor>\<^bold>O\<langle>FWB I | \<^bold>\<box>\<^sup>D(Good I) (FWB I)\<rangle>\<rfloor>\<^sub>C" using explGoodness3 explicationFWB2 by blast       
           (**There is an (other-directed) obligation to my FWB:*)
        hence "\<lfloor>\<^bold>O\<^sub>i(FWB I)\<rfloor>\<^sub>C" using explicationFWB2 explicationFWB3 C4 CJ_14p by fastforce        
           (**It must therefore be the case that my FWB is possible:*)
        hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<diamond>\<^sub>a(FWB I))\<rfloor>\<^sub>C" using OIOAC by simp       
           (**There is an obligation for others not to interfere with my FWB:*)
        hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<forall>a. \<^bold>\<not>InterferesWith a (FWB I))\<rfloor>\<^sub>C" using InterferenceWithFWB by simp        
           (**(5) I have a claim right to my FWB:*)
        hence C5: "\<lfloor>RightTo I FWB\<rfloor>\<^sub>C" using RightTo_def by simp }
      (**I have a claim right to my FWB (since I act on some purpose E):*) 
    hence "\<lfloor>ActsOnPurpose I E \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" by (rule impI) }
      (** "allI" is the logical generalization rule: all-quantifier introduction*)
    hence "\<lfloor>\<^bold>\<forall>P. ActsOnPurpose I P \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" by (rule allI)    
      (**I have a claim right to my FWB since I am a PPA:*)
    hence "\<lfloor>PPA I \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" using PPA_def by simp }
    (**Every agent has a claim right to its FWB since it is a PPA:*)
  hence "\<forall>x. \<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sub>C" by simp }
    (**(13) For every perspective C: every agent has a claim right to its FWB:*)
  thus C13: "\<forall>C. \<lfloor>\<^bold>\<forall>x. PPA x \<^bold>\<rightarrow> (RightTo x FWB)\<rfloor>\<^sub>C" by (rule allI)  
qed

(**The following is a weaker variant of PGC: the agent of some context claims rights to FWB if it holds itself as a PPA.*)
lemma PGC_weak: "\<forall>C. \<lfloor>PPA (Agent C) \<^bold>\<rightarrow> (RightTo (Agent C) FWB)\<rfloor>\<^sub>C" using PGC by simp

section \<open>An example\<close>

(**In the following, we illustrate how to draw some inferences building upon Gewirth's PGC.
Note that all theorems below can be proven using Isabelle's term rewriting engine.*)

consts X::c (**Context of use X (to which a certain speaker agent corresponds)*)
consts Y::c (**Context of use Y (to which another speaker agent corresponds)*)

(**The agent (of context) X holds itself as a PPA:*)
axiomatization where AgentX_X_PPA: "\<lfloor>PPA (Agent X)\<rfloor>\<^sub>X"

(**The agent (of another context) Y holds the agent (of context) X  as a PPA:*)
lemma AgentY_X_PPA: "\<lfloor>PPA (Agent X)\<rfloor>\<^sub>Y" using AgentX_X_PPA recognizeOtherPPA by simp

(**Now the agent (of context) Y holds itself as a PPA: *)
axiomatization where AgentY_Y_PPA: "\<lfloor>PPA (Agent Y)\<rfloor>\<^sub>Y"

(**The agent Y claims a right to FWB:*)
lemma AgentY_Y_FWB: "\<lfloor>RightTo (Agent Y) FWB\<rfloor>\<^sub>Y" using AgentY_Y_PPA PGC_weak by simp

(**The agent Y accepts X claiming a right to FWB:*)
lemma AgentY_X_FWB: "\<lfloor>RightTo (Agent X) FWB\<rfloor>\<^sub>Y" using AgentY_X_PPA PGC by simp

(**The agent Y accepts an (other-directed) obligation of non-interference with X's FWB:*)
lemma AgentY_NonInterference_X_FWB: "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<forall>z. \<^bold>\<not>InterferesWith z (FWB (Agent X)))\<rfloor>\<^sub>Y" using AgentY_X_FWB RightTo_def by simp

(**Axiom consistency checked: Nitpick finds a two-world model (card w=2).*)
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 2] oops

end
