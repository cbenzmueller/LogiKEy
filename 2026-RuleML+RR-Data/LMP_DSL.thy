(* 
Luca Pasetto, Christoph Benzmüller, and Réka Markovich. 2026.
Right on Thought, Left Private: Reasoning about Mental Privacy in LogiKEy.
*)

section \<open>L2.1 Legal DSL for Mental Privacy and Freedom of Thought\<close>

text \<open>
  This theory defines the lightweight L2.1 legal DSL used in the paper.
  The DSL constructors are HOL definitions that expand to LMP formulas of type \<sigma>.
\<close>

theory LMP_DSL
  imports LMP
begin

nitpick_params[user_axioms=true,assms=true,expect=genuine,show_all,format=2,mono=false,dont_box]

text \<open>Access control of mental states.\<close>

definition CtrlB :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where
  "CtrlB a b \<psi> \<equiv>
     \<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K b (\<^bold>B a \<psi>)))))"

definition Ctrl3 :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where
  "Ctrl3 a b \<psi> \<equiv>
     \<^bold>\<diamond> (\<^bold>E a (
       (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K b (\<^bold>B a \<psi>)))) \<^bold>\<and>
       (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K b (\<^bold>B a (\<^bold>\<not> \<psi>))))) \<^bold>\<and>
       (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K b ((<\<^bold>B a> \<psi>) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not> \<psi>))))))
     ))"

text \<open>Claim-right to mental privacy.\<close>

definition StateMPB :: "ag \<Rightarrow> ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "StateMPB s c a \<psi> T \<equiv>
     \<lambda>w. \<forall>b. T b \<longrightarrow>
       (\<^bold>O[s\<rightarrow>a] (\<^bold>E s (\<^bold>O[c\<rightarrow>a] (\<^bold>E c (CtrlB a b \<psi>))))) w"

definition MPB :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "MPB c a \<psi> T \<equiv>
     \<lambda>w. \<forall>b. T b \<longrightarrow>
       (\<^bold>O[c\<rightarrow>a] (\<^bold>E c (CtrlB a b \<psi>))) w"

definition MP3 :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "MP3 c a \<psi> T \<equiv>
     \<lambda>w. \<forall>b. T b \<longrightarrow>
       (\<^bold>O[c\<rightarrow>a] (\<^bold>E c (Ctrl3 a b \<psi>))) w"

text \<open>Mental privacy violation checks.\<close>

definition MPLeakB :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where
  "MPLeakB a b \<psi> \<equiv> \<^bold>\<not> (CtrlB a b \<psi>)"

definition MPViolB :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "MPViolB c a \<psi> T \<equiv>
     (MPB c a \<psi> T) \<^bold>\<and>
     (\<lambda>w. \<exists>b. T b \<and> (MPLeakB a b \<psi>) w)"

text \<open>Direct interference with freedom of thought.\<close>

definition DirFoT :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where
  "DirFoT b a \<psi> \<equiv>
     (\<^bold>E b (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>B a \<psi>)))) \<^bold>\<or>
     (\<^bold>E b (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>B a (\<^bold>\<not> \<psi>))))) \<^bold>\<or>
     (\<^bold>E b (\<^bold>\<not> (\<^bold>\<diamond> ((<\<^bold>B a> \<psi>) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not> \<psi>))))))"

definition NoDirFoT :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where
  "NoDirFoT b a \<psi> \<equiv> \<^bold>\<not> (DirFoT b a \<psi>)"

text \<open>Claim-right to freedom of thought.\<close>

definition FoT :: "ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "FoT a \<psi> T \<equiv>
     \<lambda>w. \<forall>b. T b \<longrightarrow>
       (\<^bold>O[b\<rightarrow>a] (NoDirFoT b a \<psi>)) w"

text \<open>Freedom of thought violation checks.\<close>

definition FoTViol :: "ag \<Rightarrow> \<sigma> \<Rightarrow> (ag\<Rightarrow>bool) \<Rightarrow> \<sigma>" where
  "FoTViol a \<psi> T \<equiv>
     (FoT a \<psi> T) \<^bold>\<and>
     (\<lambda>w. \<exists>b. T b \<and> (DirFoT b a \<psi>) w)"

named_theorems LMP_DSL_Defs

declare
  LMP_Defs[LMP_DSL_Defs]
  CtrlB_def[LMP_DSL_Defs]
  Ctrl3_def[LMP_DSL_Defs]
  StateMPB_def[LMP_DSL_Defs]
  MPB_def[LMP_DSL_Defs]
  MP3_def[LMP_DSL_Defs]
  MPLeakB_def[LMP_DSL_Defs]
  MPViolB_def[LMP_DSL_Defs]
  DirFoT_def[LMP_DSL_Defs]
  NoDirFoT_def[LMP_DSL_Defs]
  FoT_def[LMP_DSL_Defs]
  FoTViol_def[LMP_DSL_Defs]

end
