(* Sebastian Reiche and Christoph Benzmüller, 2021 *)
theory PAL_definitions imports Main

begin
 typedecl i (* Type of possible worlds *)
 type_synonym \<sigma> = "i\<Rightarrow>bool" (* \<D> *)
 type_synonym \<tau> = "\<sigma>\<Rightarrow>i\<Rightarrow>bool" (* Type of world depended formulas (truth sets) *) 
 type_synonym \<alpha> = "i\<Rightarrow>i\<Rightarrow>bool" (* Type of accessibility relations between world *)
 type_synonym \<rho> = "\<alpha>\<Rightarrow>bool" (* Type of groups of agents *)

 (* Some useful relations (for constraining accessibility relations) *)
 definition reflexive::"\<alpha>\<Rightarrow>bool" where "reflexive R \<equiv> \<forall>x. R x x"
 definition symmetric::"\<alpha>\<Rightarrow>bool" where "symmetric R \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"
 definition transitive::"\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
 definition euclidean::"\<alpha>\<Rightarrow>bool" where "euclidean R \<equiv> \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
 definition intersection_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "intersection_rel R Q \<equiv> \<lambda>u v. R u v \<and> Q u v"
 definition union_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "union_rel R Q \<equiv> \<lambda>u v. R u v \<or> Q u v"
 definition sub_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
 definition inverse_rel::"\<alpha>\<Rightarrow>\<alpha>" where "inverse_rel R \<equiv> \<lambda>u v. R v u"
 definition big_union_rel::"\<rho>\<Rightarrow>\<alpha>" where "big_union_rel X \<equiv> \<lambda>u v. \<exists>R. (X R) \<and> (R u v)"
 definition big_intersection_rel::"\<rho>\<Rightarrow>\<alpha>"
   where "big_intersection_rel X \<equiv> \<lambda>u v. \<forall>R. (X R) \<longrightarrow> (R u v)"

 (*In HOL the transitive closure of a relation can be defined in a single line.*)
 definition tc::"\<alpha>\<Rightarrow>\<alpha>" where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"

 (* Lifted HOMML connectives for PAL *)
 abbreviation patom::"\<sigma>\<Rightarrow>\<tau>" ("\<^sup>A_"[79]80) where "\<^sup>Ap \<equiv> \<lambda>W w. W w \<and> p w"
 abbreviation ptop::"\<tau>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>W w. True" 
 abbreviation pneg::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>W w. \<not>(\<phi> W w)" 
 abbreviation pand::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<and> (\<psi> W w)"   
 abbreviation por::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<or> (\<psi> W w)"   
 abbreviation pimp::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longrightarrow> (\<psi> W w)"  
 abbreviation pequ::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longleftrightarrow> (\<psi> W w)"
 abbreviation pknow::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K_ _") where "\<^bold>K r \<phi> \<equiv> \<lambda>W w.\<forall>v. (W v \<and> r w v) \<longrightarrow> (\<phi> W v)"
 abbreviation ppal::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>[\<^bold>!_\<^bold>]_") where "\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longrightarrow> (\<psi> (\<lambda>z. W z \<and> \<phi> W z) w)"

 (* Validity of \<tau>-type lifted PAL formulas *)
 abbreviation pvalid::"\<tau> \<Rightarrow> bool" ("\<^bold>\<lfloor>_\<^bold>\<rfloor>"[7]8) where "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor> \<equiv> \<forall>W.\<forall>w. W w \<longrightarrow> \<phi> W w"

 (* Agent Knowledge, Mutual Knowledge, Common Knowledge *)
 abbreviation EVR::"\<rho>\<Rightarrow>\<alpha>" where "EVR A \<equiv> big_union_rel A"
 abbreviation DIS::"\<rho>\<Rightarrow>\<alpha>" where "DIS A \<equiv> big_intersection_rel A"
 abbreviation agttknows::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K\<^sub>_ _") where "\<^bold>K\<^sub>r \<phi> \<equiv>  \<^bold>K r \<phi>" 
 abbreviation evrknows::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>E\<^sub>_ _") where "\<^bold>E\<^sub>A \<phi> \<equiv>  \<^bold>K (EVR A) \<phi>"
 abbreviation prck::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_\<^bold>\<lparr>_\<^bold>|_\<^bold>\<rparr>")
   where "\<^bold>C\<^sub>A\<^bold>\<lparr>\<phi>\<^bold>|\<psi>\<^bold>\<rparr> \<equiv> \<lambda>W w. \<forall>v. \<not>(tc (intersection_rel (EVR A) (\<lambda>u v. W v \<and> \<phi> W v)) w v) \<or> (\<psi> W v)"
 abbreviation pcmn::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_ _") where "\<^bold>C\<^sub>A \<phi> \<equiv>  \<^bold>C\<^sub>A\<^bold>\<lparr>\<^bold>\<top>\<^bold>|\<phi>\<^bold>\<rparr>"
 abbreviation disknows :: "\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>D\<^sub>_ _") where "\<^bold>D\<^sub>A \<phi> \<equiv> \<^bold>K (DIS A) \<phi>"

 (* S5 principles for the agent’saccessibility relations *)
 abbreviation S5Agent::"\<alpha>\<Rightarrow>bool"
   where  "S5Agent i \<equiv> reflexive i \<and> transitive i \<and> euclidean i"
 abbreviation S5Agents::"\<rho>\<Rightarrow>bool"
   where "S5Agents A \<equiv> \<forall>i. (A i \<longrightarrow> S5Agent i)"

 (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
 named_theorems Defs
 declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] euclidean_def[Defs] 
   intersection_rel_def[Defs] union_rel_def[Defs] sub_rel_def[Defs] inverse_rel_def[Defs] 
   big_union_rel_def[Defs] big_intersection_rel_def[Defs] tc_def[Defs]

 (* Consistency confirmed by nitpick *)
 lemma True nitpick [satisfy,show_all] oops (* model found *)
end





