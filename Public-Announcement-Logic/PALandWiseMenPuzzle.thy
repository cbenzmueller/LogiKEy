theory PALandWiseMenPuzzle imports Main       (* Sebastian Reiche and Christoph Benzmüller, 2021 *)
begin
 (* Parameter settings for Nitpick *) nitpick_params[user_axioms=true, format=4, show_all]
  
 typedecl i (* Type of possible worlds *)
 type_synonym \<sigma> = "i\<Rightarrow>bool" (* \<D> *)
 type_synonym \<tau> = "\<sigma>\<Rightarrow>i\<Rightarrow>bool" (* Type of world depended formulas (truth sets) *) 
 type_synonym \<alpha> = "i\<Rightarrow>i\<Rightarrow>bool" (* Type of accessibility relations between world *)

 (* Some useful relations (for constraining accessibility relations) *)
 definition reflexive::"\<alpha>\<Rightarrow>bool" where "reflexive R \<equiv> \<forall>x. R x x"
 definition symmetric::"\<alpha>\<Rightarrow>bool" where "symmetric R \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"
 definition transitive::"\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
 definition euclidean::"\<alpha>\<Rightarrow>bool" where "euclidean R \<equiv> \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
 definition intersection_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "intersection_rel R Q \<equiv> \<lambda>u v. R u v \<and> Q u v"
 definition union_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "union_rel R Q \<equiv> \<lambda>u v. R u v \<or> Q u v"
 definition sub_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
 definition inverse_rel::"\<alpha>\<Rightarrow>\<alpha>" where "inverse_rel R \<equiv> \<lambda>u v. R v u"
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

 (* Agents *)
 consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>" (* Agents modeled as accessibility relations *)
 abbreviation  Agent ("\<A>") where "\<A> x \<equiv> x = a \<or> x = b \<or> x = c"
 axiomatization where
   alldifferent:  "\<not>(a = b) \<and> \<not>(a = c) \<and> \<not>(b = c)" and
   group_S5: "\<forall>i. \<A> i \<longrightarrow> (reflexive i \<and> transitive i \<and> euclidean i)"

 abbreviation EVR::"\<alpha>" ("EVR") where "EVR \<equiv> union_rel (union_rel a b) c"
 abbreviation prck::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^bold>\<lparr>_\<^bold>|_\<^bold>\<rparr>")
   where "\<^bold>C\<^bold>\<lparr>\<phi>\<^bold>|\<psi>\<^bold>\<rparr> \<equiv> \<lambda>W w. \<forall>v. \<not>(tc (intersection_rel EVR (\<lambda>u v. W v \<and> \<phi> W v)) w v) \<or> (\<psi> W v)"
 abbreviation DIS :: "\<alpha>" ("DIS") where "DIS \<equiv> intersection_rel (intersection_rel a b) c"

 (* Validity of \<tau>-type lifted PAL formulas *)
 abbreviation pvalid::"\<tau> \<Rightarrow> bool" ("\<^bold>\<lfloor>_\<^bold>\<rfloor>"[7]8) where "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor> \<equiv> \<forall>W.\<forall>w. W w \<longrightarrow> \<phi> W w"

 (* Agent Knowledge, Mutual Knowledge, Common Knowledge *)
 abbreviation agttknows::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K\<^sub>_ _") where "\<^bold>K\<^sub>r \<phi> \<equiv>  \<^bold>K r \<phi>" 
 abbreviation evrknows::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>E\<^sub>\<A> _") where "\<^bold>E\<^sub>\<A> \<phi> \<equiv>  \<^bold>K EVR \<phi>"
 abbreviation pcmn::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>\<A> _") where "\<^bold>C\<^sub>\<A> \<phi> \<equiv>  \<^bold>C\<^bold>\<lparr>\<^bold>\<top>\<^bold>|\<phi>\<^bold>\<rparr>"
 abbreviation disknows :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>D\<^sub>\<A> _") where "\<^bold>D\<^sub>\<A> \<phi> \<equiv> \<^bold>K DIS \<phi>"

 (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
 named_theorems Defs
 declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] euclidean_def[Defs] 
   intersection_rel_def[Defs] union_rel_def[Defs] sub_rel_def[Defs] inverse_rel_def[Defs] 
   tc_def[Defs] 

(***********************************************************************************************)
(*****                         Experiments and Wise Men Puzzle                             *****)
(***********************************************************************************************)
 (*Some useful lemmata *) 
 lemma trans_tc: "transitive (tc R)" unfolding Defs tc_def by metis
 lemma trans_inv_tc: "transitive (inverse_rel (tc R))" unfolding Defs tc_def by metis
 lemma sub_rel_tc: "symmetric R \<longrightarrow> (sub_rel R (inverse_rel (tc R)))" unfolding Defs tc_def by smt
 lemma sub_rel_tc_tc: "symmetric R \<longrightarrow> (sub_rel (tc R) (inverse_rel (tc R)))" 
   using sub_rel_def sub_rel_tc tc_def trans_inv_tc by fastforce
 lemma symm_tc: "symmetric R \<longrightarrow> symmetric (tc R)"  
   using inverse_rel_def sub_rel_def sub_rel_tc_tc symmetric_def by auto

 (* System K: is implied by the semantical embedding *)
 lemma tautologies: "\<^bold>\<lfloor>\<^bold>\<top>\<^bold>\<rfloor>" by auto
 lemma axiom_K: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i \<psi>))\<^bold>\<rfloor>" by auto 
 lemma modusponens: assumes 1: "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<^bold>\<rfloor>" and 2: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>\<psi>\<^bold>\<rfloor>" using 1 2 by auto  
 lemma necessitation: assumes 1: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<A> i \<Longrightarrow> \<^bold>\<lfloor>\<^bold>K\<^sub>i \<phi>\<^bold>\<rfloor>" using 1 by auto
 (* More axioms: implied by the semantical embedding  *)
 lemma axiom_T: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> \<phi>\<^bold>\<rfloor>" using group_S5 reflexive_def by blast
 lemma axiom_4: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<^bold>K\<^sub>i \<phi>))\<^bold>\<rfloor>" by (meson group_S5 transitive_def)
 lemma axiom_5: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>\<not>\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<^bold>\<not>\<^bold>K\<^sub>i \<phi>))\<^bold>\<rfloor>" by (metis euclidean_def group_S5)
 (*Reduction axioms: implied by the semantical embedding *)
 lemma atomic_permanence: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<^sup>Ap) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> \<^sup>Ap)\<^bold>\<rfloor>" by auto
 lemma conjunction: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<psi> \<^bold>\<and> \<chi>)) \<^bold>\<rightarrow> ((\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>) \<^bold>\<and> (\<^bold>[\<^bold>!\<phi>\<^bold>]\<chi>))\<^bold>\<rfloor>" by auto
 lemma part_func: "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<^bold>\<not>\<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>))\<^bold>\<rfloor>" by auto
 lemma action_knowledge: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>K\<^sub>i \<psi>)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>K\<^sub>i (\<phi> \<^bold>\<rightarrow> (\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>))))\<^bold>\<rfloor>" by auto
 lemma "\<^bold>\<lfloor>(\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<psi>\<^bold>\<rparr>)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>C\<^bold>\<lparr>\<phi>\<^bold>\<and>(\<^bold>[\<^bold>!\<phi>\<^bold>]\<chi>)\<^bold>|\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi>\<^bold>\<rparr>))\<^bold>\<rfloor>" 
   by (smt intersection_rel_def sub_rel_def tc_def transitive_def)

 (* Axiom schemes for RCK: implied by the semantical embedding *)
 lemma \<C>_normality: "\<^bold>\<lfloor>\<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rightarrow>\<psi>\<^bold>\<rparr> \<^bold>\<rightarrow>(\<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr> \<^bold>\<rightarrow> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<psi>\<^bold>\<rparr>)\<^bold>\<rfloor>" unfolding Defs by blast
 lemma mix_axiom1: "\<^bold>\<lfloor>\<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr> \<^bold>\<rightarrow> (\<^bold>E\<^sub>\<A> (\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>)))\<^bold>\<rfloor>" unfolding Defs by metis
 lemma mix_axiom2: "\<^bold>\<lfloor>(\<^bold>E\<^sub>\<A> (\<chi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<and> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>))) \<^bold>\<rightarrow> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" unfolding Defs (* timeout *) sorry
 lemma induction_axiom: "\<^bold>\<lfloor>((\<^bold>E\<^sub>\<A> (\<chi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<and> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi> \<^bold>\<rightarrow> (\<^bold>E\<^sub>\<A> (\<chi> \<^bold>\<rightarrow> \<phi>))\<^bold>\<rparr>) \<^bold>\<rightarrow> \<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>"
   unfolding Defs (* timeout *) sorry
 
 (* Necessitation rules: implied by the semantical embedding *)
 lemma announcement_nec: assumes 1: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<psi>\<^bold>]\<phi>\<^bold>\<rfloor>" using 1 by auto 
 lemma rkc_necessitation: assumes 1: "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor>" shows "\<^bold>\<lfloor>\<^bold>C\<^bold>\<lparr>\<chi>\<^bold>|\<phi>\<^bold>\<rparr>\<^bold>\<rfloor>" 
   by (metis 1 intersection_rel_def sub_rel_def tc_def transitive_def)

 (* Axiom schemes for Distributed Knowledge: implied by the semantical embedding *)
 lemma System_W: "\<A> i \<Longrightarrow> \<^bold>\<lfloor>(\<^bold>K\<^sub>i \<phi>) \<^bold>\<rightarrow> (\<^bold>D\<^sub>\<A> \<phi>)\<^bold>\<rfloor>" using intersection_rel_def by auto
 lemma System_K\<^sub>D: "\<^bold>\<lfloor>(\<^bold>D\<^sub>\<A> (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((\<^bold>D\<^sub>\<A> \<phi>) \<^bold>\<rightarrow> (\<^bold>D\<^sub>\<A> \<psi>))\<^bold>\<rfloor>" by blast
 lemma System_T\<^sub>D: "\<^bold>\<lfloor>(\<^bold>D\<^sub>\<A> \<phi>) \<^bold>\<rightarrow> \<phi>\<^bold>\<rfloor>" using group_S5 intersection_rel_def reflexive_def by auto
 lemma System_4\<^sub>D: "\<^bold>\<lfloor>(\<^bold>D\<^sub>\<A> \<phi>) \<^bold>\<rightarrow> (\<^bold>D\<^sub>\<A> (\<^bold>D\<^sub>\<A> \<phi>))\<^bold>\<rfloor>" by (smt group_S5 intersection_rel_def transitive_def)
 lemma System_5\<^sub>D: "\<^bold>\<lfloor>(\<^bold>\<not>\<^bold>D\<^sub>\<A> \<phi>) \<^bold>\<rightarrow> (\<^bold>D\<^sub>\<A> (\<^bold>\<not>\<^bold>D\<^sub>\<A> \<phi>))\<^bold>\<rfloor>"
   by (metis euclidean_def group_S5 intersection_rel_def)

 (* Further axioms: implied for atomic formulas, but not implied in general *)
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>\<^sup>Ap \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" by simp
 lemma "\<^bold>\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>(\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" by blast
 lemma "\<^bold>\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)
 lemma "\<^bold>\<lfloor>(\<^bold>K\<^sub>a \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" using group_S5 reflexive_def by auto
 lemma "\<^bold>\<lfloor>(\<^bold>K\<^sub>a \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)  
 lemma "\<^bold>\<lfloor>(\<^bold>K\<^sub>a \<^sup>Ap) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<^sup>Ap\<^bold>](\<^sup>Ap \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<^sup>Ap)\<^bold>\<rfloor>" using group_S5 reflexive_def by auto
 lemma "\<^bold>\<lfloor>(\<^bold>K\<^sub>a \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>[\<^bold>!\<phi>\<^bold>](\<phi> \<^bold>\<and> \<^bold>\<not>\<^bold>K\<^sub>a \<phi>)\<^bold>\<rfloor>" nitpick oops (* countermodel found *)

 (*** Encoding of the wise men puzzle in PAL ***)
 (* Choose CVC4 as smt solver *)  declare [[smt_solver=cvc4,smt_oracle,smt_timeout=60]]
 (* Common knowledge: At least one of a, b and c has a white spot *)
 consts ws::"\<alpha>\<Rightarrow>\<sigma>" 
 axiomatization where WM1: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^sup>Aws a \<^bold>\<or> \<^sup>Aws b \<^bold>\<or> \<^sup>Aws c)\<^bold>\<rfloor>" 

 axiomatization where
   (* Common knowledge: If x not has a white spot then y know this *)
   WM2ab: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ac: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ba: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2ca: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cb: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" 

 (* Positive introspection principles are implied *)
 lemma WM2ab': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^sup>Aws a)))\<^bold>\<rfloor>" using WM2ab group_S5 unfolding Defs by metis
 lemma WM2ac': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^sup>Aws a)))\<^bold>\<rfloor>" using WM2ac group_S5 unfolding Defs by metis
 lemma WM2ba': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^sup>Aws b)))\<^bold>\<rfloor>" using WM2ba group_S5 unfolding Defs by metis
 lemma WM2bc': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^sup>Aws b)))\<^bold>\<rfloor>" using WM2bc group_S5 unfolding Defs by metis
 lemma WM2ca': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^sup>Aws c)))\<^bold>\<rfloor>" using WM2ca group_S5 unfolding Defs by metis
 lemma WM2cb': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^sup>Aws c)))\<^bold>\<rfloor>" using WM2cb group_S5 unfolding Defs by metis

 (* Automated solutions of the Wise Men Puzzle *)
 theorem whitespot_c: 
     "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>a (\<^sup>Aws a)) \<^bold>\<or> (\<^bold>K\<^sub>a (\<^bold>\<not>\<^sup>Aws a)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>b (\<^sup>Aws b)) \<^bold>\<or> (\<^bold>K\<^sub>b (\<^bold>\<not>\<^sup>Aws b)))\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb group_S5 unfolding Defs by smt 

 theorem "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>a(\<^sup>Aws a)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>b(\<^sup>Aws b)\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb group_S5 unfolding Defs 
   by (smt (verit))

 (* Consistency confirmed by nitpick *)
 lemma True nitpick [satisfy] oops  (* model found *)

end