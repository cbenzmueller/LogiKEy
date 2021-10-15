theory PALandWiseMenPuzzle2021_4Agents_New imports Main    (* Christoph Benzmüller and Sebastian Reiche, 2021 *)

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
 definition bigunion_rel::"(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<alpha>" ("\<^bold>\<Union>_") where "\<^bold>\<Union> X \<equiv> \<lambda>u v. \<exists>R. (X R) \<and> (R u v)"
 definition bigintersection_rel::"(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<alpha>" ("\<^bold>\<Inter>_") where "\<^bold>\<Inter> X \<equiv> \<lambda>u v. \<forall>R. (X R) \<longrightarrow> (R u v)"

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
 abbreviation  "EVR A \<equiv> \<^bold>\<Union> A"
 abbreviation  "DIS A \<equiv> \<^bold>\<Inter> A"
 abbreviation agttknows::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K\<^sub>_ _") where "\<^bold>K\<^sub>r \<phi> \<equiv>  \<^bold>K r \<phi>" 
 abbreviation evrknows::"(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>E\<^sub>_ _") where "\<^bold>E\<^sub>A \<phi> \<equiv>  \<^bold>K (EVR A) \<phi>"
 abbreviation prck::"(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_\<^bold>\<lparr>_\<^bold>|_\<^bold>\<rparr>")
   where "\<^bold>C\<^sub>A\<^bold>\<lparr>\<phi>\<^bold>|\<psi>\<^bold>\<rparr> \<equiv> \<lambda>W w. \<forall>v. \<not>(tc (intersection_rel (EVR A) (\<lambda>u v. W v \<and> \<phi> W v)) w v) \<or> (\<psi> W v)"
 abbreviation pcmn::"(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_ _") where "\<^bold>C\<^sub>A \<phi> \<equiv>  \<^bold>C\<^sub>A\<^bold>\<lparr>\<^bold>\<top>\<^bold>|\<phi>\<^bold>\<rparr>"
 abbreviation disknows :: "(\<alpha>\<Rightarrow>bool)\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>D\<^sub>_ _") where "\<^bold>D\<^sub>A \<phi> \<equiv> \<^bold>K (DIS A) \<phi>"

 (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
 named_theorems Defs
 declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] euclidean_def[Defs] 
   intersection_rel_def[Defs] union_rel_def[Defs] sub_rel_def[Defs] inverse_rel_def[Defs] 
   bigunion_rel_def[Defs] tc_def[Defs]

 (***********************************************************************************************)
 (*****                        Wise Men Puzzle with 4 Agents                                *****)
 (***********************************************************************************************)
 (* Agents *)
 consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>" d::"\<alpha>" (* Agents modeled as accessibility relations *)
 abbreviation  Agent::"\<alpha>\<Rightarrow>bool" ("\<A>") where "\<A> x \<equiv> x = a \<or> x = b \<or> x = c \<or> x = d"
 axiomatization where  group_S5: "\<forall>i. \<A> i \<longrightarrow> (reflexive i \<and> transitive i \<and> euclidean i)"

 (*** Encoding of the wise men puzzle in PAL ***)
 (* Common knowledge: At least one of a, b, c and d has a white spot *)
 consts ws::"\<alpha>\<Rightarrow>\<sigma>" 
 axiomatization where WM1: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^sup>Aws a \<^bold>\<or> \<^sup>Aws b \<^bold>\<or> \<^sup>Aws c \<^bold>\<or> \<^sup>Aws d)\<^bold>\<rfloor>" 

 axiomatization where
   (* Common knowledge: If x not has a white spot then y know this *)
   WM2ab: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ac: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ad: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ba: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bd: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2ca: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cb: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cd: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2da: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" and
   WM2db: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" and
   WM2dc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" 


 (* Automated solutions of the Wise Men Puzzle with 4 Agents*)
 theorem whitespot_c_1: "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>a(\<^sup>Aws a)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>b(\<^sup>Aws b)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>c(\<^sup>Aws c)\<^bold>](\<^bold>K\<^sub>d (\<^sup>Aws d))))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb WM2da WM2db WM2dc
   unfolding Defs
   by (smt (verit))

 theorem whitespot_c_2: 
     "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>a (\<^sup>Aws a)) \<^bold>\<or> (\<^bold>K\<^sub>a (\<^bold>\<not>\<^sup>Aws a)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>b (\<^sup>Aws b)) \<^bold>\<or> (\<^bold>K\<^sub>b (\<^bold>\<not>\<^sup>Aws b)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>c (\<^sup>Aws c)) \<^bold>\<or> (\<^bold>K\<^sub>c (\<^bold>\<not>\<^sup>Aws c)))\<^bold>](\<^bold>K\<^sub>d (\<^sup>Aws d))))\<^bold>\<rfloor>" 
   using whitespot_c_1 
   unfolding Defs  sledgehammer[verbose]()  (* proof found *)
   (* reconstruction timeout *)
   by (smt (verit)) 
   oops


 (* Consistency confirmed by nitpick *)
 lemma True nitpick [satisfy] oops  (* model found *)

end