theory PreferenceLogicApplication2 imports PreferenceLogicBasics PreferenceLogicTests                    
begin
(*some conceptually unimportant declarations of defaults for tools*) 
nitpick_params[assms=true,user_axioms=true,expect=genuine,show_all,format=3] 

(***** proof of concept formalization of ethical value ontology *****)

(*useful to encode mutual disjointness of propositions, etc.*)
abbreviation disj2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w))" 
abbreviation disj3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>|\<gamma>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w)\<and>(\<gamma> w))"
abbreviation disj4::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_|_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>|\<gamma>|\<eta>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w)\<and>(\<gamma> w)\<and>(\<eta> w))"
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")  where "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 
abbreviation diff::"\<pi>\<Rightarrow>\<pi>\<Rightarrow>\<pi>" ("_\<^bold>\<midarrow>_")  where  "\<Gamma> \<^bold>\<midarrow> \<Gamma>' \<equiv> \<lambda>\<phi>. (\<phi> \<^bold>\<in> \<Gamma>) \<and> \<not>(\<phi> \<^bold>\<in> \<Gamma>')"
(*TODO: discover a more elegant way to do this:*)
abbreviation mkSet4::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_,_,_\<^bold>}")  where
 "\<^bold>{a,b,c,d\<^bold>} \<equiv> \<lambda>x. x=a \<or> x=b \<or> x=c \<or> x=d"
abbreviation mkSet5::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_,_,_,_\<^bold>}")  where
 "\<^bold>{a,b,c,d,e\<^bold>} \<equiv> \<lambda>x. x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e"
abbreviation mkSet8::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<pi>" ("\<^bold>{_,_,_,_,_,_,_,_\<^bold>}")  where
 "\<^bold>{a,b,c,d,e,f,g,h\<^bold>} \<equiv> \<lambda>x. x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=g \<or> x=h"



datatype p = \<alpha> | \<beta> (*parties/contenders*)

datatype VAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype SUBVAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

consts V::"p=>VAL\<Rightarrow>\<sigma>" 
consts SV::"p=>SUBVAL\<Rightarrow>\<sigma>" 

axiomatization where
 V1:"\<lfloor>(V x SECURITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(V x LIBERTY)\<rfloor>" and
 V2:"\<lfloor>(V x EQUALITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(V x UTILITY)\<rfloor>" and

 V3:"\<lfloor>(V x SECURITY) \<^bold>\<leftrightarrow> ((SV x RELI) \<^bold>\<or> (SV x STAB))\<rfloor>" and
 V4:"\<lfloor>(V x EQUALITY) \<^bold>\<leftrightarrow> ((SV x EQUI) \<^bold>\<or> (SV x FAIR))\<rfloor>" and
 V5:"\<lfloor>(V x LIBERTY)  \<^bold>\<leftrightarrow> ((SV x RESP) \<^bold>\<or> (SV x WILL))\<rfloor>" and
 V6:"\<lfloor>(V x UTILITY)  \<^bold>\<leftrightarrow> ((SV x GAIN) \<^bold>\<or> (SV x EFFI))\<rfloor>" 


lemma True nitpick[satisfy] oops
lemma "\<exists>x. \<lfloor>((SV x GAIN) \<^bold>\<and> ((SV x STAB) \<^bold>\<and> (SV x WILL)))\<rfloor>" nitpick[satisfy] oops
lemma "\<not>(\<exists>x. \<lfloor>((SV x GAIN) \<^bold>\<and> ((SV x STAB) \<^bold>\<and> (SV x WILL)))\<rfloor>)" using V1 V3 V5 by blast
lemma "\<exists>x. \<lfloor>((SV x RESP) \<^bold>\<and> ((SV x GAIN) \<^bold>\<and> (SV x WILL)))\<rfloor>" nitpick[satisfy] oops
lemma "\<exists>x. \<lfloor>((SV x RESP) \<^bold>\<and> ((SV x GAIN) \<^bold>\<and> \<^bold>\<not>(SV x WILL)))\<rfloor>" nitpick[satisfy] oops



(*kinds of situations*)
consts Animals :: "p\<Rightarrow>\<sigma>"  (*appropriation of animals in general*)
consts WildAnimals :: "p\<Rightarrow>\<sigma>"  (*appropriation of wild animals*)
consts DomesticAnimals :: "p\<Rightarrow>\<sigma>" (*appropriation of domestic animals*)
consts FoxHunting :: "p\<Rightarrow>\<sigma>" (*appropriation of foxes*)
(*...*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
W1: "\<lparr> DomesticAnimals x | WildAnimals x \<rparr>" and
W2: "WildAnimals x \<subseteq> Animals x" and
W3: "FoxHunting x \<subseteq> WildAnimals x" and
W4: "DomesticAnimals x \<subseteq> Animals x"
(*...*)

lemma True nunchaku[satisfy] nitpick[satisfy] oops (*axiomatization is consistent*)

axiomatization where (*legal corpus*)
S1: "\<lfloor>Animals x          \<^bold>\<rightarrow>  ((SV x WILL) \<^bold>\<preceq>\<^sub>A\<^sub>E ((SV x STAB) \<^bold>\<and> (SV x GAIN)))\<rfloor>" and
S2: "\<lfloor>WildAnimals x      \<^bold>\<rightarrow>  ((SV x WILL) \<^bold>\<preceq>\<^sub>A\<^sub>E (SV x STAB))\<rfloor>" and
S3: "\<lfloor>DomesticAnimals x  \<^bold>\<rightarrow>  ((SV x STAB) \<^bold>\<preceq>\<^sub>A\<^sub>E ((SV x RELI) \<^bold>\<and> (SV x WILL)))\<rfloor>" 

lemma True nitpick[satisfy] oops (*axioms consistent*)

(* Suppose that \<alpha> represents Post  and \<beta> Pierson.
Post (\<alpha>) argument goes like this:
1) Post was chasing the fox
2) pursuit vests (ceteris paribus) property —i.e. WILL \<alpha> (Post's warrant)
3) Therefore, the fox belongs to Post
*)

(*
Pierson (\<beta>) argument says:
1) Pierson has corporal possession of the fox
2) corporal possession creates legal certainty (Pufendorf)  —i.e. STAB \<beta> (Pierson's warrant)
3) Therefore, the fox belongs to Pierson

The situational facts (here summarized as "FoxHunting") may entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "WildAnimals").
*)

lemma "\<lfloor>FoxHunting x \<^bold>\<rightarrow> ((SV x WILL) \<^bold>\<preceq>\<^sub>A\<^sub>E (SV x  STAB))\<rfloor>" sledgehammer using S2 W3 by blast 
lemma "\<lfloor>DomesticAnimals x \<^bold>\<rightarrow> ((SV x WILL) \<^bold>\<preceq>\<^sub>A\<^sub>E (SV x  STAB))\<rfloor>"  nitpick[satisfy] nitpick oops
lemma "\<lfloor>Animals x \<^bold>\<rightarrow> ((SV x WILL) \<^bold>\<preceq>\<^sub>A\<^sub>E ((SV x RELI) \<^bold>\<and> (SV x GAIN)))\<rfloor>"  nitpick[satisfy] nitpick oops

(* lemma "\<lfloor>FoxHunting \<alpha> \<^bold>\<and> DomesticAnimals \<beta>\<rfloor>" nitpick[satisfy] nitpick oops *)


end


