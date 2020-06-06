theory PreferenceLogicApplication1 imports PreferenceLogicBasics PreferenceLogicTests                    
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
(*values*)
type_synonym \<theta> = "p\<Rightarrow>\<sigma>" (*values: propositions (sets of words) w.r.t. a given party/contender*)
consts SECURITY::\<theta> LIBERTY::\<theta> EQUALITY::\<theta> UTILITY::\<theta>
consts STAB::\<theta> RELI::\<theta> 
consts WILL::\<theta> RESP::\<theta>
consts EQUI::\<theta> FAIR::\<theta>
consts EFFI::\<theta> GAIN::\<theta>

definition "VAL \<equiv> \<^bold>{WILL \<alpha>,RELI \<alpha>,RESP \<alpha>,EQUI \<alpha>,FAIR \<alpha>,EFFI \<alpha>,STAB \<alpha>,GAIN \<alpha>\<^bold>} \<^bold>\<union>
                   \<^bold>{WILL \<beta>,RELI \<beta>,RESP \<beta>,EQUI \<beta>,FAIR \<beta>,EFFI \<beta>,STAB \<beta>,GAIN \<beta>\<^bold>}"

axiomatization where
 V1: "\<lparr> SECURITY x | LIBERTY x | EQUALITY x | UTILITY x \<rparr>" and
 V2: "(SECURITY x \<^bold>\<or> (LIBERTY x \<^bold>\<or> (EQUALITY x \<^bold>\<or> UTILITY x))) = \<^bold>\<top>" and
 V3: "STAB x \<subseteq> SECURITY x" and V4:  "RELI x \<subseteq> SECURITY x" and
 V5: "WILL x \<subseteq> LIBERTY x"  and V6:  "RESP x \<subseteq> LIBERTY x" and
 V7: "EQUI x \<subseteq> EQUALITY x" and V8:  "FAIR x \<subseteq> EQUALITY x" and
 V9: "EFFI x \<subseteq> UTILITY x"  and V10: "GAIN x \<subseteq> UTILITY x" and 
 V11:"EQUI x \<subseteq> SECURITY x" and V12: "EFFI x \<subseteq> SECURITY x" and 
 V13:"FAIR x \<subseteq> LIBERTY x"  and V14: "GAIN x \<subseteq> LIBERTY x" and 
 V15:"RELI x \<subseteq> EQUALITY x" and V16: "RESP x \<subseteq> EQUALITY x" and 
 V17:"STAB x \<subseteq> UTILITY x"  and V18: "WILL x \<subseteq> UTILITY x" 
(*TODO: encode other dialectical relations between values (e.g. are RELI & STAB disjoint?)*)

(*kinds of situations*)
consts Animals :: \<sigma>  (*appropriation of animals in general*)
consts WildAnimals :: \<sigma>  (*appropriation of wild animals*)
consts DomesticAnimals :: \<sigma> (*appropriation of domestic animals*)
consts FoxHunting :: \<sigma> (*appropriation of foxes*)
(*...*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
W1: "\<lparr> DomesticAnimals | WildAnimals \<rparr>" and
W2: "WildAnimals \<subseteq> Animals" and
W3: "FoxHunting \<subseteq> WildAnimals" and
W4: "DomesticAnimals \<subseteq> Animals"
(*...*)

lemma True nitpick[satisfy] oops (*axiomatization is consistent*)

axiomatization where (*legal corpus*)
S1: "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{WILL x,STAB y,GAIN y\<^bold>}
                   in \<lfloor>Animals \<^bold>\<rightarrow>  (WILL x \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> (STAB y \<^bold>\<and> GAIN y))\<rfloor>" and
S2: "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{WILL x,STAB y\<^bold>}
                   in \<lfloor>WildAnimals \<^bold>\<rightarrow> (WILL x \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> STAB y)\<rfloor>" and
S3: "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{STAB x,RELI y,WILL y\<^bold>}
                   in \<lfloor>DomesticAnimals \<^bold>\<rightarrow> (STAB x \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> (RELI y \<^bold>\<and> WILL y))\<rfloor>"
(*...*)
lemma True nitpick[satisfy,show_all] oops (*axioms consistent - what is "Empty assignment"? *)

(* Suppose that \<alpha> represents Post  and \<beta> Pierson.
Post (\<alpha>) argument goes like this:
1) Post was chasing the fox
2) pursuit vests (ceteris paribus) property —i.e. WILL \<alpha> (Post's warrant)
3) Therefore, the fox belongs to Post

Pierson (\<beta>) argument says:
1) Pierson has corporal possession of the fox
2) corporal possession creates legal certainty (Pufendorf)  —i.e. STAB \<beta> (Pierson's warrant)
3) Therefore, the fox belongs to Pierson

The situational facts (here summarized as "FoxHunting") may entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "WildAnimals").
*)

(*Some tests:*)
lemma "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{WILL \<alpha>,STAB \<beta>\<^bold>}
                   in \<lfloor>FoxHunting \<^bold>\<rightarrow> (WILL \<alpha> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> STAB \<beta>)\<rfloor>" sledgehammer [remote_leo2] using S2 W3 by fastforce 
(* Above Pierson's warrant has preference over Post's as expected *)

lemma "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{WILL \<alpha>,STAB \<beta>\<^bold>}
                   in \<lfloor>FoxHunting \<^bold>\<rightarrow> (STAB \<alpha> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> WILL \<beta>)\<rfloor>" nitpick oops
lemma "let \<Gamma> = VAL \<^bold>\<midarrow> \<^bold>{WILL \<alpha>,STAB \<beta>\<^bold>}
                   in \<lfloor>Animals \<^bold>\<rightarrow> (STAB \<alpha>  \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> (RELI \<beta> \<^bold>\<and> GAIN \<beta>))\<rfloor>" nitpick oops
(*TODO: add some others, eventually without ceteris paribus (automated tools have a hard time here)*)

lemma "\<exists>P. P \<^bold>\<in> VAL" nitpick[satisfy]

end


