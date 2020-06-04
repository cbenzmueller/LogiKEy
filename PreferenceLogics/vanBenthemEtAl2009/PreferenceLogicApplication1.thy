theory PreferenceLogicApplication1 imports PreferenceLogicBasics PreferenceLogicTests                    
begin
(*some conceptually unimportant declarations of defaults for tools*) 
nitpick_params[assms=true,user_axioms=true,expect=genuine,format=3] 

(***** proof of concept formalization of ethical value ontology *****)

(*useful to encode mutual disjointness of propositions, etc.*)
abbreviation disj2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w))" 
abbreviation disj3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>|\<gamma>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w)\<and>(\<gamma> w))"
abbreviation disj4::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("\<lparr>_|_|_|_\<rparr>")  where "\<lparr>\<alpha>|\<beta>|\<gamma>|\<eta>\<rparr> \<equiv> \<not>(\<exists>w.(\<alpha> w)\<and>(\<beta> w)\<and>(\<gamma> w)\<and>(\<eta> w))"
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")  where "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 
(*values*)
consts EFFI :: \<sigma> GAIN :: \<sigma>
consts STAB :: \<sigma> RELI :: \<sigma> 
consts WILL :: \<sigma> RESP :: \<sigma>
consts EQUI :: \<sigma> FAIR :: \<sigma>
(*TODO: encode dialectical relations between values*)

(*kinds of situations*)
consts Animals :: \<sigma>  (*appropriation of animals in general*)
consts WildAnimals :: \<sigma>  (*appropriation of wild animals*)
consts DomesticAnimals :: \<sigma> (*appropriation of domestic animals*)
consts FoxHunting :: \<sigma> (*appropriation of foxes*)
(*...*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
ax_1: "\<lparr> DomesticAnimals | WildAnimals \<rparr>" and
ax_2: "WildAnimals \<subseteq> Animals" and
ax_3: "FoxHunting \<subseteq> WildAnimals" and
ax_4: "DomesticAnimals \<subseteq> Animals"

lemma True nitpick[satisfy] oops (*axiomatization is consistent*)

(* abbreviation "def\<equiv>\<lfloor>Animals \<^bold>\<rightarrow>  (WILL \<^bold>\<preceq>\<^sub>A\<^sub>A (STAB \<^bold>\<and> GAIN))\<rfloor>" *)
abbreviation "def \<equiv> let \<Gamma> = \<^bold>{Animals\<^bold>} in \<lfloor>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> (STAB \<^bold>\<and> GAIN)\<rfloor>"
(* abbreviation "excep1\<equiv>\<lfloor>WildAnimals \<^bold>\<rightarrow> (WILL \<^bold>\<preceq>\<^sub>A\<^sub>A STAB)\<rfloor>" *)
abbreviation "excep1 \<equiv> let \<Gamma> = \<^bold>{WildAnimals\<^bold>} in \<lfloor>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> STAB\<rfloor>"
(* abbreviation "excep2\<equiv>\<lfloor>DomesticAnimals \<^bold>\<rightarrow> (STAB \<^bold>\<preceq>\<^sub>A\<^sub>A (RELI \<^bold>\<and> WILL))\<rfloor>" *)
abbreviation "excep2 \<equiv> let \<Gamma> = \<^bold>{DomesticAnimals\<^bold>} in \<lfloor>(STAB \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> (RELI \<^bold>\<and> WILL))\<rfloor>"
(*...*)

axiomatization where (*legal knowledge*)
DEF: def and
EXCEP1: excep1 and
EXCEP2: excep2

lemma True nitpick[satisfy] oops (*axiomatization is consistent*)

lemma "let \<Gamma> = \<^bold>{DomesticAnimals\<^bold>} in \<lfloor>[\<Gamma>]\<^sup>\<preceq>STAB\<rfloor>" using EXCEP2 by auto (*TODO why?*)
lemma "let \<Gamma> = \<^bold>{FoxHunting\<^bold>} in \<lfloor>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> STAB\<rfloor>" nitpick oops (*TODO why?*)
(*TODO: find correct formalization*)

end


