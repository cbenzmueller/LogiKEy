theory PreferenceLogicApplication3 imports PreferenceLogicBasics PreferenceLogicTests                    
begin
(*some conceptually unimportant declarations of defaults for tools*) 
nitpick_params[assms=true,user_axioms=true,expect=genuine,show_all,format=3] 

(***** proof of concept formalization of ethical value ontology *****)

abbreviation pref::\<nu>   ("_\<^bold>\<prec>_")  where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>" 
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

datatype c = p | d (*parties/contenders: plaintiff, defendant*)
consts For :: "c\<Rightarrow>\<sigma>"  (*decision: find for party*)

datatype UVAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

consts UV::"c\<Rightarrow>UVAL\<Rightarrow>\<sigma>" (*upper values*)
consts V::"c\<Rightarrow>VAL\<Rightarrow>\<sigma>" (*values*)

axiomatization where (*axioms for value ontology*)
 V1:"\<lfloor>(UV x SECURITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(UV x LIBERTY)\<rfloor>" and
 V2:"\<lfloor>(UV x EQUALITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(UV x UTILITY)\<rfloor>" and

 V3:"\<lfloor>(UV x SECURITY) \<^bold>\<leftrightarrow> ((V x RELI) \<^bold>\<or> (V x STAB))\<rfloor>" and
 V4:"\<lfloor>(UV x EQUALITY) \<^bold>\<leftrightarrow> ((V x EQUI) \<^bold>\<or> (V x FAIR))\<rfloor>" and
 V5:"\<lfloor>(UV x LIBERTY)  \<^bold>\<leftrightarrow> ((V x RESP) \<^bold>\<or> (V x WILL))\<rfloor>" and
 V6:"\<lfloor>(UV x UTILITY)  \<^bold>\<leftrightarrow> ((V x GAIN) \<^bold>\<or> (V x EFFI))\<rfloor>" 

lemma True nitpick[satisfy] oops
lemma "\<exists>x. \<lfloor>((V x GAIN) \<^bold>\<and> ((V x STAB) \<^bold>\<and> (V x WILL)))\<rfloor>" nitpick[satisfy] oops (*not satisfiable*)
lemma "\<not>(\<exists>x. \<lfloor>((V x GAIN) \<^bold>\<and> ((V x STAB) \<^bold>\<and> (V x WILL)))\<rfloor>)" using V1 V3 V5 by blast
lemma "\<exists>x. \<lfloor>((V x RESP) \<^bold>\<and> ((V x GAIN) \<^bold>\<and> (V x WILL)))\<rfloor>" nitpick[satisfy] oops
lemma "\<exists>x. \<lfloor>((V x RESP) \<^bold>\<and> ((V x GAIN) \<^bold>\<and> \<^bold>\<not>(V x WILL)))\<rfloor>" nitpick[satisfy] oops

(*kinds of situations*)
 consts Animals :: "\<sigma>"  (*appropriation of animals in general*)
 consts WildAnimals :: "\<sigma>"  (*appropriation of wild animals*)
 consts DomesticAnimals :: "\<sigma>" (*appropriation of domestic animals*)
 consts FoxHunting :: "\<sigma>" (*hunting (appropriation) of foxes*)
(*...*)
axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
(* W1: "\<lparr> DomesticAnimals | WildAnimals \<rparr>" and  *)
W2: "WildAnimals \<subseteq> Animals" and
W3: "FoxHunting \<subseteq> WildAnimals" and
W4: "DomesticAnimals \<subseteq> Animals"
(*...*)

axiomatization where (*example legal corpus*)
S1: "\<lfloor>Animals          \<^bold>\<rightarrow>  ((V x WILL) \<^bold>\<prec> ((V x STAB) \<^bold>\<and> (V x GAIN)))\<rfloor>" and (*general*)
S2: "\<lfloor>WildAnimals      \<^bold>\<rightarrow>  ((V x WILL) \<^bold>\<prec> (V x STAB))\<rfloor>" and                (*specialization*)
S3: "\<lfloor>DomesticAnimals  \<^bold>\<rightarrow>  ((V x STAB) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x WILL)))\<rfloor>"     (*specialization*)

lemma True nitpick[satisfy] oops (*axioms consistent*)

(*explore implicit legal knowledge*)
lemma "\<lfloor>FoxHunting \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" nitpick[satisfy] 
  using S2 W3 by blast
lemma "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" nitpick[satisfy]
  using S1 V1 V3 V5 W4 by blast (*interesting...*)
lemma "\<lfloor>Animals \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x GAIN)))\<rfloor>" nitpick[satisfy] 
  using S1 V1 V3 V5 by blast (*interesting...*)

(*situational factors*)
consts Intent :: "c\<Rightarrow>\<sigma>"  (*party was actively pursuing the animal (related to WILL)*)
consts Liv :: "c\<Rightarrow>\<sigma>"  (*party was pursuing its livelihood (related to economic GAIN)*)
consts Land :: "c\<Rightarrow>\<sigma>"  (*party was on its own land (related to RELI)*)
consts Poss :: "c\<Rightarrow>\<sigma>"  (*party was in possession of the animal (related to STAB)*)

axiomatization where (*world knowledge: meaning postulates for situational factors*)
W5: "\<not>(y=x) \<longrightarrow> \<lfloor>Land x \<^bold>\<rightarrow> (\<^bold>\<not>Land y)\<rfloor>" and
W6: "\<not>(y=x) \<longrightarrow> \<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss y)\<rfloor>"

axiomatization where (* relate factors to values*)
R1: "\<lfloor>(Intent x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^sup>\<preceq>(V x WILL)\<rfloor>" and (*finding for x given 'Intent' promotes value 'WILL'*)
R2: "\<lfloor>(Liv x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^sup>\<preceq>(V x GAIN)\<rfloor>" and
R3: "\<lfloor>(Land x  \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(V x RELI)\<rfloor>" and
R4: "\<lfloor>(Poss x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^sup>\<preceq>(V x STAB)\<rfloor>"

lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<rightarrow> For d\<rfloor>" nitpick[satisfy]
  by (meson R4 S2 V1 V3 V5 W3 W6 c.distinct(1) reflBR) (*Pierson v. Post*)

lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> Land p)) \<^bold>\<rightarrow> For p\<rfloor>" nitpick[satisfy]
  by (meson R3 S2 V1 V3 V5 W5 c.distinct(1) reflBR)  (*Keeble v. Hickergill*)

lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> (Land p \<^bold>\<and> (Liv d \<^bold>\<and> Poss d)))) \<^bold>\<rightarrow> For p\<rfloor>" nitpick[satisfy]
  by (meson R3 S2 V1 V3 V5 W5 c.distinct(1) reflBR)  (*Young v. Hitchens*)

(* Suppose that 'p' represents Post and 'd' Pierson.
Post's (p) argument goes like this:
1) Post was chasing the fox — i.e. Intent p
2) However, Pierson interfered and got possession of it —i.e. Poss d
3) pursuit vests (ceteris paribus) property —i.e. WILL p (Post's warrant, by R1 above)
4) Therefore, the fox belongs to Post — i.e. For p (defeated)

Pierson's (d) argument says:
1) Although Post was initially chasing the fox — i.e. Intent p
2) Pierson now has corporal possession of the fox  —i.e. Poss d
3) corporal possession creates legal certainty (Pufendorf)  —i.e. STAB \<beta> (Pierson's warrant, by R4)
4) Therefore, the fox belongs to Pierson — i.e. For d (accepted, STAB is preferred to WILL by S2)

The situational factors (here summarized as "FoxHunting") indeed entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "WildAnimals").
*)

end


