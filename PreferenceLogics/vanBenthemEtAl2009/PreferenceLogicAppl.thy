theory PreferenceLogicAppl                (*Benzmüller, Fuenmayor and Lomfeld, 2020*)               
   imports PreferenceLogicBasics
begin (***** proof of concept: ethical value ontology and wild animal cases *****)
(*auxiliary definitions*)
abbreviation pref::\<nu>            ("_\<^bold>\<prec>_")   where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>" 
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")   where  "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 
abbreviation boxg::\<mu> ("\<^bold>\<box>_") where "\<^bold>\<box>\<phi> \<equiv> \<^bold>\<box>\<^sup>\<prec>\<phi>"

(*ethico-legal values*)
datatype UVAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

(*contenders have values*)
datatype c = p | d      (*parties/contenders: plaintiff, defendant*)  
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p"

consts UV::"c\<Rightarrow>UVAL\<Rightarrow>\<sigma>" (*upper values*)
consts V::"c\<Rightarrow>VAL\<Rightarrow>\<sigma>"   (*values*)

axiomatization where (*axiomatization of the ethico-legal value ontology*)
 V1:"\<lfloor>(UV x SECURITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(UV x LIBERTY)\<rfloor>" and
 V2:"\<lfloor>(UV x EQUALITY) \<^bold>\<leftrightarrow> \<^bold>\<not>(UV x UTILITY)\<rfloor>" and
 V3:"\<lfloor>((V x RELI) \<^bold>\<or> (V x STAB)) \<^bold>\<leftrightarrow> (UV x SECURITY)\<rfloor>" and
 V4:"\<lfloor>((V x EQUI) \<^bold>\<or> (V x FAIR)) \<^bold>\<leftrightarrow> (UV x EQUALITY)\<rfloor>" and
 V5:"\<lfloor>((V x RESP) \<^bold>\<or> (V x WILL)) \<^bold>\<leftrightarrow> (UV x LIBERTY)\<rfloor>" and
 V6:"\<lfloor>((V x GAIN) \<^bold>\<or> (V x EFFI)) \<^bold>\<leftrightarrow> (UV x UTILITY)\<rfloor>" and
 V7:"\<lfloor>((V x GAIN)\<^bold>\<or>((V x EFFI)\<^bold>\<or>((V x WILL)\<^bold>\<or>(V x STAB)))) \<^bold>\<rightarrow> \<^bold>\<not>(UV x EQUALITY)\<rfloor>" and
 V8:"\<lfloor>((V x RESP)\<^bold>\<or>((V x WILL)\<^bold>\<or>((V x GAIN)\<^bold>\<or>(V x FAIR)))) \<^bold>\<rightarrow> \<^bold>\<not>(UV x SECURITY)\<rfloor>" and
 V9:"\<lfloor>((V x EQUI)\<^bold>\<or>((V x FAIR)\<^bold>\<or>((V x RELI)\<^bold>\<or>(V x RESP)))) \<^bold>\<rightarrow> \<^bold>\<not>(UV x UTILITY)\<rfloor>" and
V10:"\<lfloor>((V x RELI)\<^bold>\<or>((V x STAB)\<^bold>\<or>((V x EQUI)\<^bold>\<or>(V x EFFI)))) \<^bold>\<rightarrow> \<^bold>\<not>(UV x LIBERTY)\<rfloor>" 


(*exploring & assessing the ontology with reasoning tools*)
lemma "True" nitpick[satisfy,max_genuine=10,eval=UV V p d] oops (*show diff. models*)
lemma "\<exists>x.\<lfloor>((V x STAB) \<^bold>\<and> V x WILL)\<rfloor>" nitpick[satisfy]      oops (*not satisfiable*)
lemma "\<not>(\<exists>x. \<lfloor>((V x GAIN) \<^bold>\<and> ((V x STAB) \<^bold>\<and> (V x WILL)))\<rfloor>)" using V1 V3 V5 by blast

(*kinds of situations*)
consts Animals :: "\<sigma>"  (*appropriation of animals in general*)
consts WildAnimals :: "\<sigma>"  (*appropriation of wild animals*)
consts DomesticAnimals :: "\<sigma>" (*appropriation of domestic animals*)
consts FoxHunting :: "\<sigma>" (*hunting (appropriation) of foxes*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
W1: "WildAnimals \<subseteq> Animals" and
W2: "FoxHunting \<subseteq> WildAnimals" and
W3: "DomesticAnimals \<subseteq> Animals"

axiomatization where (*example legal corpus*)
(* S1: "\<lfloor>Animals         \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> ((V x STAB) \<^bold>\<and> (V x GAIN)))\<rfloor>" and (*general*) *)
S2: "\<lfloor>WildAnimals     \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x STAB))\<rfloor>" and             (*specialization*)
S3: "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> ((V x\<inverse> STAB) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x WILL)))\<rfloor>"  (*specialization*)

lemma True nitpick[satisfy] oops (*axioms consistent*)


(*explore implicit legal knowledge*)
lemma "\<lfloor>FoxHunting \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" using S2 W2 by blast
lemma "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" nitpick oops

(*situational factors*)
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
consts Intent::"c\<Rightarrow>\<sigma>" (*party was actively pursuing the animal (related to WILL)*)
consts Liv::"c\<Rightarrow>\<sigma>"    (*party was pursuing its livelihood (related to economic GAIN)*)
consts Land::"c\<Rightarrow>\<sigma>"   (*party was on its own land (related to RELI)*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*party was in possession of the animal (related to STAB)*)

axiomatization where (*world knowledge: meaning postulates for situational factors*)
W4: "\<not>(y=x) \<longrightarrow> \<lfloor>Land x \<^bold>\<rightarrow> (\<^bold>\<not>Land y)\<rfloor>" and
W5: "\<not>(y=x) \<longrightarrow> \<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss y)\<rfloor>"

axiomatization where (* relate factors to values*)
R1: "\<lfloor>(Intent x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x WILL)\<rfloor>" and  (*finding for x given Intent promotes WILL*)
R2: "\<lfloor>(Liv x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x GAIN)\<rfloor>" and 
R3: "\<lfloor>(Land x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x RELI)\<rfloor>" and
R4: "\<lfloor>(Poss x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x STAB)\<rfloor>"

lemma True nitpick[satisfy] oops (*axioms are consistent*)
(*sanity checks: *)
lemma "(\<exists>w. (WildAnimals) w)" nitpick[satisfy] oops
lemma "(\<exists>w. (DomesticAnimals) w)" nitpick[satisfy] oops 
lemma "(\<exists>w. (Animals) w)" nitpick[satisfy] oops

(*Pierson v. Post*)         
lemma "\<exists>w. (FoxHunting \<^bold>\<and> (Intent p  \<^bold>\<and> Poss d)) w" nitpick[satisfy,show_all] oops 
lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<rightarrow> For d\<rfloor>" nitpick[satisfy,show_all] nitpick oops

(*Keeble v. Hickergill*)
lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> Land p))\<rfloor>" nitpick[satisfy] oops
lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> Land p)) \<^bold>\<rightarrow> For p\<rfloor>" nitpick[satisfy,show_all] nitpick oops

(*Young v. Hitchens*)
lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> (Land p \<^bold>\<and> (Liv d \<^bold>\<and> Poss d))))\<rfloor>" nitpick[satisfy] oops
lemma "\<lfloor>(WildAnimals \<^bold>\<and> (Liv p \<^bold>\<and> (Land p \<^bold>\<and> (Liv d \<^bold>\<and> Poss d)))) \<^bold>\<rightarrow> For p\<rfloor>"
   nitpick[satisfy,show_all] nitpick oops 
end

(* Suppose that 'p' represents Post and 'd' Pierson.
Post's (p) argument goes like this:
1) Post was chasing the fox — i.e. Intent p
2) However, Pierson interfered and got possession of it —i.e. Poss d
3) pursuit vests (ceteris paribus) property —i.e. WILL p (Post's warrant, by R1 above)
4) Therefore, the fox belongs to Post — i.e. For p (defeated)

Pierson's (d) argument says:
1) Although Post was initially chasing the fox — i.e. Intent p
2) Pierson now has corporal possession of the fox  —i.e. Poss d
3) corporal possession creates legal certainty (Pufendorf) — i.e. STAB \<beta> (Pierson's warrant, by R4)
4) Therefore, the fox belongs to Pierson — i.e. For d (accepted, STAB is preferred to WILL by S2)

The situational factors (here summarized as "FoxHunting") indeed entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "WildAnimals").
*)

end

