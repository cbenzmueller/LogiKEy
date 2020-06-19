theory PreferenceLogicApplTest1                (*Benzmüller, Fuenmayor and Lomfeld, 2020*)               
   imports PreferenceLogicBasics
begin (***** proof of concept: ethical value ontology and wild animal cases *****)
(*auxiliary definitions*)
abbreviation pref::\<nu>            ("_\<^bold>\<prec>_")   where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>" 
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")   where  "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 

(*ethico-legal values*)
datatype UVAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

(*contenders have values*)
datatype c = p | d      (*parties/contenders: plaintiff, defendant*)  
consts UV::"c\<Rightarrow>UVAL\<Rightarrow>\<sigma>" (*upper values*)
consts V::"c\<Rightarrow>VAL\<Rightarrow>\<sigma>"   (*values*)

axiomatization where (*axiomatization of the ethico-legal value ontology*)
 V0: "\<lfloor>((UV x SECURITY) \<^bold>\<or> ((UV x EQUALITY) \<^bold>\<or> ((UV x LIBERTY) \<^bold>\<or> (UV x UTILITY))))\<rfloor>" and
 V1a:"\<lfloor>(UV x SECURITY) \<^bold>\<rightarrow> \<^bold>\<not>(UV x LIBERTY)\<rfloor>" and
 V1b:"\<lfloor>(UV x LIBERTY)  \<^bold>\<rightarrow> \<^bold>\<not>(UV x SECURITY)\<rfloor>" and
 V2a:"\<lfloor>(UV x EQUALITY) \<^bold>\<rightarrow> \<^bold>\<not>(UV x UTILITY)\<rfloor>" and
 V2b:"\<lfloor>(UV x UTILITY)  \<^bold>\<rightarrow> \<^bold>\<not>(UV x EQUALITY)\<rfloor>" and
 V3a:"\<lfloor>((V x RELI) \<^bold>\<or> (V x STAB)) \<^bold>\<rightarrow> (UV x SECURITY)\<rfloor>" and
 V4a:"\<lfloor>((V x EQUI) \<^bold>\<or> (V x FAIR)) \<^bold>\<rightarrow> (UV x EQUALITY)\<rfloor>" and
 V5a:"\<lfloor>((V x RESP) \<^bold>\<or> (V x WILL)) \<^bold>\<rightarrow> (UV x LIBERTY)\<rfloor>" and
 V6a:"\<lfloor>((V x GAIN) \<^bold>\<or> (V x EFFI)) \<^bold>\<rightarrow> (UV x UTILITY)\<rfloor>" and
(* V3b:"\<lfloor>(UV x SECURITY) \<^bold>\<rightarrow> ((V x RELI) \<^bold>\<or> (V x STAB))\<rfloor>" and
 V4b:"\<lfloor>(UV x EQUALITY) \<^bold>\<rightarrow> ((V x EQUI) \<^bold>\<or> (V x FAIR))\<rfloor>" and
 V5b:"\<lfloor>(UV x LIBERTY)  \<^bold>\<rightarrow> ((V x RESP) \<^bold>\<or> (V x WILL))\<rfloor>" and
 V6b:"\<lfloor>(UV x UTILITY)  \<^bold>\<rightarrow> ((V x GAIN) \<^bold>\<or> (V x EFFI))\<rfloor>" and *)
 V3c:"(val = EQUI \<or> val = EFFI \<or> val = FAIR \<or> val = GAIN \<or> val = RESP \<or> val = WILL)
      \<longrightarrow> \<lfloor>(UV x SECURITY) \<^bold>\<rightarrow> (((V x val) \<^bold>\<prec> (V x RELI)) \<^bold>\<or> ((V x val) \<^bold>\<prec> (V x STAB)))\<rfloor>" and
 V4c:"(val = RELI \<or> val = RESP \<or> val = STAB \<or> val = WILL \<or> val = EFFI \<or> val = GAIN)
      \<longrightarrow> \<lfloor>(UV x EQUALITY) \<^bold>\<rightarrow> (((V x val) \<^bold>\<prec> (V x EQUI)) \<^bold>\<or> ((V x val) \<^bold>\<prec> (V x FAIR)))\<rfloor>" and
 V5c:"(val = FAIR \<or> val = GAIN \<or> val = EQUI \<or> val = EFFI \<or> val = RELI \<or> val = STAB)
      \<longrightarrow> \<lfloor>(UV x LIBERTY) \<^bold>\<rightarrow> (((V x val) \<^bold>\<prec> (V x RESP)) \<^bold>\<or> ((V x val) \<^bold>\<prec> (V x WILL)))\<rfloor>" and
 V6c:"(val = WILL \<or> val = STAB \<or> val = RESP \<or> val = RELI \<or> val = FAIR \<or> val = EQUI)
      \<longrightarrow> \<lfloor>(UV x UTILITY) \<^bold>\<rightarrow> (((V x val) \<^bold>\<prec> (V x EFFI)) \<^bold>\<or> ((V x val) \<^bold>\<prec> (V x GAIN)))\<rfloor>" 




(*exploring & assessing the ontology with reasoning tools*)
lemma "\<exists>w. (V d GAIN) w" nitpick[satisfy,max_genuine=1,eval=UV V p d] oops (*show diff. models*)
lemma "False" sledgehammer oops
lemma "\<exists>x.\<lfloor>((V x STAB) \<^bold>\<and> V x WILL)\<rfloor>" nitpick[satisfy,user_axioms,eval=UV V p d]      oops (*satisfiable*)
lemma "\<not>(\<exists>x. \<lfloor>((V x GAIN) \<^bold>\<and> ((V x STAB) \<^bold>\<and> (V x WILL)))\<rfloor>)"  using V1a V3a V5a by blast

(*kinds of situations*)
consts Animals :: "c\<Rightarrow>\<sigma>"  (*appropriation of animals in general*)
consts WildAnimals :: "c\<Rightarrow>\<sigma>"  (*appropriation of wild animals*)
consts DomesticAnimals :: "c\<Rightarrow>\<sigma>" (*appropriation of domestic animals*)
consts FoxHunting :: "c\<Rightarrow>\<sigma>" (*hunting (appropriation) of foxes*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
W1: "WildAnimals x \<subseteq> Animals x" and
W2: "FoxHunting x \<subseteq> WildAnimals x" and
W3: "DomesticAnimals x \<subseteq> Animals x"

axiomatization where (*example legal corpus*)
S1: "\<lfloor>Animals x        \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> ((V x STAB) \<^bold>\<and> (V x GAIN)))\<rfloor>" and (*general*)
S2: "\<lfloor>WildAnimals x    \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> (V x STAB))\<rfloor>" and             (*specialization*)
S3: "\<lfloor>DomesticAnimals x \<^bold>\<rightarrow> ((V x STAB) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x WILL)))\<rfloor>" (*specialization*)

lemma True nitpick[satisfy] oops (*axioms consistent*)

(*explore implicit legal knowledge*)
lemma "\<lfloor>FoxHunting x \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" using S2 W2 by blast
lemma "\<lfloor>DomesticAnimals x \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" nitpick using S1 V1a V3a V5a W3 by blast 
lemma "\<lfloor>Animals x \<^bold>\<rightarrow> ((V x WILL) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x GAIN)))\<rfloor>" using S1 V1a V3a V5a by blast (*interesting...*)

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
 (*R1: finding for x given Intent promotes WILL*)
R1: "\<lfloor>(Intent x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(V x WILL)\<rfloor>" and 
R2: "\<lfloor>(Liv x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^sup>\<preceq>(V x GAIN)\<rfloor>" and
R3: "\<lfloor>(Land x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(V x RELI)\<rfloor>" and
R4: "\<lfloor>(Poss x \<^bold>\<rightarrow> For x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^sup>\<preceq>(V x STAB)\<rfloor>"

consts cw::i

(*Pierson v. Post*)         (*** Hi David, we still have some problems ... ***)
lemma "\<exists>w. ((FoxHunting d \<^bold>\<and> (Intent p \<^bold>\<and> Poss d))) w" nitpick[satisfy,show_all] oops
lemma "\<exists>w. ((FoxHunting d \<^bold>\<and> (FoxHunting p \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)))) w" nitpick[satisfy,show_all] oops
lemma "\<exists>w. ((FoxHunting d \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<and> For d) w" nitpick[satisfy,show_all] oops
lemma "\<not>(\<exists>w. ((FoxHunting d \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<and> For d) w)" 
  using R4 S2 V1a V3a V5 W2 reflBR by blast
lemma assumes "\<lfloor>FoxHunting d \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)\<rfloor>" shows "For d cw" sledgehammer nitpick
  by (meson R3 S2 V1 V3a V5a W2 W4 assms c.distinct(1) reflBR) 
(*Keeble v. Hickergill*)
lemma "\<exists>w. (WildAnimals p \<^bold>\<and> (Liv p \<^bold>\<and> Land p)) w" nitpick[satisfy] oops
lemma "\<exists>w. (WildAnimals p \<^bold>\<and> (WildAnimals d \<^bold>\<and> (Liv p \<^bold>\<and> Land p))) w" nitpick[satisfy] oops
lemma "\<lfloor>(WildAnimals p \<^bold>\<and> (Liv p \<^bold>\<and> Land p)) \<^bold>\<rightarrow> For p\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>(WildAnimals p \<^bold>\<and> (Liv p \<^bold>\<and> Land p)) \<^bold>\<rightarrow> For p\<rfloor>" sledgehammer
  by (meson R3 S2 V1 V3 V5 W4 c.distinct(1) reflBR)
(*Young v. Hitchens*)

lemma "\<lfloor>(WildAnimals d \<^bold>\<and> (Liv p \<^bold>\<and> (Land p \<^bold>\<and> (Liv d \<^bold>\<and> Poss d))))\<rfloor>" nitpick[satisfy] oops
lemma "\<lfloor>(WildAnimals d \<^bold>\<and> (Liv p \<^bold>\<and> (Land p \<^bold>\<and> (Liv d \<^bold>\<and> Poss d)))) \<^bold>\<rightarrow> For p\<rfloor>"
  by (meson R3 S2 V1 V3 V5 W4 c.distinct(1) reflBR)  (*Young v. Hitchens*)
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
