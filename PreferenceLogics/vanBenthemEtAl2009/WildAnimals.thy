theory WildAnimals imports PreferenceLogicBasics (*Benzm., Fuenmayor & Lomfeld, 2020*)               
begin (***** proof of concept: ethical value ontology and wild animal cases *****)
(*auxiliary definitions*)
abbreviation pref::\<nu>            ("_\<^bold>\<prec>_")   where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<prec>\<^sub>A\<^sub>E \<psi>"   
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")   where  "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 
abbreviation boxg::\<mu> ("\<^bold>\<box>_") where "\<^bold>\<box>\<phi> \<equiv> \<^bold>\<box>\<^sup>\<preceq>\<phi>"

(*ethico-legal values*)
datatype UVAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

(*contenders have values*)
datatype c = p | d      (*parties/contenders: plaintiff, defendant*)  
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p"

consts UV::"c\<Rightarrow>UVAL\<Rightarrow>\<sigma>" (*upper values*)
consts V::"c\<Rightarrow>VAL\<Rightarrow>\<sigma>"   (*values*)
axiomatization where (*axiomatization of the ethico-legal value ontology*)
 V1:"\<lfloor>((UV x SECURITY) \<^bold>\<and> (UV x EQUALITY)) \<^bold>\<leftrightarrow> \<^bold>\<not>((UV x UTILITY) \<^bold>\<and> (UV x LIBERTY))\<rfloor>"  and 
 V2:"\<lfloor>((UV x SECURITY) \<^bold>\<and> (UV x UTILITY)) \<^bold>\<leftrightarrow> \<^bold>\<not>((UV x EQUALITY) \<^bold>\<and> (UV x LIBERTY))\<rfloor>"  and 
 V3:"\<lfloor>(((V x RELI) \<^bold>\<or> (V x EQUI)) \<^bold>\<or> ((V x STAB) \<^bold>\<or> (V x EFFI))) \<^bold>\<leftrightarrow> (UV x SECURITY)\<rfloor>" and
 V4:"\<lfloor>(((V x FAIR) \<^bold>\<or> (V x RESP)) \<^bold>\<or> ((V x EQUI) \<^bold>\<or> (V x RELI))) \<^bold>\<leftrightarrow> (UV x EQUALITY)\<rfloor>" and
 V5:"\<lfloor>(((V x WILL) \<^bold>\<or> (V x GAIN)) \<^bold>\<or> ((V x RESP) \<^bold>\<or> (V x FAIR))) \<^bold>\<leftrightarrow> (UV x LIBERTY)\<rfloor>"  and
 V6:"\<lfloor>(((V x EFFI) \<^bold>\<or> (V x STAB)) \<^bold>\<or> ((V x GAIN) \<^bold>\<or> (V x WILL))) \<^bold>\<leftrightarrow> (UV x UTILITY)\<rfloor>" 

(*exploring & assessing the ontology with reasoning tools*)
lemma "True" nitpick[satisfy,max_genuine=10,eval=UV V p d] oops (*shows diff. models*)
lemma "\<exists>x.\<lfloor>((V x STAB) \<^bold>\<and> V x WILL)\<rfloor>" nitpick[satisfy]      oops (* satisfiable*)
lemma "(\<exists>x. \<lfloor>((V x GAIN) \<^bold>\<and> ((V x STAB) \<^bold>\<and> (V x WILL)))\<rfloor>)"   oops (* satisfiable*)
lemma "\<not>(\<exists>x.\<lfloor>((V x RELI) \<^bold>\<and> V x WILL)\<rfloor>)" using V1 V3 V4 V5 V6 by blast (* unsatisfiable*)

(*kinds of situations*)
consts Animals :: "\<sigma>"  (*appropriation of animals in general*)
consts WildAnimals :: "\<sigma>"  (*appropriation of wild animals*)
consts DomesticAnimals :: "\<sigma>" (*appropriation of domestic animals*)
consts FoxHunting :: "\<sigma>" (*hunting (appropriation) of foxes*)
consts ParrotCapture :: "\<sigma>" (*capture (appropriation) of a parrot*)

axiomatization where (*world knowledge: meaning postulates for kinds of situations*)
W1: "WildAnimals \<subseteq> Animals" and
W2: "FoxHunting \<subseteq> WildAnimals" and
W3: "DomesticAnimals \<subseteq> Animals" and
W4: "ParrotCapture \<subseteq> DomesticAnimals"

axiomatization where (*example legal corpus*)
(* S1: "\<lfloor>Animals         \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> ((V x STAB) \<^bold>\<and> (V x GAIN)))\<rfloor>" and (*general*) *)
S2: "\<lfloor>WildAnimals     \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x STAB))\<rfloor>" and             (*specialization*)
S3: "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> ((V x\<inverse> STAB) \<^bold>\<prec> ((V x RELI) \<^bold>\<and> (V x WILL)))\<rfloor>"  (*specialization*)

lemma True nitpick[satisfy] oops (*axioms consistent*)

(*explore implicit legal knowledge*)
lemma "\<lfloor>FoxHunting \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" using S2 W2 by blast
lemma "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> ((V x\<inverse> WILL) \<^bold>\<prec> (V x  STAB))\<rfloor>" nitpick oops (*Countermodel*)

(*situational factors*)
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
consts Intent::"c\<Rightarrow>\<sigma>" (*party was actively pursuing the animal (related to WILL)*)
consts Liv::"c\<Rightarrow>\<sigma>"    (*party was pursuing its livelihood (related to economic GAIN)*)
consts Own::"c\<Rightarrow>\<sigma>"    (*animal was initially on party's own land (related to RELI)*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*party has corporal possession of the animal (related to STAB)*)
consts Cust::"c\<Rightarrow>\<sigma>"   (*party has (not yet relinquished) custody of the animal (related to RESP)*)

axiomatization where (*world knowledge: meaning postulates for situational factors*)
W5: "\<lfloor>Own x \<^bold>\<rightarrow> (\<^bold>\<not>Own x\<inverse>)\<rfloor>" and
W6: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and
W7: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

axiomatization where (* relate factors to values*)
 R1: "\<lfloor>(Intent x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x WILL)\<rfloor>" and  (*finding/ruling for x given its 'Intent' promotes WILL*)
 R2: "\<lfloor>(Liv x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x GAIN)\<rfloor>" and
 R3: "\<lfloor>(Own x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x RELI)\<rfloor>" and
 R4: "\<lfloor>(Poss x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x STAB)\<rfloor>" and
 R5: "\<lfloor>(Cust x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x RESP)\<rfloor>"

lemma True nitpick[satisfy] oops (*axioms are consistent*)
(*sanity checks: situation kinds are possible *)
lemma "(\<exists>w. (WildAnimals) w)" nitpick[satisfy] oops
lemma "(\<exists>w. (DomesticAnimals) w)" nitpick[satisfy] oops 

(*Pierson v. Post*)         
lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<and> For d\<rfloor>"  
   nitpick[satisfy,show_all] oops (*non-trivial model exists*)
lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<rightarrow> For d\<rfloor>" 
  (* sledgehammer[verbose] (*proof not yet found*) *)
 nitpick[show_all] oops (*no countermodel found*) 

(*Conti v. ASPCA*)
lemma "\<lfloor>(ParrotCapture \<^bold>\<and> (Cust p \<^bold>\<and> (Own p \<^bold>\<and> Poss d))) \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,show_all]  oops (*non-trivial models exist*)
lemma "\<lfloor>(ParrotCapture \<^bold>\<and> (Cust p \<^bold>\<and> (Own p \<^bold>\<and> Poss d))) \<^bold>\<rightarrow> For p\<rfloor>" sledgehammer
  by (metis R4 S3 V2 V3 V4 V5 V6 W4 W7 other.simps(1) reflBR) (* proof found*)

end



(***Text descriptions: **)

(* Pierson v. Post:
Suppose that 'p' represents Post and 'd' Pierson. Post's (p) argument goes like this:
1) Post was chasing the fox — i.e. Intent p
2) However, Pierson interfered and got possession of it —i.e. Poss d
3) 'pursuit vests property' — (Post's warrant, by R1 above)
4) Therefore, the fox belongs to Post — i.e. For p (defeated)

Pierson's (d) argument says:
1) Although Post was initially chasing the fox — i.e. Intent p
2) Pierson now has corporal possession of the fox  —i.e. Poss d
3) corporal possession creates legal certainty (Pufendorf) — (Pierson's warrant, by R4)
4) Therefore, the fox belongs to Pierson — i.e. For d (accepted, STAB is preferred to WILL by S2)

The situational factors (here summarized as "FoxHunting") indeed entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "WildAnimals").
*)

(***Text descriptions: **)

(* Conti v. ASPCA:
Suppose that 'p' represents ASPCA and 'd' Conti. ASPCA's (p) argument goes like this:
1) ASPCA owned the parrot — i.e. Own p
2) The parrot escaped and was recaptured by Conti —i.e. Poss d
3) However, ASPCA has not relinquished custody of the parrot —i.e. Cust p
4) (ASPCA's warrant, by R5 above)
4) Therefore, the parrot belongs to ASPCA — i.e. For p (accepted, RELI + RESP is preferred to STAB by S3)

Conti's (d) argument says:
1) Although the parrot belonged to ASPCA (who is still looking for it) — i.e. Own p & Cust p
2) Conti now has corporal possession of the parrot  —i.e. Poss d
3) corporal possession creates legal certainty (Pufendorf) — (Conti's warrant, by R4)
4) Therefore, the parrot belongs to Conti — i.e. For d (defeated)

The situational factors (here summarized as "ParrotCapture") indeed entail one of the antecedents
in the conditional preferences which constitute our background legal knowledge (here: "DomesticAnimals").
*)


