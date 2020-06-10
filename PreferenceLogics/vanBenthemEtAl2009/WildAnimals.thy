theory WildAnimals imports GeneralOntology (*Benzm.,Fuenmayor & Lomfeld, 2020*)               
begin (*** proof of concept: ethical value ontology and wild animal cases ***)
(*situational factors*)
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
consts Intent::"c\<Rightarrow>\<sigma>" (*c pursuing the animal (related to WILL)*)
consts Liv::"c\<Rightarrow>\<sigma>"    (*c pursuing its livelihood (related to GAIN)*)
consts Own::"c\<Rightarrow>\<sigma>"    (*animal was initially on c own land (related to RELI)*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*c has corporal possession of animal (related to STAB)*)
consts Cust::"c\<Rightarrow>\<sigma>"   (*c has (not yet relinquished) custody of the animal 
                        (related to RESP)*)

(*world knowledge*)
axiomatization where (*meaning postulates for situational factors*)
W6: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and
W7: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

axiomatization where (* relate factors to values*)
 R1: "\<lfloor>(Intent x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x WILL)\<rfloor>" and  
 R2: "\<lfloor>(Liv x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x GAIN)\<rfloor>" and
 R3: "\<lfloor>(Own x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>(V x RELI)\<rfloor>" and
 R4: "\<lfloor>(Poss x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x STAB)\<rfloor>" and
 R5: "\<lfloor>(Cust x \<^bold>\<and> For x) \<^bold>\<rightarrow>  \<^bold>\<box>(V x RESP)\<rfloor>"

lemma True nitpick[satisfy] oops (*axioms are consistent*)

(*sanity checks: situation kinds are possible *)
lemma "(\<exists>w. (WildAnimals) w)"     nitpick[satisfy] oops
lemma "(\<exists>w. (DomesticAnimals) w)" nitpick[satisfy] oops 

(*Pierson v. Post*)         
lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<and> For d\<rfloor>" 
  nitpick[satisfy,show_all]  oops (*non-trivial models exist*)
lemma "\<lfloor>(FoxHunting \<^bold>\<and> (Intent p \<^bold>\<and> Poss d)) \<^bold>\<rightarrow> For d\<rfloor>" 
  sledgehammer           (*proof not yet found*) 
  nitpick[show_all] oops (*countermodel not found*) 

(*Conti v. ASPCA*)
lemma "\<lfloor>(ParrotCapture \<^bold>\<and> (Cust p \<^bold>\<and> (Own p \<^bold>\<and> Poss d))) \<^bold>\<and> For p\<rfloor>"
  nitpick[satisfy,show_all]  oops (*non-trivial models exist*)
lemma "\<lfloor>(ParrotCapture \<^bold>\<and> (Cust p \<^bold>\<and> (Own p \<^bold>\<and> Poss d))) \<^bold>\<rightarrow> For p\<rfloor>"
  by (metis L3 R4 S3 V2 V3 V4 V5 W4 W7 other.simps(1) reflBR) (* proof found*)
end

