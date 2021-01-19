theory GeneralKnowledge imports ValueOntology (** Benzmüller, Fuenmayor & Lomfeld, 2021 **)  
begin (*** General Legal and World Knowledge (LWK) ***)
(*LWK: kinds of situations addressed*)
consts appObject::\<sigma>  appAnimal::\<sigma> (*appropriation of objects/animals in general*)
       appWildAnimal::\<sigma>  appDomAnimal::\<sigma> (*appropriation of wild/domestic animals*)
(*LWK: postulates for kinds of situations*)
axiomatization where 
 W1: "\<lfloor>appAnimal \<^bold>\<rightarrow> appObject\<rfloor>" and
 W2: "\<lfloor>\<^bold>\<not>(appWildAnimal \<^bold>\<and> appDomAnimal)\<rfloor>" and 
 W3: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>"  and
 W4: "\<lfloor>appDomAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>"
(*LWK: (prima facie) value preferences for kinds of situations*)
axiomatization where 
 R1: "\<lfloor>appAnimal \<^bold>\<rightarrow> ([STAB\<^sup>p] \<^bold>\<prec> [STAB\<^sup>d])\<rfloor>" and  
 R2: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> ([WILL\<^sup>x\<inverse>] \<^bold>\<prec> [STAB\<^sup>x])\<rfloor>" and         
 R3: "\<lfloor>appDomAnimal  \<^bold>\<rightarrow> ([STAB\<^sup>x\<inverse>] \<^bold>\<prec> [RELI\<^sup>x\<^bold>\<oplus>RESP\<^sup>x])\<rfloor>"
(*LWK: domain vocabulary*)
typedecl e    (*declares new type for 'entities'*)
consts 
  Animal::"e\<Rightarrow>\<sigma>" Domestic::"e\<Rightarrow>\<sigma>" Fox::"e\<Rightarrow>\<sigma>" Parrot::"e\<Rightarrow>\<sigma>" Pet::"e\<Rightarrow>\<sigma>" FreeRoaming::"e\<Rightarrow>\<sigma>" 
(*LWK: domain knowledge (about animals)*)
axiomatization where 
 W5: "\<lfloor>\<^bold>\<forall>a. Fox a \<^bold>\<rightarrow> Animal a\<rfloor>"  and  
 W6: "\<lfloor>\<^bold>\<forall>a. Parrot a \<^bold>\<rightarrow> Animal a\<rfloor>" and
 W7: "\<lfloor>\<^bold>\<forall>a. (Animal a \<^bold>\<and> FreeRoaming a \<^bold>\<and> \<^bold>\<not>Pet a) \<^bold>\<rightarrow> \<^bold>\<not>Domestic a\<rfloor>" and
 W8: "\<lfloor>\<^bold>\<forall>a. Animal a \<^bold>\<and> Pet a \<^bold>\<rightarrow> Domestic a\<rfloor>"
(*LWK: legally-relevant, situational 'factors'*)
consts Own::"c\<Rightarrow>\<sigma>"    (*object is owned by party c*)
       Poss::"c\<Rightarrow>\<sigma>"   (*party c has actual possession of object*)
       Intent::"c\<Rightarrow>\<sigma>" (*party c has intention to possess object*)
       Mal::"c\<Rightarrow>\<sigma>" (*party c acts out of malice*)
       Mtn::"c\<Rightarrow>\<sigma>" (*party c respons. for maintenance of object*)
(*LWK: meaning postulates for general notions*)
axiomatization where
 W9: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and 
 W10: "\<lfloor>Own x \<^bold>\<rightarrow> (\<^bold>\<not>Own x\<inverse>)\<rfloor>"
(*LWK: conditional value preferences, e.g. from precedents*)
axiomatization where 
 R4: "\<lfloor>(Mal x\<inverse> \<^bold>\<and> Own x)  \<^bold>\<rightarrow> ([STAB\<^sup>x\<inverse>] \<^bold>\<prec> [RESP\<^sup>x\<^bold>\<oplus>RELI\<^sup>x])\<rfloor>"
(*LWK: relate values, outcomes and situational 'factors'*)
axiomatization where 
 F1: "Promotes (Intent x) (For x) WILL\<^sup>x" and
 F2: "Promotes (Mal x) (For x\<inverse>) RESP\<^sup>x" and  
 F3: "Promotes (Poss x) (For x) STAB\<^sup>x" and
 F4: "Promotes (Mtn x) (For x) RESP\<^sup>x" and  
 F5: "Promotes (Own x) (For x) RELI\<^sup>x"
(*Theory is consistent, (non-trivial) model found*)
lemma True nitpick[satisfy,card \<iota>=4] oops
end

