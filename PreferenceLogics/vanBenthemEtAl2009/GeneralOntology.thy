theory GeneralOntology imports ValueOntology (*Benzm.,Fuenmayor&Lomfeld, 2020*)               
begin (**General/Upper Ontology**)

(*kinds of situations*)
consts Animals::"\<sigma>"         (*appropriation of animals in general*)
consts WildAnimals::"\<sigma>"     (*appropriation of wild animals*)
consts DomesticAnimals::"\<sigma>" (*appropriation of domestic animals*)
consts FoxHunting::"\<sigma>"      (*hunting (appropriation) of foxes*)
consts ParrotCapture::"\<sigma>"   (*capture (appropriation) of a parrot*)

(*world knowledge: meaning postulates for kinds of situations*)
axiomatization where 
W1: "WildAnimals \<subseteq> Animals" and
W2: "FoxHunting \<subseteq> WildAnimals" and
W3: "DomesticAnimals \<subseteq> Animals" and
W4: "ParrotCapture \<subseteq> DomesticAnimals"

(*(abstract) example legal corpus and implications for value preferences*)
axiomatization where 
S2: "\<lfloor>WildAnimals     \<^bold>\<rightarrow> (x\<inverse>\<down>WILL \<^bold>\<prec> x\<down>STAB)\<rfloor>" and        (*specialization*)
S3: "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> (x\<inverse>\<down>STAB \<^bold>\<prec> (x\<down>RELI \<^bold>\<and> x\<down>WILL))\<rfloor>" (*specialization*)

(*explore implicit legal knowledge*)
lemma "\<lfloor>FoxHunting \<^bold>\<rightarrow> (x\<inverse>\<down>WILL \<^bold>\<prec> x\<down>STAB)\<rfloor>" using S2 W2 by blast
lemma "\<lfloor>DomesticAnimals \<^bold>\<rightarrow> (x\<inverse>\<down>WILL \<^bold>\<prec> x\<down>STAB)\<rfloor>" nitpick oops (*Countermodel*)

lemma True nitpick[satisfy] oops (*satisfiable, axioms are consistent*)
end

