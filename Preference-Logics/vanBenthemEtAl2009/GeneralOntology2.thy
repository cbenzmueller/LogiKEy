theory GeneralOntology2 imports ValueOntology2 (*Benzm.,Fuenmayor&Lomfeld, 2020*)               
begin (**General World/Legal Knowledge**)

abbreviation pref::\<nu>  ("_\<^bold>\<prec>_")  where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>"  

(*legal/world knowledge: kinds of situations*)
consts appObject::"\<sigma>"         (*appropriation of objects in general*)
consts appAnimal::"\<sigma>"         (*appropriation of animals in general*)
consts appWildAnimal::"\<sigma>"     (*appropriation of wild animals*)
consts appDomesticAnimal::"\<sigma>" (*appropriation of domestic animals*)

(*legal/world knowledge: meaning postulates for kinds of situations*)
axiomatization where (* implicitly quantified for all situation/state/worlds *)
W1: "\<lfloor>(appWildAnimal \<^bold>\<or> appDomesticAnimal) \<^bold>\<leftrightarrow> appAnimal\<rfloor>" and (*mutually exhaustive*)
W2: "\<lfloor>appWildAnimal \<^bold>\<leftrightarrow> \<^bold>\<not>appDomesticAnimal\<rfloor>" and (*mutually exclusive*)
W3: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>"  and
W4: "\<lfloor>appDomesticAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>" and
W5: "\<lfloor>appAnimal \<^bold>\<rightarrow> appObject\<rfloor>" 
(* ... other situations regarding appropriation of objects, etc.*)

(* legal corpus: value preferences conditioned on kinds of situations*)
axiomatization where (*if situations not mutually exclusive: add ceteris paribus or make \<^bold>\<rightarrow> non-monotonic*)
L1: "\<lfloor>appObject         \<^bold>\<rightarrow> (p\<upharpoonleft>STAB \<^bold>\<prec> d\<upharpoonleft>STAB)\<rfloor>" and (* legal certainty always on the side of defendant*)
L2: "\<lfloor>appAnimal         \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>[STAB\<oplus>GAIN])\<rfloor>" and 
L3: "\<lfloor>appWildAnimal     \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec> x\<upharpoonleft>STAB)\<rfloor>" and        
L4: "\<lfloor>appDomesticAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>STAB \<^bold>\<prec> x\<upharpoonleft>[RELI\<oplus>RESP])\<rfloor>"
(* ... others*)

lemma True nitpick[satisfy,card i=4] oops (*satisfiable, axioms are consistent*)

(*legal/world knowledge: general legal notions (with an existing clear definition)*)
consts Own::"c\<Rightarrow>\<sigma>"    (*object is owned by c (later related to RELI)*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*party c has actual possession of object (later related to STAB)*)
consts Intent::"c\<Rightarrow>\<sigma>" (*party c has intention to possess the object (later related to WILL)*)

(*legal/world knowledge: other general notions with some legal relevance (e.g. 'factors')*)
consts Mtn::"c\<Rightarrow>\<sigma>" (*party c is responsible for the maintenance of the object (later related to RESP)*)
consts Liv::"c\<Rightarrow>\<sigma>" (*party c is pursuing its livelihood (later related to GAIN)*)

(*world knowledge: meaning postulates for general notions*)
axiomatization where
  W6: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and 
  W7: "\<lfloor>Own x \<^bold>\<rightarrow> (\<^bold>\<not>Own x\<inverse>)\<rfloor>"
(* ... others*)

(*legal corpus: value preferences conditioned on other notions (cf. 'factors')*)
axiomatization where
L5: "\<lfloor>(Poss x \<^bold>\<and> \<^bold>\<not>Mtn x\<inverse>)  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>RELI \<^bold>\<prec> (x\<upharpoonleft>STAB))\<rfloor>"
(* ... others*)

(*legal corpus: (unconditional) value preferences given ruling decisions (cf. 'rules' based on 'factors') *)
axiomatization where (* relate factors to values*)
 R1: "\<lfloor>(Intent x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>WILL)\<rfloor>" and  (*ruling for x given its intent to possess promotes WILL*)
 R2: "\<lfloor>(Liv x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>GAIN)\<rfloor>" and
 R3: "\<lfloor>(Poss x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>STAB)\<rfloor>" and
 R4: "\<lfloor>(Mtn x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RESP)\<rfloor>"
(* ... others*)

lemma True nitpick[satisfy] oops (*satisfiable, axioms are consistent*)

end
