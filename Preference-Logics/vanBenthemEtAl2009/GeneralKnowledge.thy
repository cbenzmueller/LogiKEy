theory GeneralKnowledge  (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports ValueOntology 
begin (*** General Legal and World Knowledge (LWK) ***)

(*LWK: kinds of situations addressed*)
consts appObject::"\<sigma>"      (*appropriation of objects in general*)
consts appAnimal::"\<sigma>"      (*appropriation of animals in general*)
consts appWildAnimal::"\<sigma>"  (*appropriation of wild animals*)
consts appDomAnimal::"\<sigma>"   (*appropriation of domestic animals*)

(*LWK: meaning postulates for kinds of situations*)
axiomatization where (*implicitly quantified for all situations*)
W1: "\<lfloor>(appWildAnimal \<^bold>\<or> appDomAnimal) \<^bold>\<leftrightarrow> appAnimal\<rfloor>" and 
W2: "\<lfloor>appWildAnimal \<^bold>\<leftrightarrow> \<^bold>\<not>appDomAnimal\<rfloor>" and 
W3: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>"  and
W4: "\<lfloor>appDomAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>" and
W5: "\<lfloor>appAnimal \<^bold>\<rightarrow> appObject\<rfloor>" 
(*... other situations regarding appropriation of objects, etc.*)

(*LWK: value preferences for kinds of situations*)
axiomatization where 
(* legal certainty always on the side of defendant*)
L1: "\<lfloor>appObject     \<^bold>\<rightarrow> (p\<upharpoonleft>STAB  \<^bold>\<prec>\<^sub>A\<^sub>A d\<upharpoonleft>STAB)\<rfloor>" and 
L2: "\<lfloor>appAnimal     \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[STAB\<oplus>GAIN])\<rfloor>" and 
L3: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>STAB)\<rfloor>" and        
L4: "\<lfloor>appDomAnimal  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>STAB \<^bold>\<prec>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>RESP])\<rfloor>"
(* ... others*)
(*remark: assumes that conditions are mutually exclusive;
  we may want to add ceteris paribus or make \<^bold>\<rightarrow> non-monotonic*)

lemma True nitpick[satisfy] oops (*satisfiable,model found*)

(*LWK: general legal notions, with an existing clear definition*)
consts Own::"c\<Rightarrow>\<sigma>"    (*object is owned by c*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*party c has actual possession of object*)
consts Intent::"c\<Rightarrow>\<sigma>" (*party c has intention to possess object*)
(*Remark: Own will later be related to RELI, Poss to STAB and
  Intent to WILL*)

(*LWK: other notions with some legal relevance (e.g. 'factors')*)
consts Liv::"c\<Rightarrow>\<sigma>" (*party c is pursuing its livelihood*)
consts Mtn::"c\<Rightarrow>\<sigma>" (*c responsible for maintenance of object*)
(*Remark: Mtn will be related to RESP and Liv to GAIN*)

(*world knowledge: meaning postulates for general notions*)
axiomatization where
  W6: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and 
  W7: "\<lfloor>Own x \<^bold>\<rightarrow> (\<^bold>\<not>Own x\<inverse>)\<rfloor>"
(* ... others*)

(*legal corpus: value prefs depend. on legal notions ('factors')*)
axiomatization where
L5: "\<lfloor>(Poss x \<^bold>\<and> \<^bold>\<not>Mtn x\<inverse>)  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>RELI \<^bold>\<prec> (x\<upharpoonleft>STAB))\<rfloor>"
(* ... others*)

(*legal corpus: (unconditional) value preferences given ruling 
  decisions ('rules' based on 'factors') *)
axiomatization where (* relate factors to values*)
 R1: "\<lfloor>(Intent x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>WILL)\<rfloor>" and  
  (*R1: ruling for x given its intent to possess promotes WILL*)
 R2: "\<lfloor>(Liv x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>GAIN)\<rfloor>" and
 R3: "\<lfloor>(Poss x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>STAB)\<rfloor>" and
 R4: "\<lfloor>(Mtn x \<^bold>\<and> For x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RESP)\<rfloor>"
(* ... others*)

lemma True nitpick[satisfy] oops (*satisfiable, consistent*)
end
