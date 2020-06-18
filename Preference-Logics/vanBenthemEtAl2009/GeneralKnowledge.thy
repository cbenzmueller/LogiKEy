theory GeneralKnowledge  (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports ValueOntology 
begin (*** General Legal and World Knowledge (LWK) ***)

(*LWK: kinds of situations addressed*)
consts appObject::"\<sigma>"      (*appropriation of objects in general*)
consts appAnimal::"\<sigma>"      (*appropriation of animals in general*)
consts appWildAnimal::"\<sigma>"  (*appropriation of wild animals*)
consts appDomAnimal::"\<sigma>"   (*appropriation of domestic animals*)

(*LWK: meaning postulates for kinds of situations*)
axiomatization where 
W1: "\<lfloor>(appWildAnimal \<^bold>\<or> appDomAnimal) \<^bold>\<leftrightarrow> appAnimal\<rfloor>" and 
W2: "\<lfloor>appWildAnimal \<^bold>\<leftrightarrow> \<^bold>\<not>appDomAnimal\<rfloor>" and 
W3: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>"  and
W4: "\<lfloor>appDomAnimal \<^bold>\<rightarrow> appAnimal\<rfloor>" and
W5: "\<lfloor>appAnimal \<^bold>\<rightarrow> appObject\<rfloor>" 
(*\<dots>further situations regarding appropriation of objects\<dots>*)

(*LWK: value preferences for kinds of situations*)
 axiomatization where 
 L2: "\<lfloor>appWildAnimal \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB)\<rfloor>" and         
 L3: "\<lfloor>appDomAnimal  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>RESP])\<rfloor>"
(*\<dots>further preferences\<dots>*)

lemma True nitpick[satisfy] oops (*consistency, model found*)

(*LWK: general legal notions, with an existing clear definition*)
consts Own::"c\<Rightarrow>\<sigma>"    (*object is owned by party c*)
consts Poss::"c\<Rightarrow>\<sigma>"   (*party c has actual possession of object*)
consts Intent::"c\<Rightarrow>\<sigma>" (*party c has intention to possess object*)

(*LWK: other notions with some legal relevance (e.g. 'factors')*)
consts Liv::"c\<Rightarrow>\<sigma>" (*party c is pursuing its livelihood*)
consts Mtn::"c\<Rightarrow>\<sigma>" (*party c respons. for maintenance of object*)

(*LWK: meaning postulates for general notions*)
axiomatization where
W6: "\<lfloor>Poss x \<^bold>\<rightarrow> (\<^bold>\<not>Poss x\<inverse>)\<rfloor>" and 
W7: "\<lfloor>Own x \<^bold>\<rightarrow> (\<^bold>\<not>Own x\<inverse>)\<rfloor>"
(*\<dots>others\<dots>*)

(*LWK: conditional legal value preferences*)
 axiomatization where 
L5: "\<lfloor>(Poss x \<^bold>\<and> \<^bold>\<not>Mtn x\<inverse>)  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>RELI \<^bold>\<preceq>\<^sub>A\<^sub>A (x\<upharpoonleft>STAB))\<rfloor>" and
L6: "\<lfloor>(Own x \<^bold>\<and> Intent x \<^bold>\<and> Poss x\<inverse>)  \<^bold>\<rightarrow> (x\<inverse>\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>WILL])\<rfloor>"
(*\<dots>others\<dots>*)

(*LWK: value preferences given certain situational factors*)
axiomatization where 
R1: "\<lfloor>For x \<^bold>\<rightarrow> (Intent x \<^bold>\<leftrightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>WILL))\<rfloor>" and  
R2: "\<lfloor>For x \<^bold>\<rightarrow> (Liv x \<^bold>\<leftrightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>GAIN))\<rfloor>" and  
R3: "\<lfloor>For x \<^bold>\<rightarrow> (Poss x \<^bold>\<leftrightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>STAB))\<rfloor>" and  
R4: "\<lfloor>For x \<^bold>\<rightarrow> (Mtn x \<^bold>\<leftrightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RESP))\<rfloor>" and  
R5: "\<lfloor>For x \<^bold>\<rightarrow> (Own x \<^bold>\<leftrightarrow> \<^bold>\<box>\<^sup>\<preceq>(x\<upharpoonleft>RELI))\<rfloor>"
(*\<dots>others\<dots>*)

lemma True nitpick[satisfy] oops (*consistency, model found*)
end


