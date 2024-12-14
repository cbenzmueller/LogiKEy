(* Note: Same as AxiomaticCategoryTheory except that full free logic is employed here (i.e.
with * and definite description) and that the model consisting of only one existing object that 
was previously constructed by nitpick for the axiom system FS-I (resp. FS-II) by Freyd Scedrov can 
obviously no longer be obtained. This is because * has now been axiomatized as a 
distinguished non-existing  object; therefore lines 293-296 (resp. 337-340) have been 
commented. *) 

theory AxiomaticCategoryTheory_FullFreeLogic imports Main
begin 
typedecl i  (*Type for individuals*)
consts fExistence:: "i\<Rightarrow>bool" ("E") (*Existence/definedness predicate in free logic*)
consts fStar:: "i" ("\<^bold>\<star>")   (*Distinguished symbol for undefinedness*)
axiomatization where fStarAxiom: "\<not>E(\<^bold>\<star>)" (*\<star> is a ``non-existing'' object in D.*)

abbreviation fNot ("\<^bold>\<not>") (*Free negation*)                          
 where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) (*Free implication*)        
 where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
abbreviation fIdentity (infixr "\<^bold>=" 13) (*Free identity*)        
 where "l \<^bold>= r \<equiv> l = r"
abbreviation fForall ("\<^bold>\<forall>") (*Free universal quantification guarded by @{text "E"}*)                
 where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
abbreviation fForallBinder (binder "\<^bold>\<forall>" [8] 9) (*Binder notation*) 
 where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"
abbreviation fThat:: "(i\<Rightarrow>bool)\<Rightarrow>i" ("\<^bold>I") 
 where "\<^bold>I\<Phi> \<equiv> if \<exists>x. E(x) \<and> \<Phi>(x) \<and> (\<forall>y. (E(y) \<and> \<Phi>(y)) \<longrightarrow> (y = x)) 
              then THE x. E(x) \<and> \<Phi>(x)
              else \<^bold>\<star>"
abbreviation fThatBinder:: "(i\<Rightarrow>bool)\<Rightarrow>i"  (binder "\<^bold>I" [8] 9) 
 where "\<^bold>Ix. \<phi>(x) \<equiv> \<^bold>I(\<phi>)"

text \<open> Further free logic connectives can now be defined as usual. \<close>

abbreviation fOr (infixr "\<^bold>\<or>" 11)                                 
 where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>" 
abbreviation fAnd (infixr "\<^bold>\<and>" 12)                                
 where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"    
abbreviation fImplied (infixr "\<^bold>\<leftarrow>" 13)       
 where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>" 
abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)                             
 where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"  
abbreviation fExists ("\<^bold>\<exists>")                                       
 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     
 where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"

declare [[smt_solver = cvc4,smt_oracle]]

section \<open> Preliminaries \<close>

consts 
 domain:: "i\<Rightarrow>i" ("dom _" [108] 109) 
 codomain:: "i\<Rightarrow>i" ("cod _" [110] 111) 
 composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

abbreviation KlEq (infixr "\<cong>" 56) (* Kleene equality *)
 where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<^bold>= y"  

abbreviation ExId (infixr "\<simeq>" 56) (* Existing identity *)  
 where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>= y"

lemma "x \<cong> x \<^bold>\<and> (x \<cong> y \<^bold>\<rightarrow> y \<cong> x) \<^bold>\<and> ((x \<cong> y \<^bold>\<and> y \<cong> z) \<^bold>\<rightarrow> x \<cong> z)" by blast
lemma "x \<simeq> x" nitpick [user_axioms, show_all, format = 2, expect = genuine] oops  
lemma " (x \<simeq> y \<^bold>\<rightarrow> y \<simeq> x) \<^bold>\<and> ((x \<simeq> y \<^bold>\<and> y \<simeq> z) \<^bold>\<rightarrow> x \<simeq> z)" by blast
lemma "x \<simeq> y \<^bold>\<rightarrow> x \<cong> y" by simp
lemma "x \<simeq> y \<^bold>\<leftarrow> x \<cong> y" nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 

abbreviation I where "I i \<equiv> (\<^bold>\<forall>x. E(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"


section \<open> Axioms Set I \<close>

locale Axioms_Set_I =
assumes 
 S\<^sub>i: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
 E\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y" and
 D\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma E\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i C\<^sub>i S\<^sub>i)
  lemma UC\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<^bold>\<forall>j.(I j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)" 
    by (smt A\<^sub>i C\<^sub>i S\<^sub>i)  
  lemma UD\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<^bold>\<forall>i.(I i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i)"
    by (smt A\<^sub>i D\<^sub>i S\<^sub>i) 
 lemma "(\<exists>C D. (\<^bold>\<forall>y. I (C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. I (D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
 lemma "(\<exists>x. E x) \<^bold>\<and> (\<exists>C D. (\<^bold>\<forall>y. I (C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. I (D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops  
end


section \<open> Axioms Set II \<close>

locale Axioms_Set_II =
assumes 
 S\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
 A\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
begin  
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  (* Nitpick finds a model *)  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  (* Nitpick finds a model *) 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma E\<^sub>i\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i\<^sub>i C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  lemma domTotal: "E x \<^bold>\<rightarrow> E(dom x)" 
    by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i) 
  lemma codTotal: "E x \<^bold>\<rightarrow> E(cod x)" 
    by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)  
end

context Axioms_Set_II
begin
  lemma S\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"  
    using S\<^sub>i\<^sub>i by blast
  lemma E\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    using E\<^sub>i\<^sub>i by blast
  lemma A\<^sub>iFromII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i by blast
  lemma C\<^sub>iFromII: "\<^bold>\<forall>y.\<^bold>\<exists>i. I i \<^bold>\<and> i\<cdot>y \<cong> y" 
    by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  lemma D\<^sub>iFromII: "\<^bold>\<forall>x.\<^bold>\<exists>j. I j \<^bold>\<and> x\<cdot>j \<cong> x" 
    by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
end


section \<open> Axioms Set III \<close>

locale Axioms_Set_III =
assumes
 S\<^sub>i\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
 D\<^sub>i\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
begin
  lemma True  (* Nitpick finds a model *)
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  (* Nitpick finds a model *) 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  (* Nitpick finds a model *) 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma E\<^sub>i\<^sub>i\<^sub>iImplied: "E(x\<cdot>y) \<^bold>\<rightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" 
    by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
end

context Axioms_Set_III
begin
  lemma S\<^sub>i\<^sub>iFromIII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>iFromIII: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" 
    by (metis A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>iFromIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>iFromIII: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    using C\<^sub>i\<^sub>i\<^sub>i by auto
  lemma D\<^sub>i\<^sub>iFromIII: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
    using D\<^sub>i\<^sub>i\<^sub>i by auto
end

context Axioms_Set_II
begin 
  lemma S\<^sub>i\<^sub>i\<^sub>iFromII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>i\<^sub>iFromII: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> (E(cod y)))" 
    by (metis C\<^sub>i\<^sub>i D\<^sub>i\<^sub>i E\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>i\<^sub>iFromII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>i\<^sub>iFromII: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    using C\<^sub>i\<^sub>i by auto
  lemma D\<^sub>i\<^sub>i\<^sub>iFromII: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" 
    using D\<^sub>i\<^sub>i by auto
end


section \<open> Axioms Set IV \<close>

locale Axioms_Set_IV =
assumes
 S\<^sub>i\<^sub>v: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
 E\<^sub>i\<^sub>v: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
 A\<^sub>i\<^sub>v: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 C\<^sub>i\<^sub>v: "(cod y)\<cdot>y \<cong> y" and
 D\<^sub>i\<^sub>v: "x\<cdot>(dom x) \<cong> x" 
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  (* Nitpick finds a model *)  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  (* Nitpick finds a model *) 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_IV
begin
  lemma S\<^sub>i\<^sub>i\<^sub>iFromIV: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>v by blast
  lemma E\<^sub>i\<^sub>i\<^sub>iFromIV: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> (E(cod y)))" 
    using E\<^sub>i\<^sub>v by blast
  lemma A\<^sub>i\<^sub>i\<^sub>iFromIV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>v by blast
  lemma C\<^sub>i\<^sub>i\<^sub>iFromIV: "E y \<^bold>\<rightarrow> (I(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" 
    by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
  lemma D\<^sub>i\<^sub>i\<^sub>iFromIV: "E x \<^bold>\<rightarrow> (I(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)"
    by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
end

context Axioms_Set_III
begin
  lemma S\<^sub>i\<^sub>vFromIII: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  
    using S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma E\<^sub>i\<^sub>vFromIII: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" 
    by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
  lemma A\<^sub>i\<^sub>vFromIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A\<^sub>i\<^sub>i\<^sub>i by blast
  lemma C\<^sub>i\<^sub>vFromIII: "(cod y)\<cdot>y \<cong> y" 
    using C\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
  lemma D\<^sub>i\<^sub>vFromIII: "x\<cdot>(dom x) \<cong> x" 
    using D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
end


section \<open> Axioms Set V \<close>

locale Axioms_Set_V =
assumes 
 S1: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2: "E(cod y) \<^bold>\<rightarrow> E y" and
 S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
 S5: "x\<cdot>(dom x) \<cong> x" and
 S6: "(cod y)\<cdot>y \<cong> y" 
begin  (*The obligatory consistency checks*)
  lemma True 
     nitpick [satisfy, user_axioms, expect=genuine] oops (*model found*)
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True 
    nitpick [satisfy, user_axioms, expect=genuine] oops (*model found*)
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True  
    nitpick [satisfy, user_axioms,  expect=genuine] oops (*model found*)
end

context Axioms_Set_V   (*Axioms Set IV is implied by Axioms Set V*)
begin
  lemma S\<^sub>i\<^sub>vFromV: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"   
    using S1 S2 S3 by blast
  lemma E\<^sub>i\<^sub>vFromV: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))"  using S3 by metis
  lemma A\<^sub>i\<^sub>vFromV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  using S4 by blast
  lemma C\<^sub>i\<^sub>vFromV: "(cod y)\<cdot>y \<cong> y"  using S6 by blast
  lemma D\<^sub>i\<^sub>vFromV: "x\<cdot>(dom x) \<cong> x"  using S5 by blast
end

context Axioms_Set_IV  (*Axioms Set V is implied by Axioms Set IV*)
begin
  lemma S1FromIV:  "E(dom x) \<^bold>\<rightarrow> E x"  using S\<^sub>i\<^sub>v by blast
  lemma S2FromIV:  "E(cod y) \<^bold>\<rightarrow> E y"  using S\<^sub>i\<^sub>v by blast
  lemma S3FromIV:  "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"  using E\<^sub>i\<^sub>v by metis
  lemma S4FromIV:  "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  using A\<^sub>i\<^sub>v by blast
  lemma S5FromIV:  "x\<cdot>(dom x) \<cong> x"  using D\<^sub>i\<^sub>v by blast
  lemma S6FromIV:  "(cod y)\<cdot>y \<cong> y"  using C\<^sub>i\<^sub>v by blast
end


section \<open> Axioms Set FS-I \<close>

consts  
   source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) 
   target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) 
   compositionF:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<^bold>\<cdot>" 110)

locale Axioms_Set_FS_I =
assumes           
  A1: "E(x\<^bold>\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<cong> \<box>y)" and 
 A2a: "((\<box>x)\<box>) \<cong> \<box>x" and 
 A2b: "\<box>(x\<box>) \<cong> \<box>x" and 
 A3a: "(\<box>x)\<^bold>\<cdot>x \<cong> x" and 
 A3b: "x\<^bold>\<cdot>(x\<box>) \<cong> x" and 
 A4a: "\<box>(x\<^bold>\<cdot>y) \<cong> \<box>(x\<^bold>\<cdot>(\<box>y))" and 
 A4b: "(x\<^bold>\<cdot>y)\<box> \<cong> ((x\<box>)\<^bold>\<cdot>y)\<box>" and 
  A5: "x\<^bold>\<cdot>(y\<^bold>\<cdot>z) \<cong> (x\<^bold>\<cdot>y)\<^bold>\<cdot>z"
begin
(* Commented (see explanation in header of file)   
  lemma True 
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
*) 
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = none] oops
  lemma InconsistencyAutomatic: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" 
    by (metis A1 A2a A3a)
  lemma InconsistencyInteractive: assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False 
    proof -
      (* Let @{text "a"} be an undefined object *)
     obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
      (* We instantiate axiom @{text "A3a"} with @{text "a"}. *)
     have 2: "(\<box>a)\<^bold>\<cdot>a \<cong> a" using A3a by blast
      (* By unfolding the definition of @{text "\<cong>"} we get from 1 that @{text "(\<box>a)\<^bold>\<cdot>a"} is 
           not defined. This is 
           easy to see, since if @{text "(\<box>a)\<^bold>\<cdot>a"} were defined, we also had that  @{text "a"} is 
           defined, which is not the case by assumption. *)
     have 3: "\<^bold>\<not>(E((\<box>a)\<^bold>\<cdot>a))" using 1 2 by metis
      (* We instantiate axiom @{text "A1"} with @{text "\<box>a"} and @{text "a"}. *)
     have 4: "E((\<box>a)\<^bold>\<cdot>a) \<^bold>\<leftrightarrow> (\<box>a)\<box> \<cong> \<box>a" using A1 by blast
      (* We instantiate axiom @{text "A2a"} with @{text "a"}. *)
     have 5: "(\<box>a)\<box> \<cong> \<box>a" using A2a by blast 
      (* From 4 and 5 we obtain @{text "\<^bold>(E((\<box>a)\<^bold>\<cdot>a))"} by propositional logic. *) 
     have 6: "E((\<box>a)\<^bold>\<cdot>a)" using 4 5 by blast 
      (* We have @{text "\<^bold>\<not>(E((\<box>a)\<^bold>\<cdot>a))"} and @{text "E((\<box>a)\<^bold>\<cdot>a)"}, hence Falsity. *)
     then show ?thesis using 6 3 by blast
    qed
end


section \<open> Axioms Set FS-II \<close>

locale Axioms_Set_FS_II =
assumes
  A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 A2a: "cod(dom x) \<cong> dom x " and  
 A2b: "dom(cod y) \<cong> cod y" and  
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
 A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
(* Commented (see explanation in header of file)   
  lemma True 
   nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
*) 
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = none] oops
  lemma InconsistencyAutomaticVII: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" 
    by (metis A1 A2a A3a)
  lemma "\<forall>x. E x" 
    using InconsistencyAutomaticVII by auto
  lemma InconsistencyInteractiveVII: 
    assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False 
    proof -
      (* Let @{text "a"} be an undefined object *)
     obtain a where 1: "\<^bold>\<not>(E a)" using NEx by auto
      (* We instantiate axiom @{text "A3a"} with @{text "a"}. *)
     have 2: "a\<cdot>(dom a) \<cong> a" using A3a by blast  
      (* By unfolding the definition of @{text "\<cong>"} we get from 1 that
          @{text "a\<cdot>(dom a)"} is not defined. This is 
          easy to see, since if @{text "a\<cdot>(dom a)"} were defined, we also had that @{text "a"} is 
          defined, which is not the case by assumption.*)
     have 3: "\<^bold>\<not>(E(a\<cdot>(dom a)))" using 1 2 by metis
      (* We instantiate axiom @{text "A1"} with @{text "a"} and @{text "dom a"}. *)
     have 4: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> cod(dom a)" using A1 by blast
      (* We instantiate axiom @{text "A2a"} with @{text "a"}. *)
     have 5: "cod(dom a) \<cong> dom a" using A2a by blast 
      (* We use 5 (and symmetry and transitivity of @{text "\<cong>"}) to rewrite the 
           right-hand of the equivalence 4 into @{text "dom a \<cong> dom a"}. *) 
     have 6: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> dom a" using 4 5 by auto
      (* By reflexivity of @{text "\<cong>"} we get that @{text "a\<cdot>(dom a)"} must be defined. *)
     have 7: "E(a\<cdot>(dom a))" using 6 by blast
      (* We have shown in 7 that @{text "a\<cdot>(dom a)"} is defined, and in 3 
           that it is undefined. Contradiction. *)
     then show ?thesis using 7 3 by blast
   qed
end


section \<open> Axioms Set VI \<close>

locale Axioms_Set_VI =
assumes
 A1': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 A2a: "cod(dom x) \<cong> dom x" and  
 A2b: "dom(cod y) \<cong> cod y" and  
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
 A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma A4aRedundant: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" 
    using A1' A2a A3a A5 by metis
  lemma A4bRedundant: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))"  
    using A1' A2b A3b A5 by smt
  lemma A2aRedundant: "cod(dom x) \<cong> dom x" 
    using A1' A3a A3b A4a A4b by smt
  lemma A2bRedundant: "dom(cod y) \<cong> cod y" 
    using A1' A3a A3b A4a A4b by smt 
end

context Axioms_Set_VI
begin
  lemma S1FromVI: "E(dom x) \<^bold>\<rightarrow> E x" 
    by (metis A1' A2a A3a)
  lemma S2FromVI: "E(cod y) \<^bold>\<rightarrow> E y" 
    using A1' A2b A3b by metis
  lemma S3FromVI: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    by (metis A1')
  lemma S4FromVI: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A5 by blast
  lemma S5FromVI: "x\<cdot>(dom x) \<cong> x" 
    using A3a by blast
  lemma S6FromVI: "(cod y)\<cdot>y \<cong> y" 
    using A3b by blast
end

context Axioms_Set_V
begin
  lemma A1'FromV: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    using S3 by blast
  lemma A2aFromV: "cod(dom x) \<cong> dom x"  
    by (metis S1 S2 S3 S5)
  lemma A2bFromV: "dom(cod y) \<cong> cod y"  
    using S1 S2 S3 S6 by metis
  lemma A3aFromV: "x\<cdot>(dom x) \<cong> x" 
    using S5 by blast
  lemma A3bFromV: "(cod y)\<cdot>y \<cong> y" 
    using S6 by blast
  lemma A4aFromV: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)"
    by (metis S1 S3 S4 S5 S6)
  lemma A4bFromV: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" 
    by (metis S2 S3 S4 S5 S6)
  lemma  A5FromV: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using S4 by blast
end


section \<open> Axioms Set VI reduced a \<close>

locale Axioms_Set_VI_reduced_a =
assumes
 A1': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
 A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_VI_reduced_a
begin
  lemma S1FromVI: "E(dom x) \<^bold>\<rightarrow> E x" 
    using A1' A3a A4a by (smt (verit))
  lemma S2FromVI: "E(cod y) \<^bold>\<rightarrow> E y" 
    by (smt (verit) A1' A3b A4b)
  lemma S3FromVI: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    by (metis A1')
  lemma S4FromVI: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A5 by blast
  lemma S5FromVI: "x\<cdot>(dom x) \<cong> x" 
    using A3a by blast
  lemma S6FromVI: "(cod y)\<cdot>y \<cong> y" 
    using A3b by blast
end


section \<open> Axioms Set VI reduced b \<close>

locale Axioms_Set_VI_reduced_b =
assumes
 A1': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 A2a: "cod(dom x) \<cong> dom x" and  
 A2b: "dom(cod y) \<cong> cod y" and  
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_VI_reduced_b
begin
  lemma S1FromVI_new': "E(dom x) \<^bold>\<rightarrow> E x" 
    by (metis A1' A2a A3a)
  lemma S2FromVI_new': "E(cod y) \<^bold>\<rightarrow> E y" 
    using A1' A2b A3b by smt
  lemma S3FromVI_new': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    by (metis A1')
  lemma S4FromVI_new': "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A5 by blast
  lemma S5FromVI_new': "x\<cdot>(dom x) \<cong> x" 
    using A3a by blast
  lemma S6FromVI_new': "(cod y)\<cdot>y \<cong> y" 
    using A3b by blast
end


section \<open> Axioms Set VI reduced c \<close>

locale Axioms_Set_VI_reduced_c =
assumes
 S1\<^sub>v: "E(dom x) \<^bold>\<rightarrow> E x" and
 S2\<^sub>v: "E(cod y) \<^bold>\<rightarrow> E y" and
 A1': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
 A3a: "x\<cdot>(dom x) \<cong> x" and 
 A3b: "(cod y)\<cdot>y \<cong> y" and 
  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_VI_reduced_c
begin
  lemma S1FromVI_new'': "E(dom x) \<^bold>\<rightarrow> E x" 
    using S1\<^sub>v by blast
  lemma S2FromVI_new'': "E(cod y) \<^bold>\<rightarrow> E y" 
    using S2\<^sub>v by blast
  lemma S3FromVI_new'': "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" 
    by (metis A1')
  lemma S4FromVI_new'': "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" 
    using A5 by blast
  lemma S5FromVI_new'': "x\<cdot>(dom x) \<cong> x" 
    using A3a by blast
  lemma S6FromVI_new'': "(cod y)\<cdot>y \<cong> y" 
    using A3b by blast
end


section \<open> Axioms Set FS-III \<close>

locale Axioms_Set_FS_III =
  assumes
  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " and  
 B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" and  
 B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and 
 B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and 
 B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True   
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_FS_III
begin
  lemma S1: "E(dom x) \<^bold>\<rightarrow> E x" 
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma S2: "E(cod y) \<^bold>\<rightarrow> E y"  
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"  
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma S5: "x\<cdot>(dom x) \<cong> x"  
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
  lemma S6: "(cod y)\<cdot>y \<cong> y"  
    nitpick [user_axioms, show_all, format = 2, expect = genuine] oops 
end


section \<open> Axioms Set FS-IV \<close>

locale Axioms_Set_FS_IV =
assumes
 B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
 B0b: "E(dom x) \<^bold>\<rightarrow> E x" and
 B0c: "E(cod x) \<^bold>\<rightarrow> E x" and
  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
 B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " and  
 B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" and  
 B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and 
 B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and 
 B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and 
 B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and 
  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"  
begin
  lemma True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True  
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops
  lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True 
    nitpick [satisfy, user_axioms, show_all, format = 2, expect = genuine] oops 
end

context Axioms_Set_FS_IV
begin
  lemma S1FromVIII: "E(dom x) \<^bold>\<rightarrow> E x"  using B0b by blast
  lemma S2FromVIII: "E(cod y) \<^bold>\<rightarrow> E y"  using B0c by blast 
  lemma S3FromVIII: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" by (metis B0a B0b B0c B1 B3a)
  lemma S4FromVIII: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" by (meson B0a B5) 
  lemma S5FromVIII: "x\<cdot>(dom x) \<cong> x" using B0a B3a by blast  
  lemma S6FromVIII: "(cod y)\<cdot>y \<cong> y" using B0a B3b by blast
end

context Axioms_Set_V
begin
  lemma B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S1 S2 S3 by blast
  lemma B0b: "E(dom x) \<^bold>\<rightarrow> E x" using S1 by blast
  lemma B0c: "E(cod x) \<^bold>\<rightarrow> E x" using S2 by blast
  lemma  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" by (metis S3 S5)
  lemma B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " by (metis S3 S5)
  lemma B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" by (metis S3 S6)  
  lemma B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" using S5 by auto
  lemma B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" using S6 by blast
  lemma B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis S1 S3 S4 S5)
  lemma B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis S2 S3 S4 S6)
  lemma  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using S4 by blast
end


context Axioms_Set_FS_IV  
begin
  lemma B2aRedundant: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " by (metis B0a B1 B3a) 
  lemma B2bRedundant: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" by (metis B0a B1 B3b) 
  lemma B4aRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis B0a B0b B1 B3a B5) 
  lemma B4bRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis B0a B0c B1 B3b B5) 
end

end



