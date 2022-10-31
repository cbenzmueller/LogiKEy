theory ScottVariantClassroom imports Main  (*C. Benzmüller, 2022*)
begin  


(**********************************************)
(*** Higher-Order Modal Logic (HOML) in HOL ***)
(**********************************************)

(*unimportant*) declare [[smt_solver=cvc4,smt_oracle]]
(*unimportant*) declare[[syntax_ambiguity_warning=false]] 
(*unimportant*) nitpick_params[user_axioms,card=2] 
(*Type declarations and type abbreviations*)
typedecl i (*Possible worlds*)  
typedecl e (*Individuals*)      
type_synonym \<sigma> = "i\<Rightarrow>bool" (*World-lifted propositions*)
type_synonym \<gamma> = "e\<Rightarrow>\<sigma>" (*Lifted predicates*)
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" (*Unary modal connectives*)
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*Binary modal connectives*)

(*Modal logic connectives (operating on truth-sets)*)
abbreviation c1::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu> (infix"\<^bold>\<and>"50) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu> (infix"\<^bold>\<or>"49) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu> (infix"\<^bold>\<rightarrow>"48) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu> (infix"\<^bold>\<leftrightarrow>"47) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
consts R::"i\<Rightarrow>i\<Rightarrow>bool" ("_\<^bold>r_")  (*Accessibility relation*)
abbreviation c8::\<mu> ("\<^bold>\<box>_"[54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<^bold>rv)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu> ("\<^bold>\<diamond>_"[54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<^bold>rv)\<and>(\<phi> v)"
abbreviation c10::"\<gamma>\<Rightarrow>\<gamma>" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w.\<not>(\<Phi> x w)"
abbreviation c11::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>=_") where "x\<^bold>=y \<equiv> \<lambda>w.(x=y)"
abbreviation c12::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>\<noteq>_") where "x\<^bold>\<noteq>y \<equiv> \<lambda>w.(x\<noteq>y)"

(*Polymorphic possibilist quantification*)
abbreviation q1::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x.(\<Phi> x w)"
abbreviation q2 (binder"\<^bold>\<forall>"[10]11) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation q3::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x.(\<Phi> x w)"   
abbreviation q4 (binder"\<^bold>\<exists>"[10]11) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

(*Actualist quantification for individuals*)
consts existsAt::\<gamma> ("_\<^bold>@_")  
abbreviation q5::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x.(x\<^bold>@w)\<longrightarrow>(\<Phi> x w)"
abbreviation q6 (binder"\<^bold>\<forall>\<^sup>E"[8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
abbreviation q7::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x.(x\<^bold>@w)\<and>(\<Phi> x w)"
abbreviation q8 (binder"\<^bold>\<exists>\<^sup>E"[8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

(*Meta-logical predicate for global validity*)
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"





(******************************************************)
(*** Gödel's Ontological Argument (Scott's Variant) ***)
(******************************************************)

(*Positive properties*) 
consts posProp::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>")

(*Definition of God-like: x is God-like if, and only if, it 
  possesses all positive properties*)
definition G ("\<G>") where "\<G>(x) \<equiv> \<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"

(*Definition of Essence: Property \<Phi> is an essence of x if, and only if, 
 \<Phi> holds for x and \<Phi> necessarily entails every property Z of x*)
definition Ess ("_Ess._"[80,80]81)
  where "\<Phi> Ess. x \<equiv> \<Phi>(x) \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"

(*Definition of Necessary Existence: x has the property of necessary 
  existence if, and only if, the essence of x is necessarily instantiated*)
definition NE ("\<N>\<E>") where "\<N>\<E>(x) \<equiv> \<^bold>\<forall>\<Phi>. \<Phi> Ess. x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. (\<Phi>(x)))"

(*Axioms of Scott's variant*)
axiomatization where 
 (*one of a property or its complement∁is positive*)
 AXIOM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<^bold>\<not>\<Phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>\<P>(\<Phi>)\<rfloor>" and
 (*a property necessarily entailed by a positive property is positive*)
 AXIOM2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>.  \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" and
 (*\<P> is a logical property and \<G> is is definitely logical as an intersection 
   of positive properties; any such property ought to be positive*)
 AXIOM3: "\<lfloor>\<P>(\<G>)\<rfloor>" and
 (*any positive property is necessarily positive*)
 AXIOM4: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<P>(\<Phi>)\<rfloor>" and
 (*necessary existence is a positive property*)
 AXIOM5: "\<lfloor>\<P>(\<N>\<E>)\<rfloor>" 

(*Consistency*) 
lemma True nitpick[satisfy,show_all,format=2,card=2] oops (*Model found*)
lemma False sledgehammer[verbose,overlord] nitpick oops


(*We only need the B axiom*)
axiomatization where B:  "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<Phi>\<rfloor>" 
 (*Logic KB: what holds is necessarily possible*)
lemma B': "\<forall>x y. \<not>x\<^bold>ry \<or> y\<^bold>rx" using B by fastforce


(*Consistency*) 
lemma True nitpick[satisfy,show_all,format=2,card=1] oops (*Model found*)
lemma False sledgehammer nitpick oops

(*Verifying Scott's proof from*)
 (*positive properties are possibly exemplified*)
theorem THEOREM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>" 
  using AXIOM1 AXIOM2 by blast
 (*possibly there exists a Godlike entity*) 
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" using THEOREM1 AXIOM3 by simp
 (*being Godlike is an essential property of any Godlike entity*)
theorem THEOREM2: "\<lfloor>\<^bold>\<forall>x. \<G>(x) \<^bold>\<rightarrow> \<G> Ess. x\<rfloor>" sledgehammer
  by (smt (verit) AXIOM1 AXIOM4 Ess_def G_def)
 (*necessarily there exists a Godlike entity*)
theorem THEOREM3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  by (metis AXIOM5 B' CORO G_def NE_def THEOREM2)
 (*there exists a Godlike entity*)
theorem THEOREM4: "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" using B' CORO THEOREM3 by blast

 (*self-difference is not a positive property*)
lemma C1: "\<lfloor>\<^bold>\<not>\<P>(\<lambda>x. x\<^bold>\<noteq>x)\<rfloor>" using AXIOM1 AXIOM2 by blast
 (*absurdum/falsum is not a positive property*)
lemma C1': "\<lfloor>\<^bold>\<not>\<P>(\<lambda>x. \<^bold>\<bottom>)\<rfloor>" using AXIOM1 AXIOM2 by blast
 (*a property necessarily entailed by a positive property is positive*)
lemma C2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. \<P>(\<Phi>) \<^bold>\<and> (\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" 
   by (metis AXIOM1 G_def THEOREM4)

(*Consistency*) 
lemma True nitpick[satisfy,show_all,format=2] oops (*Model found*)
lemma False sledgehammer nitpick oops



(*Further Corollaries of Scott's theory*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" (*Modal collapse: holds*)
  sledgehammer nitpick
  oops

(*Further Corollaries of Scott's theory*)
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" (*Modal collapse: holds*)
proof - {fix w fix Q
 have 1: "\<forall>x. \<G>(x)(w) \<longrightarrow> (\<^bold>\<forall>Z. Z(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. \<G>(z) \<^bold>\<rightarrow> Z(z)))(w)" 
         by (metis AXIOM1 AXIOM4 G_def)
 have 2: "(\<exists>x. \<G>(x)(w)) \<longrightarrow> (Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. (\<G> z) \<^bold>\<rightarrow> Q))(w)" 
         using 1 by force
 have 3: "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q)(w)" using B' THEOREM3 2 by blast} 
 thus ?thesis by auto qed


end