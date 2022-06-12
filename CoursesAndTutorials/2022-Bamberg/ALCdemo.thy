theory ALCdemo  imports Main begin
typedecl i 
type_synonym \<tau> = "(i\<Rightarrow>bool)" 
type_synonym \<sigma> = "(i\<Rightarrow>i\<Rightarrow>bool)"

(* Standard Description Logic ALC: Syntax und Semantic *)
abbreviation empty_concept ("\<bottom>") where 
  "\<bottom> \<equiv> \<lambda>x. False"
abbreviation universal_concept ("\<top>") where 
  "\<top> \<equiv> \<lambda>x. True"
abbreviation negation ("\<sim>") where 
  "\<sim>A \<equiv> \<lambda>x. \<not>A(x)"
abbreviation disjunction (infixr "\<squnion>" 40) where 
  "A \<squnion> B \<equiv> \<lambda>x. A(x) \<or> B(x)"
abbreviation conjunction (infixr "\<sqinter>" 41) where 
  "A \<sqinter> B \<equiv> \<lambda>x. A(x) \<and> B(x)"
abbreviation existential_role_restriction ("\<exists>") where 
  "\<exists>r A \<equiv> \<lambda>x.\<exists>y. r x y \<and> A(y)"
abbreviation universal_role_restriction ("\<forall>") where 
  "\<forall>r A \<equiv> \<lambda>x.\<forall>y. r x y \<longrightarrow> A(y)"

abbreviation subsumtion  (infixr "\<sqsubseteq>" 39) where 
  "A\<sqsubseteq>B \<equiv> \<forall>x. A(x) \<longrightarrow> B(x)"
abbreviation equality (infixr "\<doteq>" 38) where 
  "A \<doteq> B \<equiv> A \<sqsubseteq> B \<and> B \<sqsubseteq> A"

(* ALC: Simple Meta-Theory Examples *)
 lemma L1: "\<top> \<doteq> \<sim>\<bottom>"                      by metis 
 lemma L2: "A\<sqinter>B \<doteq> \<sim>(\<sim>A\<squnion>\<sim>B)"              by metis
 lemma L3: "\<exists>r C \<doteq> \<sim>(\<forall>r (\<sim>C))"            by auto
 lemma L4: "(A \<sqsubseteq> B) \<equiv> \<exists>X.(A \<doteq> (X \<sqinter> B))"   sledgehammer  oops
 lemma L5: "(A \<sqsubseteq> B) \<equiv> ((A \<sqinter> \<sim>B) \<doteq> \<bottom>)"    by auto 

(* ALC: Example Signatur *)
 consts HappyMan::\<tau> Human::\<tau> Female::\<tau> Doctor::\<tau> Professor::\<tau>  (* Concepts *)
 consts married::\<sigma> hasChild::\<sigma>                                (* Roles *)
 consts BOB::i MARY::i                                        (* Individuals *)
 axiomatization where diff1: "BOB \<noteq> MARY"

(* ALC: Simple TBox Example *)
 axiomatization where
  tbox1: "HappyMan \<doteq> (Human \<sqinter> \<sim>Female \<sqinter> (\<exists>married Doctor) \<sqinter> (\<forall>hasChild (Doctor \<squnion> Professor)))" and
  tbox2: "Doctor \<sqsubseteq> Human" and
  tbox3: "Professor \<sqsubseteq> Human"

(* ALC: Example Queries *)
 lemma "HappyMan \<sqsubseteq> \<exists>married Human" using tbox1 tbox2 by blast
 lemma "\<exists>married Human \<sqsubseteq> HappyMan" nitpick [user_axioms,show_all,format=2,atoms=BOB MARY] oops

(* ALC: Simple ABox Example *)
 axiomatization where 
  abox1: "HappyMan BOB" and 
  abox2: "hasChild BOB MARY" and
  abox3: "\<not> Doctor MARY" 

(* ALC: Example Queries *)
 lemma "(\<exists>married Human) BOB" using abox1 tbox1 tbox2 by blast
 lemma "(\<exists>married Human) a" nitpick [satisfy,user_axioms,show_all,format=2,atoms=BOB MARY] oops
 lemma "HappyMan a" nitpick [satisfy,user_axioms,show_all,format=2,atoms=BOB MARY] oops


(* ALC: Soundness of ALC-Tableaurules *)
lemma "(A \<sqinter> B)(x) \<longrightarrow> (A(x) \<and> B(x))"       by metis
lemma "(A \<squnion> B)(x) \<longrightarrow> (A(x) \<or> B(x))"       by metis 
lemma "(\<exists>r A)(x) \<longrightarrow> (\<exists>b. r x b \<and> A(b))"   by metis
lemma "((\<forall>r A)(x) \<and> r x y) \<longrightarrow> A(y)"       by (metis (hide_lams, mono_tags))
lemma "(A(x) \<and> \<sim>A(x)) \<longrightarrow> False"           by metis


(* Propositional Multimodal Logik K *)
 abbreviation mfalse ("\<^bold>\<bottom>") where 
  "\<^bold>\<bottom> \<equiv> \<lambda>w. False"    
 abbreviation mtrue ("\<^bold>\<top>") where 
  "\<^bold>\<top> \<equiv> \<lambda>w. True"    
 abbreviation mnot ("\<^bold>\<not>") where 
  "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"     
 abbreviation mand (infixr "\<^bold>\<and>" 51) where 
  "\<phi> \<^bold>\<and> \<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)"   
 abbreviation mor (infixr "\<^bold>\<or>" 50) where 
  "\<phi> \<^bold>\<or> \<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"   
 abbreviation mbox ("\<^bold>\<box>") where 
  "\<^bold>\<box>r \<phi> \<equiv> \<lambda>w.\<forall>v. r w v \<longrightarrow> \<phi>(v)"
 abbreviation mdia ("\<^bold>\<diamond>") where 
  "\<^bold>\<diamond>r \<phi> \<equiv> \<lambda>w.\<exists>v. r w v \<and> \<phi>(v)"  

 abbreviation valid :: "\<tau> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where   "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

(* Description Logic ALC is a reinvention of Propositional Multimodal Logic K *)

lemma "\<top> = \<^bold>\<top>"              by metis 
lemma "\<bottom> = \<^bold>\<bottom>"              by metis 
lemma "(A \<sqinter> B) = (A \<^bold>\<and> B)"  by metis 
lemma "(A \<squnion> B) = (A \<^bold>\<or> B)"  by metis 
lemma "(\<forall>r A) = (\<^bold>\<box>r A)"    by auto
lemma "(\<exists>r A) = (\<^bold>\<diamond>r A)"    by simp

(* Description Logic ALCQI as extension of ALC *)

abbreviation cardinality_restriction_leq ("\<le>") where 
  "\<le>n r A \<equiv> \<lambda>x. card({y. r x y \<longrightarrow> A(y)}) \<le> n"
abbreviation cardinality_restriction_geq ("\<ge>") where 
  "\<ge>n r A \<equiv> \<lambda>x. card({y. r x y \<longrightarrow> A(y)}) \<ge> n"
abbreviation cardinality_restriction_eq ("=") where 
  "=n r A \<equiv> (\<ge>n r A) \<sqinter> (\<le>n r A) "

lemma "(\<ge>1 married Human) a" nitpick [satisfy,user_axioms,show_all,format=2] oops (*model*)
lemma "(\<ge>1 married Human) a" nitpick [user_axioms,show_all,format=2] oops (*ctm*)
lemma "(\<ge>1 married H) a" nitpick[satisfy,user_axioms,show_all,format=2] oops
lemma "(=0 married Human) a" nitpick [satisfy,user_axioms,show_all,format=2] oops (*model*)

(*
(* A small example first-order predicate logic *)
consts 
  Peter::i Ben::i Sue::i
  likes::"(i\<Rightarrow>i\<Rightarrow>bool)" loves::"(i\<Rightarrow>i\<Rightarrow>bool)"

axiomatization where A0: "Peter \<noteq> Ben  \<and> Peter \<noteq> Sue \<and> Ben \<noteq> Sue"

axiomatization where
  A1: "\<forall>x. likes Peter x \<longrightarrow> likes Ben x" and
  A2: "\<forall>x y. loves x y \<longrightarrow> likes x y" and
  A3: "loves Peter Sue" 


lemma "\<exists>x. likes Ben x" sledgehammer
  nitpick [satisfy,user_axioms,show_all,format=2,card=3,atoms=Sue Ben Peter] oops 


lemma "\<exists>x. loves Ben x" sledgehammer
  nitpick [user_axioms,show_all,format=2,card=3,atoms=Ben Peter Sue] oops
*)

consts state::bool

lemma "(\<lambda>f x. f x) (\<lambda>x. x) state"

(*
Interpretation of a (tau-program) is an conditional polynomial.

We are thus interpreting (tau-program) over the set of all conditional polynomials.
That leaves us with the question What are conditional ploynomials?

A polynomial is a finite expression involving addition and multiplication of 
variables and ring elements.

A conditional polynomial is a finite expression involving addition and multiplication and 
the floor-function of variables and ring elements.

The floor function f(x) = 0 if and only if x = 0, and 1 otherwise.

f(x) = x or (not-allowed-)

we choose the ring ...  


g of variables (also called
indeterminates) and coefficients, that involves only the operations of addition, 
subtraction, multiplication, and non-negative integer exponentiation of variables. 
An example of a polynomial of a single indeterminate x is x2 − 4x + 7. 
An example in three variables is x3 + 2xyz2 − yz + 1.



Corrections: 
We can translate/compile each (tau-program) into an conditional polynomial.

*)
end
