theory mere_addition_lewis_revised  (* Christoph Benzmüller, Xavier Parent, 2025  *)

imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma> L::\<sigma> M::\<sigma>

(*the mere addition scenario*)
(*** With the Lewis rule  ***)

axiomatization where
(* Aplus is at least as good as A*)
 P1: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 P2: "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<circ><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>" 

(* Repugnant conclusion: B is strictly better than A*)
abbreviation "RC \<equiv> (\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)"

theorem T0:
  assumes "transitivity" 
  shows  "\<lfloor>RC\<rfloor>" 
  sledgehammer oops
  by (metis P1 P2 assms)
(* sledgehammer derives the repugnant conclusion*)

theorem T1:
  assumes "Suzumura" 
  shows  "\<lfloor>RC\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops (* countermodel found for card=3*)

(* Suzumura consistency for Betterness on formulas and as a function  *)
abbreviation "SC a b aplus \<equiv> (\<^bold>\<not>\<circ><\<^bold>\<not>b|aplus\<^bold>\<or>b>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>aplus|aplus\<^bold>\<or>a>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>a|a\<^bold>\<or>b>)\<^bold>\<rightarrow>\<^bold>\<not>\<circ><\<^bold>\<not>b|a\<^bold>\<or>b>" 

theorem T2a:
  assumes "\<lfloor>SC A B Aplus\<rfloor>" 
  shows "\<lfloor>RC\<rfloor>"
  nitpick [falsify,show_all,card i=3] oops (* countermodel found for card=3*)

axiomatization where
(* M strictly better than L*)
 P3: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>M|L\<^bold>\<or>M>\<^bold>\<and>\<circ><\<^bold>\<not>L|L\<^bold>\<or>M>\<rfloor>" and
(* L strictly better than A*)
 P4: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>L|A\<^bold>\<or>L> \<^bold>\<and> \<circ><\<^bold>\<not>A|A\<^bold>\<or>L>\<rfloor>"

abbreviation "INC_2 \<equiv> (\<circ><\<^bold>\<not>M|A\<^bold>\<or>M>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>M>)" (* A and M are incomparable *)

theorem T2b:
  assumes "\<lfloor>SC A M L\<rfloor>" and "\<lfloor>\<circ><\<^bold>\<not>M|A\<^bold>\<or>M>\<rfloor>"  (* no transitivity*)
  shows "\<lfloor>INC_2\<rfloor>"
  sledgehammer 
  by (smt (verit) P3 P4 assms(1,2)) 
 

theorem T1b:
  assumes "acyclicity" 
  shows  "\<lfloor>RC\<rfloor>" 
  nitpick [falsify,show_all,card i=3] (* countermodel found for card=3*)oops

theorem T2b:
  assumes "acyclicity" 
  and  "\<lfloor>\<^bold>\<not>P3\<rfloor>" 
shows  "\<lfloor>RC\<rfloor>" 
  sledgehammer
  nitpick [satisfy,show_all,card i=3]
(* model found*)

end



















  