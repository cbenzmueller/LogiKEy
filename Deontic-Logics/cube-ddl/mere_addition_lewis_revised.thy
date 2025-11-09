theory mere_addition_lewis_revised  (* Christoph Benzmüller, Xavier Parent, 2024  *)

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

abbreviation "SC \<equiv> (\<^bold>\<not>\<circ><\<^bold>\<not>B|Aplus\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>A>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<^bold>\<rightarrow>\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>" 
(* Suzumura consistency for Betterness on formulas  *)

theorem T2a:
  assumes "\<lfloor>SC\<rfloor>" 
  shows "\<lfloor>RC\<rfloor>"
  nitpick [falsify,show_all,card i=3] oops (* countermodel found for card=3*)


axiomatization where
(* M strictly better than L*)
 P3: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>M|L\<^bold>\<or>M>\<^bold>\<and>\<circ><\<^bold>\<not>L|L\<^bold>\<or>M>\<rfloor>" and
(* L strictly better than A*)
 P4: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>L|A\<^bold>\<or>L> \<^bold>\<and> \<circ><\<^bold>\<not>A|A\<^bold>\<or>L>\<rfloor>"

abbreviation "SC_2 \<equiv> (\<^bold>\<not>\<circ><\<^bold>\<not>M|L\<^bold>\<or>M>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>L|A\<^bold>\<or>L>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>A|A\<^bold>\<or>M>)\<^bold>\<rightarrow>\<^bold>\<not>\<circ><\<^bold>\<not>M|A\<^bold>\<or>M>" 
(* Suzumura consistency for Betterness on formulas  *)

abbreviation "INC_2 \<equiv> (\<circ><\<^bold>\<not>M|A\<^bold>\<or>M>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>M>)" (* A and M are incomparable *)

theorem T2b:
  assumes "\<lfloor>SC_2\<rfloor>" and "\<lfloor>\<circ><\<^bold>\<not>M|A\<^bold>\<or>M>\<rfloor>"  (* no transitivity*)
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




theorem T2b:
  assumes "acyclicity" 
  shows  "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)




abbreviation "INC \<equiv> (\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)" (* A and B are incomparable *)

theorem T2b:
  assumes "\<lfloor>SC\<rfloor>" and "\<lfloor>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<rfloor>"  (* no transitivity*)
  shows "\<lfloor>INC\<rfloor>"
  sledgehammer oops
  by (smt (verit) P1 P2 assms(1,2)) (* proof found*)
  
(*incomparability*)

(* Repugnant conclusion: B is strictly better than A*)



theorem T6:
  assumes "quasitransitivity" 
  shows  "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)


theorem T5:
  assumes "quasitransitivty" 
  and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* A and B aren't equally good*)
  and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* B is not strictly better than A*)
shows "\<lfloor>(\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* A and B are incomparable*)
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)


theorem T2a:
  assumes "\<lfloor>SC_2\<rfloor>" 
  shows "\<lfloor>RC\<rfloor>"
  nitpick [falsify,show_all,card i=3] oops (* countermodel found for card=3*)





theorem T2:
  assumes "acyclicity" 
 and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
   and "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  shows  "\<lfloor>(\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]
(* Countermodel found*)








theorem T2:
  assumes "Suzumura" 
 and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
   and "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  shows  "\<lfloor>(\<circ><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<circ><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]
(* Countermodel found*)






(* Sledgehammer finds P0-P2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem T0:
  assumes "transitivity" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  sledgehammer oops
(* Sledgehammer is able to show that B is striclty better than A*)

theorem T1:
  assumes "Suzumura" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Nitpick finds a countermodel to the previous claim*)

theorem T2:
  assumes "Suzumura" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>) \<^bold>\<or> (\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  sledgehammer
  nitpick [falsify,show_all,card i=3]
(* Nitpick finds a countermodel to the previous claim*)









theorem T1:
  True
  nitpick [satisfy, card i=3]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem T2:
  assumes reflexivity Ferrers
  shows False
  sledgehammer 
  by (metis P0 P1 P2 assms(2))
  
(* Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity*)

theorem T3:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

theorem T4:
  assumes Quasitransit
  shows True
  nitpick [show_all,satisfy,card=4] (* model found for card i=4 *)
  oops








end



















  




axiomatization where
(* A is striclty better than B*)
 PPP0: "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<circ><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
(* Aplus is at least as good as A*)
 PPP1: "\<lfloor>\<^bold>\<not>\<circ><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 PPP2: "\<lfloor>(\<^bold>\<not>\<circ><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<circ><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>"

(* Sledgehammer finds PPP0-PPP2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem T0:
  assumes transitivity
  shows False 
  sledgehammer
  oops
  
(* Nitpick shows consistency in the absence of transitivity*)

lemma T1:
  True
  nitpick [satisfy, card i=3,show_all]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem T2:
  assumes reflexivity Ferrers
  shows False
  sledgehammer 
  
(* Nitpick shows consistency if transitivity is weakened into acyclicity
 or quasi-transitivity*)

theorem T3:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

theorem T4:
  assumes Quasitransit
  shows True
  nitpick [show_all,satisfy] 
  oops

end



















  