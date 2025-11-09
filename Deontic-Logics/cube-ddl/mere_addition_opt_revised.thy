theory mere_addition_opt_revised  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma>

(*the mere addition scenario*)

(*** With optimality  ***)

(* B is striclty better than A*)

abbreviation PO 
  where "PO \<equiv> \<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"

axiomatization where
(* Aplus is at least as good as A*)
 P1: "\<lfloor>\<^bold>\<not>\<odot><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 P2: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<odot><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>"

theorem T0:
  assumes "transitivity" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  sledgehammer oops
(* Sledgehammer is able to show that B is strictly better than A*)

theorem T1:
  assumes "Suzumura" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)

theorem T1a:
  assumes "Suzumura" 
  and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* B is not strictly better than A*)
  and  "\<lfloor>(\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* A and B are incomparable*)
  nitpick [falsify,show_all,card i=3]
(* Countermodel found*)






theorem T1:
  assumes "acyclicity" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)

theorem T6:
  assumes "quasitransitivity" 
  shows  "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)


theorem T5:
  assumes "quasitransitivty" 
  and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* A and B aren't equally good*)
  and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* B is not strictly better than A*)
shows "\<lfloor>(\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>" (* A and B are incomparable*)
  nitpick [falsify,show_all,card i=3]oops
(* Countermodel found*)







theorem T2:
  assumes "acyclicity" 
 and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
   and "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  shows  "\<lfloor>(\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  nitpick [falsify,show_all,card i=3]
(* Countermodel found*)








theorem T2:
  assumes "Suzumura" 
 and  "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
   and "\<lfloor>\<^bold>\<not>(\<^bold>\<not>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
  shows  "\<lfloor>(\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>)\<rfloor>"
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



















  