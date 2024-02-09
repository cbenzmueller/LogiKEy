theory mere_addition_lewis  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>

(*the mere addition scenario*)
(*** With the Lewis rule  ***)

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



















  