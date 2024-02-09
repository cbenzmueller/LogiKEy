theory mere_addition_kratzer  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>

(*the mere addition scenario*)
(*** With the KRATZER rule  ***)

axiomatization where
(* A is striclty better than B*)
 PPPP0: "\<lfloor>(\<^bold>\<not>\<ominus><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<ominus><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
(* Aplus is at least as good as A*)
 PPPP1: "\<lfloor>\<^bold>\<not>\<ominus><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 PPPP2: "\<lfloor>(\<^bold>\<not>\<ominus><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<ominus><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>"

(* Sledgehammer finds PPPP0-2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem 
  assumes transitivity
  shows False 
  sledgehammer
  oops

theorem
  assumes transitivity
  shows True
  nitpick [satisfy]
  oops
  

(* Nitpick shows consistency in the absence of transitivity*)

lemma true
  nitpick [satisfy, card i=3]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem ioInconsK:
  assumes reflexivity Ferrers
  shows False
  sledgehammer oops
  nitpick [satisfy]
  
(* Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity*)

theorem AcyclconsK:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

theorem QuasiconsK:
  assumes Quasitransit
  shows True
  nitpick [show_all,satisfy] 
  oops



(* Sledgehammer shows consistency if transitivity is weakened into 
quasi-tran*)

theorem SuzuConsK:
  assumes Suzumura
  shows True
  nitpick [show_all,satisfy,card=4]
  oops

theorem SuzuInConsK:
  assumes Suzumura
  shows False
  sledgehammer
  oops





