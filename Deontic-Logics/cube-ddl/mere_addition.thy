theory mere_addition  (* Christoph Benzmüller, Xavier Parent, 2022  *)

imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>

(*the mere addition scenario*)

axiomatization where
(* A is striclty better than B*)
 P0: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<odot><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
(* Aplus is at least as good as A*)
 P1: "\<lfloor>\<^bold>\<not>\<odot><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 P2: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<odot><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>"

(* Sledgehammer finds P0-P2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem TransIncons:
  assumes transitivity
  shows False 
  sledgehammer
  by (metis P0 P1 P2 assms)
  
  
(* Nitpick shows consistency in the absence of transitivity*)

lemma true
  nitpick [satisfy, card i=3]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem io:
  assumes reflexivity Ferrers
  shows false
  sledgehammer 
  by (metis P0 P1 P2 assms(2))
  
(* Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity*)

theorem Acyclcons:
  assumes loopfree
  shows true
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

theorem Quasicons2:
  assumes Quasitransit
  shows true
  nitpick [show_all,satisfy,card=4] 
  oops





(* Sledgehammer shows consistency if transitivity is weakened into 
quasi-tran*)

theorem Suzucons:
  assumes Suzumura
  shows true
  nitpick [show_all,satisfy,card=4]
  oops

theorem Suzucons:
  assumes Suzumura
  shows false
  sledgehammer
  oops


end



















  