theory mere_addition  (* Christoph Benzmüller, Xavier Parent, 2022  *)

imports cube

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

theorem TransIncons:
  assumes transitivity
  shows False 
  sledgehammer
  by (metis P0 P1 P2 assms) oops
(* Sledgehammer finds P0-P2 inconsistent given transitivity of the
 betterness relation in the models*)

lemma True nitpick [satisfy, card i=3] oops 

(* Nitpick shows consistency in the absence of transitivity*)

theorem Quasicons:
  assumes Quasitransit
  shows False
  nitpick [card=4] oops

(* Nitpick shows consistency if transitivity is weakened into 
quasi-transitivity*)

theorem Acyclcons:
  assumes loopfree
  shows true
  sledgehammer oops
  nitpick [satisfy,card=3] 

(* Nitpick shows consistency if transitivity is weakened into 
quasi-transitivity*)







end



















  