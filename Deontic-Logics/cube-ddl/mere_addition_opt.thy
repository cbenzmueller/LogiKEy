theory mere_addition_opt  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma>

(*the mere addition scenario*)

(*** With optimality  ***)


axiomatization where
(* A is striclty better than B*)
 P0: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>A|A\<^bold>\<or>B>\<^bold>\<and>\<odot><\<^bold>\<not>B|A\<^bold>\<or>B>)\<rfloor>" and
(* Aplus is at least as good as A*)
 P1: "\<lfloor>\<^bold>\<not>\<odot><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 P2: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<odot><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>"

(* Sledgehammer finds P0-P2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem T0:
  assumes transitivity
  shows False 
  using P0 P1 P2 assms
  sledgehammer
  by (metis P0 P1 P2 assms)


(* Nitpick shows consistency in the absence of transitivity*)

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



















  