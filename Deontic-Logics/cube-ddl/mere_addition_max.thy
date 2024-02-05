theory mere_addition_max  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>

(*the mere addition scenario*)
(*** With Maximality  ***)

axiomatization where
(* A is striclty better than B*)
 PP0: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<circle><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
(* Aplus is at least as good as A*)
 PP1: "\<lfloor>\<^bold>\<not>\<circle><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 PP2: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<circle><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>"

(* Sledgehammer finds PP0-PP2 inconsistent given 
transitivity of the betterness relation in the models*)

theorem TransInconsMax:
  assumes transitivity
  shows False 
  sledgehammer oops 
  oops
  
(* Nitpick shows consistency in the absence of transitivity*)

lemma True
  nitpick [satisfy, card i=3]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem ioInconsMax:
  assumes reflexivity Ferrers
  shows False
  sledgehammer 

  
(* Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity*)

theorem AcyclconsMax:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

theorem QuasiconsMax:
  assumes Quasitransit
  shows True
  nitpick [show_all,satisfy] 
  oops

theorem QuasiInconsMax:
  assumes Quasitransit
  shows False
  sledgehammer
  oops

(* Sledgehammer shows consistency if transitivity is weakened into 
quasi-tran*)

theorem SuzuConsMax:
  assumes Suzumura
  shows True
  nitpick [show_all,satisfy,card=4]
  oops

theorem SuzuInconsMax:
  assumes Suzumura
  shows False
  sledgehammer
  oops








end



















  