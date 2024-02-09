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

(* Sledgehammer finds PP0-PP2 XYZ  given 
transitivity of the betterness relation in the models*)

theorem T0:
  assumes transitivity
  shows False
  sledgehammer  (*no proof found*)
  nitpick  (*time out*) 
  oops  

(* Nitpick shows consistency in the absence of transitivity*)

theorem T1:
  shows True
  nitpick [satisfy, card i=3,show_all]   (*model found*)
  oops

(* Sledgehammer confirms inconsistency in the presence of the interval order condition*)

theorem T2:
  assumes reflexivity and Ferrers
  shows False
  sledgehammer 

  
(* Nitpick shows consistency if transitivity is weakened into acyclicity or quasi-transitivity*)

theorem T3:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops


abbreviation two 
  where "two \<equiv> \<exists>x y. (x \<^bold>r y) \<and> \<not>(y \<^bold>r x)"

theorem T4:
  assumes Quasitransit 
  shows True
  using two
  nitpick [show_all,satisfy,card=3] 
  oops

theorem T5:
  assumes Quasitransit
  shows False
  sledgehammer
  oops

end



















  