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


(* Sledgehammer unable to show consistency 
transitivity of the betterness relation in the models*)

abbreviation twoworlds
  where "twoworlds   \<equiv> \<exists>w v. r w v \<and> \<not> (r v w)"

theorem T0:
  assumes transitivity and twoworlds
  shows True
  nitpick  [show_all,satisfy,card=3](*time out*) 
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
  sledgehammer oops

  
(* Nitpick shows consistency if transitivity is weakened into acyclicity*)

theorem T3:
  assumes loopfree
  shows True
  nitpick [show_all,satisfy,card=3] (* model found for card i=3 *) 
  oops

(* Nitpick should be able to show consistency if transitivity is weakened into quasi-transitivity*)

theorem T4:
  assumes Quasitransit 
  shows True
  nitpick [show_all,satisfy,card=3] 
  oops

end




















  