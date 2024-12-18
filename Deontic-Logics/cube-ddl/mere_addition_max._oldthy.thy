theory mere_addition_max  (* Christoph Benzmüller, Xavier Parent, 2024  *)

imports DDLcube

begin

consts a::\<sigma> aplus::\<sigma> b::\<sigma>  i1::i i2::i i3::i i4::i i5::i i6::i i7::i i8::i 

(*the mere addition scenario*)
(*** With Maximality  ***)

axiomatization where
(* A is striclty better than B*)
 PP0: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>a|a\<^bold>\<or>b>\<^bold>\<and>\<circle><\<^bold>\<not>b|a\<^bold>\<or>b>)\<rfloor>" and
(* Aplus is at least as good as A*)
 PP1: "\<lfloor>\<^bold>\<not>\<circle><\<^bold>\<not>aplus|a\<^bold>\<or>aplus>\<rfloor>" and
(* B is strictly better than Aplus*)
 PP2: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>b|aplus\<^bold>\<or>b> \<^bold>\<and> \<circle><\<^bold>\<not>aplus|aplus\<^bold>\<or>b>)\<rfloor>" 


(* Sledgehammer unable to show consistency transitivity of the betterness 
   relation in the models*)

theorem T0:
  assumes transitivity  
  shows True
  nitpick [satisfy,card i=3,show_all]   
(*  nitpick  [show_all,satisfy,card i=3](*time out*) *)
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

(* Transitivity or quasi-transitivity: Nitpick shows inconsistency assuming a finite model
   of cardinality (up to) seven (if we provide the exact dependencies); for higher cardinalities 
   it returns a time out (depending on computing it may prove falsity also for cardinality eight, 
   etc. *)

theorem T4:
    assumes
      transitivity and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y= i7"
    shows False
  sledgehammer(PP0 PP1 PP2 assms assfactor_def)  (*proof found*)
  oops

theorem T5:
    assumes
      Quasitransit and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y=i7"
    shows False
  sledgehammer(PP0 PP1 PP2 assms assfactor_def)  (*proof found*)
  oops

(* Testing whether infinity holds — infinity is defined as: there is a surjective mapping G from 
   domain i to a proper subset M of domain i*)

abbreviation "infinity \<equiv> \<exists>M. (\<exists>z::i. \<not>(M z) \<and> (\<exists>G. (\<forall>y::i. (\<exists>x. (M x) \<and> (G x) = y))))"

lemma "infinity" nitpick[show_all] oops (* countermodel found *)


(* No we study infinity under the assumption of (quasi-)transitivity: we do not get any finite
   countermodels reported anymore *)

lemma 
  assumes transitivity
  shows   infinity
  nitpick[show_all]  (* no countermodel found anymore; nitpicks runs out of time *)
  sledgehammer       (* but the provers are still too weak to prove it automatically *)
  oops


lemma 
  assumes Quasitransit 
  shows   infinity
  nitpick[show_all]  (* no countermodel found anymore; nitpicks runs out of time *)
  sledgehammer       (* but the provers are still too weak to prove it automatically *)
  oops


end
