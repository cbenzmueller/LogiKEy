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
  by (metis P0 P1 P2 assms)
(* Sledgehammer finds P1-P3 inconsistent given transitivity of the
 betterness relation in the models*)

lemma True nitpick [satisfy, card i=3] oops (* Nitpick shows 
consistency in the absence of transitivity*)

end
















the following is some trash--I could not make it work with permission and > on formulas
lemma Transit: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  sledgehammer (*proof found -- this is not correct*) oops
  nitpick [show_all] oops


abbreviation epref  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("_\<ge>_") (* weak preference over formulas*)
  where "\<phi>\<ge>\<psi> \<equiv> \<P><\<phi>|\<phi>\<or>\<psi>>"

lemma
  assumes "transitivity"
  and "\<lfloor>(\<ge>\<chi>) \<and> \<not>(\<chi>\<ge>\<phi>)\<rfloor>"
  and  "\<lfloor>(\<psi>\<ge>\<phi>)\<rfloor>"
  and "\<lfloor>(\<chi>\<ge>\<psi>) \<and> \<not>(\<psi>\<ge>\<chi>)\<rfloor>"
  shows False
  sledgehammer [user_axioms] oops
  nitpick



  