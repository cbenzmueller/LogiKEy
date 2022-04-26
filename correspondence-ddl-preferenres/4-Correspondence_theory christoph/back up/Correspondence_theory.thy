theory  Correspondence_theory  imports DDLE 
begin  (*System F *)
lemma limited_corresponds_to_Dstar: 
 "(\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x)) \<longleftrightarrow> (\<forall>\<Phi> \<Psi>. \<lfloor>\<diamond>\<Phi> \<^bold>\<rightarrow> (\<circle><\<Psi>|\<Phi>>  \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>>)\<rfloor>)"
  unfolding ddecond_def ddediomond_def ddeimp_def ddeneg_def ddevalid_def  sledgehammer
  by auto

(*System G  *)
lemma limited_trans_corresponds_to_SP_Dstar_1:
 "((\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x)) \<and> (\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z))
  \<longrightarrow>
  ((\<forall>\<Phi> \<Psi> \<chi>.\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>> \<^bold>\<and> \<circle><\<Psi>\<^bold>\<rightarrow>\<chi>|\<Phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<Phi>\<^bold>\<and>\<Psi>>\<rfloor>) \<and> (\<forall>\<Phi> \<Psi>.\<lfloor>\<diamond>\<Phi> \<^bold>\<rightarrow> (\<circle><\<Psi>|\<Phi>> \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>>)\<rfloor>))"
  unfolding ddecond_def ddediomond_def ddeimp_def ddeneg_def ddeand_def ddevalid_def ddeopt_def
  sledgehammer by smt   (* this direction is provable *)

lemma limited_trans_corresponds_to_SP_Dstar_2: (* this is still too hard for the ATPs *)
 "((\<forall>\<Phi> \<Psi> \<chi>.\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>> \<^bold>\<and> \<circle><\<Psi>\<^bold>\<rightarrow>\<chi>|\<Phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<Phi>\<^bold>\<and>\<Psi>>\<rfloor>) \<and> (\<forall>\<Phi> \<Psi>.\<lfloor>\<diamond>\<Phi> \<^bold>\<rightarrow> (\<circle><\<Psi>|\<Phi>> \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>>)\<rfloor>))
  \<longrightarrow>
  ((\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x)) \<and> (\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z))"
  unfolding ddecond_def ddediomond_def ddeimp_def ddeneg_def ddeand_def ddevalid_def ddeopt_def
(*
  sledgehammer[timeout=600] () nitpick[timeout=600] nunchaku[timeout=600] (* nunchaku says no countermodel *)
  sledgehammer [timeout=600, remote_leo2 remote_leo3 remote_satallax] ()
   by smt
*)
  (* this direction unfortunately not yet, but we also do not get a countermodel; proof might be to hard *)
  oops

lemma limited_trans_corresponds_to_SP_Dstar_2a: (* splitting the conjunct, limitednedd is easy for the ATPs*)
 "((\<forall>\<Phi> \<Psi> \<chi>.\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>> \<^bold>\<and> \<circle><\<Psi>\<^bold>\<rightarrow>\<chi>|\<Phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<Phi>\<^bold>\<and>\<Psi>>\<rfloor>) \<and> (\<forall>\<Phi> \<Psi>.\<lfloor>\<diamond>\<Phi> \<^bold>\<rightarrow> (\<circle><\<Psi>|\<Phi>> \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>>)\<rfloor>))
  \<longrightarrow>
  (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
  unfolding ddecond_def ddediomond_def ddeimp_def ddeneg_def ddeand_def ddevalid_def ddeopt_def
  sledgehammer by auto 


lemma limited_trans_corresponds_to_SP_Dstar_2b: (* splitting the conjunct, transitivity is too hard for the ATPs*)
 "((\<forall>\<Phi> \<Psi> \<chi>.\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>> \<^bold>\<and> \<circle><\<Psi>\<^bold>\<rightarrow>\<chi>|\<Phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<Phi>\<^bold>\<and>\<Psi>>\<rfloor>) \<and> (\<forall>\<Phi> \<Psi>.\<lfloor>\<diamond>\<Phi> \<^bold>\<rightarrow> (\<circle><\<Psi>|\<Phi>> \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<Psi>|\<Phi>>)\<rfloor>))
  \<longrightarrow>
  ((\<forall>x y z. (x r y \<and> y r z) \<longrightarrow> x r z))"
  unfolding ddecond_def ddediomond_def ddeimp_def ddeneg_def ddeand_def ddevalid_def 
(*
  sledgehammer () nitpick nunchaku
  sledgehammer [timeout=600, remote_leo2 remote_leo3 remote_satallax] ()
   by smt
*)

  (* this direction unfortunately not yet, but we also do not get a countermodel; proof might be to hard *)
  sorry



(*** end of header part ***)


 

end