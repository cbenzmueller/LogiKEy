theory PMLinHOL_joint_tests  imports PMLinHOL_faithfulness  (* C.B. 2025 *)                                                                                (* Christoph Benzmüller, 2025 *)
begin                
nitpick_params[expect=genuine]
(*sledgehammer_params[timeout=600,expect=some,isar_proofs=false,max_proofs=1,provers=vampire,slices=1]*)
(*sledgehammer_params[timeout=100,expect=some,isar_proofs=false]*)

abbreviation(input) "AxTd \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>\<supset>\<^sup>d\<phi>)"
abbreviation(input) "AxTs \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>\<supset>\<^sup>s\<phi>)"
abbreviation(input) "AxTm \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>\<supset>\<^sup>m\<phi>)"

abbreviation(input) "AxBd \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>d \<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))"
abbreviation(input) "AxBs \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>s \<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))"
abbreviation(input) "AxBm \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>m \<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>))"

abbreviation(input) "Ax4d \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<box>\<^sup>d\<phi>))"
abbreviation(input) "Ax4s \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<box>\<^sup>s\<phi>))"
abbreviation(input) "Ax4m \<equiv>  (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<box>\<^sup>m\<phi>))"

abbreviation(input) "K \<equiv> True" 
abbreviation(input) "Kd \<equiv> True" 
abbreviation(input) "Ks \<equiv> True" 
abbreviation(input) "Km \<equiv> True" 

abbreviation(input) "KT \<equiv> reflexive R" 
abbreviation(input) "KTd \<equiv> AxTd" 
abbreviation(input) "KTs \<equiv> AxTs" 
abbreviation(input) "KTm \<equiv> AxTm" 

abbreviation(input) "KB \<equiv> symmetric R" 
abbreviation(input) "KBd \<equiv> AxBd" 
abbreviation(input) "KBs \<equiv> AxBs" 
abbreviation(input) "KBm \<equiv> AxBm" 

abbreviation(input) "K4 \<equiv> transitive R" 
abbreviation(input) "K4d \<equiv> Ax4d" 
abbreviation(input) "K4s \<equiv>  Ax4s" 
abbreviation(input) "K4m \<equiv> Ax4m" 

abbreviation(input) "KTB \<equiv>  reflexive R \<and> symmetric R" 
abbreviation(input) "KTBd \<equiv> AxTd \<and> AxBd" 
abbreviation(input) "KTBs \<equiv> AxTs \<and> AxBs" 
abbreviation(input) "KTBm \<equiv> AxTm \<and> AxBm" 

abbreviation(input) "KB4 \<equiv>  symmetric R \<and> transitive R" 
abbreviation(input) "KB4d \<equiv> AxBd \<and> Ax4d" 
abbreviation(input) "KB4s \<equiv> AxBs \<and> Ax4s" 
abbreviation(input) "KB4m \<equiv> AxBm \<and> Ax4m" 

abbreviation(input) "S4 \<equiv> reflexive R \<and> transitive R" 
abbreviation(input) "S4d \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>d \<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<box>\<^sup>d\<phi>))" 
abbreviation(input) "S4s \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>s \<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<box>\<^sup>s\<phi>))" 
abbreviation(input) "S4m \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<box>\<^sup>m\<phi>))" 

abbreviation(input) "S5 \<equiv> reflexive R \<and> symmetric R \<and> transitive R" 
abbreviation(input) "S5d \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>\<supset>\<^sup>d\<phi>) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>d \<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>\<supset>\<^sup>d\<box>\<^sup>d(\<box>\<^sup>d\<phi>))" 
abbreviation(input) "S5s \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>\<supset>\<^sup>s\<phi>) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>s \<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>\<supset>\<^sup>s\<box>\<^sup>s(\<box>\<^sup>s\<phi>))" 
abbreviation(input) "S5m \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>\<supset>\<^sup>m\<phi>) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<and> (\<forall>\<phi>. \<Turnstile>\<^sup>m \<box>\<^sup>m\<phi>\<supset>\<^sup>m\<box>\<^sup>m(\<box>\<^sup>m\<phi>))" 


abbreviation(input) ValDS5 ("\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 _") where 
  "(\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 \<phi>) \<equiv> (\<forall>W R V. \<forall>w:W.  (reflexive R \<and> symmetric R \<and> transitive R) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"
abbreviation(input) ValSS5 ("\<Turnstile>\<^sup>s\<^sub>S\<^sub>5 _") where 
  "(\<Turnstile>\<^sup>s\<^sub>S\<^sub>5 \<phi>) \<equiv> (\<forall>W R V. \<forall>w:W.  (reflexive R \<and> symmetric R \<and> transitive R) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi>)"
abbreviation(input) ValMS5 ("\<Turnstile>\<^sup>m\<^sub>S\<^sub>5 _") where 
  "(\<Turnstile>\<^sup>m\<^sub>S\<^sub>5 \<phi>) \<equiv> (\<forall>w::\<w>.  (reflexive R \<and> symmetric R \<and> transitive R) \<longrightarrow> w \<Turnstile>\<^sup>m  \<phi>)"


lemma "(\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 \<phi>) \<longrightarrow> (\<Turnstile>\<^sup>s\<^sub>S\<^sub>5 \<lparr>\<phi>\<rparr>)"  by (metis (full_types) Faithful1a)
lemma "(\<Turnstile>\<^sup>s\<^sub>S\<^sub>5 \<lparr>\<phi>\<rparr>) \<longrightarrow> (\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 \<phi>)"  by (metis (full_types) Faithful1a)
lemma "(\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 \<phi>) \<longrightarrow> (\<Turnstile>\<^sup>m\<^sub>S\<^sub>5 \<lbrakk>\<phi>\<rbrakk>)" by (metis (full_types) Faithful2)
lemma "(\<Turnstile>\<^sup>m\<^sub>S\<^sub>5 \<lbrakk>\<phi>\<rbrakk>) \<longrightarrow> (\<Turnstile>\<^sup>d\<^sub>S\<^sub>5 \<phi>)" sledgehammer nitpick oops

(* Cube Examples *)

(*
lemma "KT \<longrightarrow> KTm" sledgehammer oops (* proof found *)
lemma "KTm \<longrightarrow> KT" sledgehammer oops (* proof found *)

lemma "KB \<longrightarrow> KBm" sledgehammer oops (* proof found *)
lemma "KBm \<longrightarrow> KB" sledgehammer oops (* proof found *)

lemma "K4 \<longrightarrow> K4m" sledgehammer oops (* proof found *)
lemma "K4d \<longrightarrow> K4" sledgehammer  nitpick oops
lemma "K4s \<longrightarrow> K4" sledgehammer  nitpick  oops
lemma "K4m \<longrightarrow> K4" sledgehammer oops (* proof found *)

lemma "KT4 \<longrightarrow> KT4m" sledgehammer oops (* proof found *)
lemma "KT4m \<longrightarrow> KT4" sledgehammer oops (* proof found *)


lemma "KB4 \<longrightarrow> KB4m" sledgehammer oops (* proof found *)
lemma "KB4d \<longrightarrow> KB4" sledgehammer  nitpick oops
lemma "KB4s \<longrightarrow> KB4" sledgehammer  oops
lemma "KB4m \<longrightarrow> KB4" sledgehammer oops (* proof found *)


lemma "S4 \<longrightarrow> S4m" sledgehammer oops
lemma "S4d \<longrightarrow> S4" sledgehammer  nitpick oops
lemma "S4s \<longrightarrow> S4" sledgehammer  oops
lemma "S4m \<longrightarrow> S4" sledgehammer oops


lemma "S5 \<longrightarrow> S5m" sledgehammer oops (* proof found *)
lemma "S5d \<longrightarrow> S5" sledgehammer  oops
lemma "S5s \<longrightarrow> S5" sledgehammer  oops (* proof found *)
lemma "S5m \<longrightarrow> S5" sledgehammer  oops (* proof found *)
*)

(* Further Example *)

abbreviation(input) "F1d \<equiv> (\<forall>\<phi> \<psi> \<gamma>.  \<Turnstile>\<^sup>d  (\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<psi>) \<and>\<^sup>d \<box>\<^sup>d(\<psi> \<supset>\<^sup>d \<gamma>)) \<supset>\<^sup>d \<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<gamma>))"
abbreviation(input) "F1s \<equiv> (\<forall>\<phi> \<psi> \<gamma>.  \<Turnstile>\<^sup>s  (\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>) \<and>\<^sup>s \<box>\<^sup>s(\<psi> \<supset>\<^sup>s \<gamma>)) \<supset>\<^sup>s \<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<gamma>))"
abbreviation(input) "F1m \<equiv> (\<forall>\<phi> \<psi> \<gamma>. \<Turnstile>\<^sup>m  (\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>) \<and>\<^sup>m \<box>\<^sup>m(\<psi> \<supset>\<^sup>m \<gamma>)) \<supset>\<^sup>m \<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<gamma>))"


lemma "KT \<longrightarrow> F1m"    apply simp nitpick sledgehammer oops  (* proof found *)
lemma "KTd \<longrightarrow> F1d"   apply simp nitpick sledgehammer oops  (* proof found *)
lemma "KTs \<longrightarrow> F1s"    apply simp nitpick sledgehammer oops  (* proof found *)
lemma "KTm \<longrightarrow> F1m"  apply simp nitpick sledgehammer oops  (* proof found *)



lemma "KTB \<longrightarrow> F1m"    by simp
lemma "KTBd \<longrightarrow> F1d"   by simp
lemma "KTBs \<longrightarrow> F1s"    by simp
lemma "KTBm \<longrightarrow> F1m"  by simp

lemma "KT \<longrightarrow> F1m"    by simp
lemma "KTd \<longrightarrow> F1d"   by simp
lemma "KTs \<longrightarrow> F1s"    by simp
lemma "KTm \<longrightarrow> F1m"  by simp

lemma "KB \<longrightarrow> F1m"    by simp
lemma "KBd \<longrightarrow> F1d"   by simp
lemma "KBs \<longrightarrow> F1s"    by simp
lemma "KBm \<longrightarrow> F1m"  by simp

lemma "K \<longrightarrow> F1m"    by simp
lemma "Kd \<longrightarrow> F1d"   by simp
lemma "Ks \<longrightarrow> F1s"    by simp
lemma "Km \<longrightarrow> F1m"  by simp

abbreviation(input) "F2d \<equiv> (\<forall>\<phi>.  \<Turnstile>\<^sup>d  (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>))\<supset>\<^sup>d\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))"
abbreviation(input) "F2s \<equiv> (\<forall>\<phi>.  \<Turnstile>\<^sup>s  (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>))\<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))"
abbreviation(input) "F2m \<equiv> (\<forall>\<phi>. \<Turnstile>\<^sup>m  (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>))\<supset>\<^sup>m\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>))"

lemma "S5 \<longrightarrow> F2m"    nitpick sledgehammer oops  (* proof found *)
lemma "S5d \<longrightarrow> F2d"   nitpick sledgehammer oops  (* proof found *)
lemma "S5s \<longrightarrow> F2s"     nitpick sledgehammer oops  
lemma "S5m \<longrightarrow> F2m"   nitpick sledgehammer oops  (* proof found *)

lemma "KTB \<longrightarrow> F2m"    apply simp nitpick sledgehammer oops  (* proof found *)
lemma "KTBd \<longrightarrow> F2d"   apply simp nitpick sledgehammer oops  
lemma "KTBs \<longrightarrow> F2s"    apply simp nitpick sledgehammer oops  (* proof found *)
lemma "KTBm \<longrightarrow> F2m" apply simp nitpick sledgehammer oops  (* proof found *)


end

lemma "K \<longrightarrow> F2d"   apply simp nitpick sledgehammer oops
lemma "K \<longrightarrow> F2s"   apply simp nitpick sledgehammer oops
lemma "K \<longrightarrow> F2m"   apply simp nitpick sledgehammer oops
lemma "Kd \<longrightarrow> F2d"   apply simp nitpick sledgehammer oops
lemma "Ks \<longrightarrow> F2s"   apply simp nitpick sledgehammer oops
lemma "Km \<longrightarrow> F2m"  apply simp nitpick sledgehammer oops

lemma "KT \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "KT \<longrightarrow> F2s"   nitpick sledgehammer oops
lemma "KT \<longrightarrow> F2m"   nitpick sledgehammer oops
lemma "KTd \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "KTs \<longrightarrow> F2s"   nitpick sledgehammer oops  (* Ooops, Zipperpos can prove this *)
lemma "KTm \<longrightarrow> F2m"  nitpick sledgehammer oops

lemma "KB \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "KB \<longrightarrow> F2s"   nitpick sledgehammer oops
lemma "KB \<longrightarrow> F2m"   nitpick sledgehammer oops
lemma "KBd \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "KBs \<longrightarrow> F2s"   nitpick sledgehammer oops
lemma "KBm \<longrightarrow> F2m"  nitpick sledgehammer oops

lemma "K4 \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "K4 \<longrightarrow> F2s"   nitpick sledgehammer oops
lemma "K4 \<longrightarrow> F2m"   nitpick sledgehammer oops
lemma "K4d \<longrightarrow> F2d"   nitpick sledgehammer oops
lemma "K4s \<longrightarrow> F2s"   nitpick sledgehammer oops
lemma "K4m \<longrightarrow> F2m"  nitpick sledgehammer oops



end 
lemma assumes KT    shows F2d   nitpick sledgehammer oops
lemma assumes KT    shows F2s   nitpick sledgehammer oops
lemma assumes KT    shows F2m  nitpick sledgehammer oops
lemma assumes KTd  shows F2d  nitpick sledgehammer oops
lemma assumes KTs   shows F2s  nitpick sledgehammer oops
lemma assumes KTm shows  F2m nitpick sledgehammer oops

lemma assumes B    shows F2d   nitpick sledgehammer oops
lemma assumes B    shows F2s   nitpick sledgehammer oops
lemma assumes B    shows F2m  nitpick sledgehammer oops
lemma assumes Bd shows F2d  nitpick sledgehammer oops
lemma assumes Bs  shows F2s  nitpick sledgehammer oops
lemma assumes Bm shows F2m  nitpick sledgehammer oops

lemma assumes S4 shows F2d     nitpick sledgehammer oops
lemma assumes S4 shows F2s      nitpick sledgehammer oops
lemma assumes S4 shows F2m     nitpick sledgehammer oops
lemma assumes S4d shows F2d    nitpick sledgehammer oops
lemma assumes S4s  shows F2s    nitpick sledgehammer oops
lemma assumes S4m shows F2m  nitpick sledgehammer oops

lemma assumes S5 shows F2d     nitpick sledgehammer oops
lemma assumes S5 shows F2s      nitpick sledgehammer oops
lemma assumes S5 shows F2m     nitpick sledgehammer oops
lemma assumes S5d shows F2d    nitpick sledgehammer oops
lemma assumes S5s  shows F2s    nitpick sledgehammer oops
lemma assumes S5m shows F2m  nitpick sledgehammer oops

abbreviation(input) "F3d \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>d (\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>))\<supset>\<^sup>d\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)" 
abbreviation(input) "F3s \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>s  (\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))\<supset>\<^sup>s\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)" 
abbreviation(input) "F3m \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>m  (\<box>\<^sup>m(\<diamond>\<^sup>m \<phi>))\<supset>\<^sup>m\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)"

lemma assumes K    shows F3d   nitpick sledgehammer oops
lemma assumes K    shows F3s   nitpick sledgehammer oops
lemma assumes K    shows F3m  nitpick sledgehammer oops
lemma assumes Kd  shows  F3d  nitpick sledgehammer oops
lemma assumes Ks   shows  F3s  nitpick sledgehammer oops
lemma assumes Km shows  F3m nitpick sledgehammer oops

lemma assumes KT    shows F3d   nitpick sledgehammer oops
lemma assumes KT    shows F3s   nitpick sledgehammer oops
lemma assumes KT    shows F3m  nitpick sledgehammer oops
lemma assumes KTd  shows F3d  nitpick sledgehammer oops
lemma assumes KTs   shows F3s  nitpick sledgehammer oops
lemma assumes KTm shows  F3m nitpick sledgehammer oops

lemma assumes B    shows F3d   nitpick sledgehammer oops
lemma assumes B    shows F3s   nitpick sledgehammer oops
lemma assumes B    shows F3m  nitpick sledgehammer oops
lemma assumes Bd shows F3d  nitpick sledgehammer oops
lemma assumes Bs  shows F3s  nitpick sledgehammer oops
lemma assumes Bm shows F3m  nitpick sledgehammer oops

lemma assumes S4 shows F3d     nitpick sledgehammer oops
lemma assumes S4 shows F3s      nitpick sledgehammer oops
lemma assumes S4 shows F3m     nitpick sledgehammer oops
lemma assumes S4d shows F3d    nitpick sledgehammer oops
lemma assumes S4s  shows F3s    nitpick sledgehammer oops
lemma assumes S4m shows F3m  nitpick sledgehammer oops

lemma assumes S5 shows F3d     nitpick sledgehammer oops
lemma assumes S5 shows F3s      nitpick sledgehammer oops
lemma assumes S5 shows F3m     nitpick sledgehammer oops
lemma assumes S5d shows F3d    nitpick sledgehammer oops
lemma assumes S5s  shows F3s    nitpick sledgehammer oops
lemma assumes S5m shows F3m  nitpick sledgehammer oops


abbreviation(input) "F4d \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>d (\<diamond>\<^sup>d\<phi>)\<supset>\<^sup>d\<diamond>\<^sup>d(\<diamond>\<^sup>d\<phi>)" 
abbreviation(input) "F4s \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>s (\<diamond>\<^sup>s\<phi>)\<supset>\<^sup>s\<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)" 
abbreviation(input) "F4m \<equiv> \<forall>\<phi>.  \<Turnstile>\<^sup>m (\<diamond>\<^sup>m\<phi>)\<supset>\<^sup>m\<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)"

lemma assumes K    shows F4d   nitpick sledgehammer oops
lemma assumes K    shows F4s   nitpick sledgehammer oops
lemma assumes K    shows F4m  nitpick sledgehammer oops
lemma assumes Kd  shows  F4d  nitpick sledgehammer oops
lemma assumes Ks   shows  F4s  nitpick sledgehammer oops
lemma assumes Km shows  F4m nitpick sledgehammer oops

lemma assumes KT    shows F4d   nitpick sledgehammer oops
lemma assumes KT    shows F4s   nitpick sledgehammer oops
lemma assumes KT    shows F4m  nitpick sledgehammer oops
lemma assumes KTd  shows F4d  nitpick sledgehammer oops
lemma assumes KTs   shows F4s  nitpick sledgehammer oops
lemma assumes KTm shows  F4m nitpick sledgehammer oops

lemma assumes B    shows F4d   nitpick sledgehammer oops
lemma assumes B    shows F4s   nitpick sledgehammer oops
lemma assumes B    shows F4m  nitpick sledgehammer oops
lemma assumes Bd shows F4d  nitpick sledgehammer oops
lemma assumes Bs  shows F4s  nitpick sledgehammer oops
lemma assumes Bm shows F4m  nitpick sledgehammer oops

lemma assumes S4 shows F4d     nitpick sledgehammer oops
lemma assumes S4 shows F4s      nitpick sledgehammer oops
lemma assumes S4 shows F4m     nitpick sledgehammer oops
lemma assumes S4d shows F4d    nitpick sledgehammer oops
lemma assumes S4s  shows F4s    nitpick sledgehammer oops
lemma assumes S4m shows F4m  nitpick sledgehammer oops

lemma assumes S5 shows F4d     nitpick sledgehammer oops
lemma assumes S5 shows F4s      nitpick sledgehammer oops
lemma assumes S5 shows F4m     nitpick sledgehammer oops
lemma assumes S5d shows F4d    nitpick sledgehammer oops
lemma assumes S5s  shows F4s    nitpick sledgehammer oops
lemma assumes S5m shows F4m  nitpick sledgehammer oops

sledgehammer_params[timeout=600,expect=some,isar_proofs=false,max_proofs=1,provers=vampire,slices = 2]
lemma assumes S5m shows "reflexive R"  nitpick sledgehammer oops
end


