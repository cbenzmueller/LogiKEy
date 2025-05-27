theory PMLinHOL_faithfulness_tests  imports PMLinHOL_deep PMLinHOL_shallow PMLinHOL_shallow_minimal   (* C.B. 2025 *)                                                                                (* Christoph Benzmüller, 2025 *)
begin                 
\<comment>\<open>Mappings: deep to maximal shallow and deep to minimal shallow\<close>
  primrec DpToShMax ("\<lparr>_\<rparr>") where  "\<lparr>\<phi>\<^sup>d\<rparr>  = \<phi>\<^sup>s" | "\<lparr>\<not>\<^sup>d \<phi>\<rparr> = \<not>\<^sup>s \<lparr>\<phi>\<rparr>" | "\<lparr>\<phi> \<supset>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<supset>\<^sup>s \<lparr>\<psi>\<rparr>" | "\<lparr>\<box>\<^sup>d \<phi>\<rparr> = \<box>\<^sup>s \<lparr>\<phi>\<rparr>" 
  primrec DpToShMin  ("\<lbrakk>_\<rbrakk>") where "\<lbrakk>\<phi>\<^sup>d\<rbrakk>  = \<phi>\<^sup>m" | "\<lbrakk>\<not>\<^sup>d \<phi>\<rbrakk> = \<not>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" | "\<lbrakk>\<phi> \<supset>\<^sup>d \<psi>\<rbrakk> = \<lbrakk>\<phi>\<rbrakk> \<supset>\<^sup>m \<lbrakk>\<psi>\<rbrakk>" | "\<lbrakk>\<box>\<^sup>d \<phi>\<rbrakk> = \<box>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" 
\<comment>\<open>Proving faithfulness between deep and maximal shallow\<close>
  theorem Faithful1a:    "\<forall>W R V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>"     apply induct by auto
  theorem Faithful1b:    "\<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>"                                                        using Faithful1a by auto
\<comment>\<open>Proving faithfulness between deep and minimal shallow\<close>
  theorem Faithful2:      "\<forall>w. \<langle>(\<lambda>x::\<w>. True),R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>"                 apply induct by auto
\<comment>\<open>Proving faithfulness maximal shallow and minimal shallow\<close>
  theorem Faithful3:      "\<forall>w. \<langle>(\<lambda>x::\<w>. True),R,V\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>"               apply induct by auto
\<comment>\<open>Additional check for soundness for the minimal shallow embedding\<close>
(*
  lemma Sound1: "\<Turnstile>\<^sup>m \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lbrakk>\<phi>\<rbrakk> \<and> \<Turnstile>\<^sup>d \<phi>)"     sledgehammer oops
  lemma Sound2: "\<Turnstile>\<^sup>m \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lbrakk>\<phi>\<rbrakk> \<and> \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>)"  sledgehammer oops
  lemma Sound3: "\<Turnstile>\<^sup>s  \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lparr>\<phi>\<rparr> \<and> \<Turnstile>\<^sup>d \<phi>)"     sledgehammer oops
  lemma Sound4: "\<Turnstile>\<^sup>s  \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lparr>\<phi>\<rparr> \<and> \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>)"   sledgehammer oops
*)

abbreviation(input) "AxT \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>"
abbreviation(input) "AxB \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"
abbreviation(input) "Ax4 \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)"


lemma "\<exists>\<psi>. \<Turnstile>\<^sup>d \<psi>" apply simp nitpick[satisfy,card \<S> =2,card \<w>=2] oops
lemma "\<exists>\<psi>. AxT \<longrightarrow> \<Turnstile>\<^sup>d \<psi>" nitpick[satisfy] oops
lemma "\<exists>\<psi>. \<not>(\<Turnstile>\<^sup>d \<psi>) \<and> (AxT \<longrightarrow> \<Turnstile>\<^sup>d \<psi>)" nitpick[satisfy,card \<S> =1,card \<w>=2] oops
lemma "\<exists>\<psi>. \<not>(\<Turnstile>\<^sup>d \<psi>) \<and> (AxB \<longrightarrow> \<Turnstile>\<^sup>d \<psi>)" nitpick[satisfy,card \<S> =1,card \<w>=2] oops
lemma "\<exists>\<psi>. \<not>(\<Turnstile>\<^sup>d \<psi>) \<and> (Ax4 \<longrightarrow> \<Turnstile>\<^sup>d \<psi>)" nitpick[satisfy,card \<S> =1,card \<w>=2] oops
lemma "\<exists>\<psi>. \<not>(AxT \<longrightarrow> \<Turnstile>\<^sup>d \<psi>) \<and> (AxB \<longrightarrow> \<Turnstile>\<^sup>d \<psi>)" nitpick[satisfy,card \<S> =2,card \<w>=2] oops
lemma "\<exists>\<psi>. \<not>(AxT \<longrightarrow> \<Turnstile>\<^sup>d \<psi>) \<and> (AxT \<and> AxB \<longrightarrow> \<Turnstile>\<^sup>d \<psi>)" nitpick[satisfy,card \<S> =2,card \<w>=2] oops


nitpick_params
end


