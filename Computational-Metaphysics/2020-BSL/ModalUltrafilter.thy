theory ModalUltrafilter imports IHOML  
begin
(**Some abbreviations for operations on \<delta>/\<gamma>-sets in modal context**) 
  abbreviation elem_delta::"\<delta>\<Rightarrow>(\<delta>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (infixr"\<^bold>\<in>\<^sup>\<delta>"99) where "x\<^bold>\<in>\<^sup>\<delta>S \<equiv> S x"
  abbreviation elem_gamma::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (infixr"\<^bold>\<in>\<^sup>\<gamma>"99) where "x\<^bold>\<in>\<^sup>\<gamma>S \<equiv> S x"
  abbreviation emptySet_delta::\<delta> ("\<^bold>\<emptyset>\<^sup>\<delta>") where "\<^bold>\<emptyset>\<^sup>\<delta> \<equiv> \<lambda>x. False"  
  abbreviation emptySet_gamma::\<gamma> ("\<^bold>\<emptyset>\<^sup>\<gamma>") where "\<^bold>\<emptyset>\<^sup>\<gamma> \<equiv> \<lambda>x. \<^bold>\<bottom>"  
  abbreviation fullSet_delta::\<delta> ("\<^bold>U\<^sup>\<delta>") where "\<^bold>U\<^sup>\<delta> \<equiv> \<lambda>x. True"  
  abbreviation fullSet_gamma::\<gamma> ("\<^bold>U\<^sup>\<gamma>") where "\<^bold>U\<^sup>\<gamma> \<equiv> \<lambda>x. \<^bold>\<top>"
  abbreviation entails_delta::"\<delta>\<Rightarrow>\<delta>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<subseteq>\<^sup>\<delta>"51) where "\<phi>\<^bold>\<subseteq>\<^sup>\<delta>\<psi> \<equiv> \<lambda>w. \<forall>x. \<phi> x \<longrightarrow> \<psi> x"  
  abbreviation entails_gamma::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<subseteq>\<^sup>\<gamma>"51) where "\<phi>\<^bold>\<subseteq>\<^sup>\<gamma>\<psi> \<equiv> \<^bold>\<forall>x. \<phi> x \<^bold>\<rightarrow> \<psi> x"  
  abbreviation andPred_delta::"\<delta>\<Rightarrow>\<delta>\<Rightarrow>\<delta>" (infixr"\<^bold>\<sqinter>\<^sup>\<delta>"51) where "\<phi>\<^bold>\<sqinter>\<^sup>\<delta>\<psi> \<equiv> \<lambda>x. \<phi> x \<and> \<psi> x"  
  abbreviation andPred_gamma::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>" (infixr"\<^bold>\<sqinter>\<^sup>\<gamma>"51) where "\<phi>\<^bold>\<sqinter>\<^sup>\<gamma>\<psi> \<equiv> \<lambda>x. \<phi> x \<^bold>\<and> \<psi> x"  
  abbreviation negpred_delta::"\<delta>\<Rightarrow>\<delta>" ("\<inverse>\<^sup>\<delta>_"[52]53) where "\<inverse>\<^sup>\<delta>\<psi> \<equiv> \<lambda>x. \<not>(\<psi> x)"  
  abbreviation negpred_gamma::"\<gamma>\<Rightarrow>\<gamma>" ("\<inverse>\<^sup>\<gamma>_"[52]53) where "\<inverse>\<^sup>\<gamma>\<psi> \<equiv> \<lambda>x. \<^bold>\<not>(\<psi> x)"  
(**Definition of \<delta>/\<gamma>-Filter in modal context**) 
  abbreviation filter_delta::"(\<delta>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<delta>-Filter") where "\<delta>-Filter \<Phi> \<equiv> 
     \<^bold>U\<^sup>\<delta>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<delta>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<delta>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<delta>\<Phi>) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<delta>\<Phi>) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<delta>\<psi>)\<^bold>\<in>\<^sup>\<delta>\<Phi>))"
  abbreviation filter_gamma::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<gamma>-Filter") where "\<gamma>-Filter \<Phi> \<equiv> 
     \<^bold>U\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<and> \<^bold>\<not>\<^bold>\<emptyset>\<^sup>\<gamma>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>\<gamma>\<psi>) \<^bold>\<rightarrow> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<Phi>) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>.(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<and> \<psi>\<^bold>\<in>\<^sup>\<gamma>\<Phi>) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<^sup>\<gamma>\<psi>)\<^bold>\<in>\<^sup>\<gamma>\<Phi>))"
(**\<delta>/\<gamma>-Filter are consistent**) 
  lemma cons_delta: "\<lfloor>\<^bold>\<forall>\<Phi> \<phi>. \<delta>-Filter \<Phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<phi>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<and> (\<inverse>\<^sup>\<delta>\<phi>)\<^bold>\<in>\<^sup>\<delta>\<Phi>)\<rfloor>" by fastforce
  lemma cons_gamma: "\<lfloor>\<^bold>\<forall>\<Phi> \<phi>. \<gamma>-Filter \<Phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<phi>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<and> (\<inverse>\<^sup>\<gamma>\<phi>)\<^bold>\<in>\<^sup>\<gamma>\<Phi>)\<rfloor>" by fastforce
(**Definition of \<delta>/\<gamma>-Ultrafilter in modal context**)
  abbreviation ultrafilter_delta::"(\<delta>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<delta>-Ultrafilter") where 
    "\<delta>-Ultrafilter \<Phi> \<equiv> \<delta>-Filter \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<delta>\<Phi> \<^bold>\<or> (\<inverse>\<^sup>\<delta>\<phi>)\<^bold>\<in>\<^sup>\<delta>\<Phi>)"
  abbreviation ultrafilter_gamma::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<gamma>-Ultrafilter") where 
    "\<gamma>-Ultrafilter \<Phi> \<equiv> \<gamma>-Filter \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<^sup>\<gamma>\<Phi> \<^bold>\<or> (\<inverse>\<^sup>\<gamma>\<phi>)\<^bold>\<in>\<^sup>\<gamma>\<Phi>)"
end