theory MFilter imports HOML  
begin (*Some abbreviations for auxiliary operations*)
abbreviation a::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("_\<^bold>\<in>_") 
                               where "x\<^bold>\<in>S \<equiv> S x"
abbreviation b::\<gamma> ("\<^bold>\<emptyset>") where "\<^bold>\<emptyset> \<equiv> \<lambda>x. \<^bold>\<bottom>"  
abbreviation c::\<gamma> ("\<^bold>U") where "\<^bold>U \<equiv> \<lambda>x. \<^bold>\<top>"
abbreviation d::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<sigma>" ("_\<^bold>\<subseteq>_") 
             where "\<phi>\<^bold>\<subseteq>\<psi> \<equiv> \<^bold>\<forall>x.((\<phi> x) \<^bold>\<rightarrow> (\<psi> x))"
abbreviation e::"\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>" ("_\<^bold>\<sqinter>_") 
             where "\<phi>\<^bold>\<sqinter>\<psi> \<equiv> \<lambda>x.((\<phi> x) \<^bold>\<and> (\<psi> x))"
abbreviation f::"\<gamma>\<Rightarrow>\<gamma>" ("\<inverse>_") where "\<inverse>\<psi> \<equiv> \<lambda>x. \<^bold>\<not>(\<psi> x)"  

(*Definition of modal filter*)
abbreviation g::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("Filter") 
 where "Filter \<Phi> \<equiv> (((\<^bold>U\<^bold>\<in>\<Phi>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<Phi>))
         \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (((\<phi>\<^bold>\<in>\<Phi>) \<^bold>\<and> (\<phi>\<^bold>\<subseteq>\<psi>)) \<^bold>\<rightarrow> (\<psi>\<^bold>\<in>\<Phi>))))
         \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (((\<phi>\<^bold>\<in>\<Phi>) \<^bold>\<and> (\<psi>\<^bold>\<in>\<Phi>)) \<^bold>\<rightarrow> ((\<phi>\<^bold>\<sqinter>\<psi>)\<^bold>\<in>\<Phi>)))"

(*Definition of modal ultrafilter *)
abbreviation h::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("UFilter") where 
 "UFilter \<Phi> \<equiv> (Filter \<Phi>)\<^bold>\<and>(\<^bold>\<forall>\<phi>.((\<phi>\<^bold>\<in>\<Phi>) \<^bold>\<or> ((\<inverse>\<phi>)\<^bold>\<in>\<Phi>)))"

(*Modal Filter and ultrafilter are consistent*)
lemma "\<lfloor>\<^bold>\<forall>\<Phi> \<phi>.((UFilter \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>((\<phi>\<^bold>\<in>\<Phi>) \<^bold>\<and> ((\<inverse>\<phi>)\<^bold>\<in>\<Phi>)))\<rfloor>" 
  by force
end



