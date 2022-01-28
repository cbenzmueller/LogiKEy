theory "Zorn-lemma"
  imports misc HOL.Zorn
begin

(*Introduces technical definitions for translations between Isabelle/HOL's sets and predicates*)
definition set2pred1::"'a set \<Rightarrow> 'a Set" ("\<lbrakk>_\<rbrakk>\<^sup>1") where "\<lbrakk>S\<rbrakk>\<^sup>1 \<equiv> \<lambda>x. x \<in> S"
definition pred2set1::"'a Set \<Rightarrow> 'a set" ("\<lbrace>_\<rbrace>\<^sup>1") where "\<lbrace>P\<rbrace>\<^sup>1 \<equiv> {x. P x}"
definition set2pred2::"'a set set \<Rightarrow> 'a Set Set" ("\<lbrakk>_\<rbrakk>\<^sup>2") where "\<lbrakk>S\<rbrakk>\<^sup>2 \<equiv> \<lambda>X. \<lbrace>X\<rbrace>\<^sup>1 \<in> S"
definition pred2set2::"'a Set Set \<Rightarrow> 'a set set" ("\<lbrace>_\<rbrace>\<^sup>2") where "\<lbrace>P\<rbrace>\<^sup>2 \<equiv> {X. P \<lbrakk>X\<rbrakk>\<^sup>1}"

(*Proves useful translation lemmas between Isabelle/HOL's sets and predicates*)
lemma trans1a: "A = \<lbrakk>\<lbrace>A\<rbrace>\<^sup>1\<rbrakk>\<^sup>1" unfolding set2pred1_def pred2set1_def by simp
lemma trans1b: "A = \<lbrace>\<lbrakk>A\<rbrakk>\<^sup>1\<rbrace>\<^sup>1" unfolding set2pred1_def pred2set1_def by simp
lemma trans2a: "A = \<lbrakk>\<lbrace>A\<rbrace>\<^sup>2\<rbrakk>\<^sup>2" unfolding set2pred2_def pred2set2_def using trans1a by (metis mem_Collect_eq)
lemma trans2b: "A = \<lbrace>\<lbrakk>A\<rbrakk>\<^sup>2\<rbrace>\<^sup>2" unfolding set2pred2_def pred2set2_def using trans1b by (metis (mono_tags, lifting) Collect_cong Collect_mem_eq)

(*Introduces technical definition to facilitate substitutions in subsequent proofs*)
definition chains :: "'a Set Set \<Rightarrow> 'a Set Set Set"
  where "chains A \<equiv> \<lambda>C. C \<subseteq> A \<and> chain C"

(*Proves useful translation lemmas between Isabelle/HOL's sets and predicates*)
lemma chainEq: "chain A \<longleftrightarrow> chain\<^sub>\<subseteq> \<lbrace>A\<rbrace>\<^sup>2" unfolding chain_subset_def chain_def
  by (smt (verit, ccfv_SIG) Collect_mono_iff pred2set1_def pred2set2_def set2pred1_def subsetI trans1a)
lemma chainsEq: "(X::'a set set) \<in> Zorn.chains \<lbrace>A\<rbrace>\<^sup>2 \<longleftrightarrow> chains (A::'a Set Set) \<lbrakk>X\<rbrakk>\<^sup>2" 
  using chainEq by (smt (verit, del_insts) chains_def Collect_mono_iff Zorn.chains_def mem_Collect_eq pred2set2_def set2pred2_def trans2a trans2b)

lemma ZornLemma: "allChainsHaveUB A \<Longrightarrow> \<exists>M. maximal A M id"
proof -
  fix A::"'a Set Set"
  let ?A = "\<lbrace>A\<rbrace>\<^sup>2"
  assume "allChainsHaveUB A"
  hence "\<forall>C\<in>Zorn.chains ?A. \<exists>U\<in>?A. \<forall>X\<in>C. Set.subset_eq X U" (* uses subset relation from the library *)
    using allChainsHaveUB_def upper_bound_def chainsEq by (smt (z3) chains_def mem_Collect_eq pred2set1_def pred2set2_def subsetI trans1a trans1b trans2b)
  hence "\<exists>M\<in>?A. \<forall>X\<in>?A. Set.subset_eq M X \<longrightarrow> X = M" 
    by (simp add: Zorn.Zorn_Lemma2) (* uses Zorn's lemma from the library*)
  thus "\<exists>M. maximal A M id"
    unfolding maximal_def id_apply by (metis Collect_mono_iff pred2set1_def set2pred2_def trans1a trans1b trans2a)
qed

lemma ZornLemma2: "allChainsHaveUB A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)"
proof -
  fix A::"'a Set Set"
  assume "allChainsHaveUB A"
  {
    fix X assume *: "A X"
    let ?F= "\<lambda>Y. A Y \<and> X \<subseteq> Y"
    have "allChainsHaveUB ?F" 
      by (smt (verit, del_insts) "*" \<open>allChainsHaveUB A\<close> allChainsHaveUB_def upper_bound_def)
    hence "\<exists>M. maximal ?F M id" by (simp add: ZornLemma)
    then obtain M where max: "maximal ?F M id" by (rule exE)
    hence gtX: "X \<subseteq> M" by (simp add: maximal_def)
    moreover from max have "maximal A M id"  
      by (smt (verit) id_apply maximal_def)
    ultimately have "\<exists>M. maximal A M id \<and> X \<subseteq> M" by blast
  }
  thus "\<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)" by blast
qed

lemma ZornLemma_\<omega>: "\<omega>-cpo A \<Longrightarrow> \<exists>M. maximal A M id" by (simp add: ZornLemma omegaCompleteUB)
lemma ZornLemma2_\<omega>: "\<omega>-cpo A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)" by (simp add: ZornLemma2 omegaCompleteUB)


(****************************************************************)
(************* TODO: Relativized variants ***********************)
(****************************************************************)

(* TODO: prove the following bridge lemmas (seem prima facie true)*)
lemma bridge1: "allChainsHaveUB A \<Longrightarrow> \<exists>M. maximal A M id \<Longrightarrow> \<exists>N. maximal\<^sup>U A N id" sorry
lemma bridge2: "allChainsHaveUB\<^sup>U A \<Longrightarrow> allChainsHaveUB A" sorry

lemma ZornLemma_rel: "allChainsHaveUB\<^sup>U A \<Longrightarrow> \<exists>M. maximal\<^sup>U A M id" by (simp add: ZornLemma bridge1 bridge2)
lemma ZornLemma2_rel: "allChainsHaveUB\<^sup>U A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M)"
  using ZornLemma2 bridge1 bridge2 sorry (* TODO: prove(?)*)

lemma ZornLemma_\<omega>_rel: "\<omega>-cpo\<^sup>U A \<Longrightarrow> \<exists>M. maximal\<^sup>U A M id" by (simp add: ZornLemma_rel omegaCompleteUB_rel)
lemma ZornLemma2_\<omega>_rel: "\<omega>-cpo\<^sup>U A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M)" by (simp add: ZornLemma2_rel omegaCompleteUB_rel)

end