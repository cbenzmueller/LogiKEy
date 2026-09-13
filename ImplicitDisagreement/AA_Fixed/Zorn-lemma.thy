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
lemma trans2a: "A = \<lbrakk>\<lbrace>A\<rbrace>\<^sup>2\<rbrakk>\<^sup>2"
  unfolding set2pred2_def pred2set2_def set2pred1_def pred2set1_def by simp
lemma trans2b: "A = \<lbrace>\<lbrakk>A\<rbrakk>\<^sup>2\<rbrace>\<^sup>2"
  unfolding set2pred2_def pred2set2_def set2pred1_def pred2set1_def by simp

(*Introduces technical definition to facilitate substitutions in subsequent proofs*)
definition chains :: "'a Set Set \<Rightarrow> 'a Set Set Set"
  where "chains A \<equiv> \<lambda>C. C \<subseteq> A \<and> chain C"

(*Proves useful translation lemmas between Isabelle/HOL's sets and predicates*)
lemma chainEq: "chain A \<longleftrightarrow> chain\<^sub>\<subseteq> \<lbrace>A\<rbrace>\<^sup>2"
proof
  assume ordered: "chain A"
  show "chain\<^sub>\<subseteq> \<lbrace>A\<rbrace>\<^sup>2"
  proof (unfold chain_subset_def, intro ballI)
    fix X Y assume xm: "X \<in> \<lbrace>A\<rbrace>\<^sup>2" and ym: "Y \<in> \<lbrace>A\<rbrace>\<^sup>2"
    have ax: "A \<lbrakk>X\<rbrakk>\<^sup>1" using xm unfolding pred2set2_def by simp
    have ay: "A \<lbrakk>Y\<rbrakk>\<^sup>1" using ym unfolding pred2set2_def by simp
    have "\<lbrakk>X\<rbrakk>\<^sup>1 \<subseteq> \<lbrakk>Y\<rbrakk>\<^sup>1 \<or> \<lbrakk>Y\<rbrakk>\<^sup>1 \<subseteq> \<lbrakk>X\<rbrakk>\<^sup>1"
      by (rule ordered[unfolded chain_def, rule_format, OF ax ay])
    then show "Set.subset_eq X Y \<or> Set.subset_eq Y X"
      by (simp add: set2pred1_def subset_iff)
  qed
next
  assume ordered: "chain\<^sub>\<subseteq> \<lbrace>A\<rbrace>\<^sup>2"
  show "chain A"
  proof (unfold chain_def, intro allI impI)
    fix X Y assume ax: "A X" and ay: "A Y"
    have xm: "\<lbrace>X\<rbrace>\<^sup>1 \<in> \<lbrace>A\<rbrace>\<^sup>2"
      using ax unfolding pred2set2_def set2pred1_def pred2set1_def by simp
    have ym: "\<lbrace>Y\<rbrace>\<^sup>1 \<in> \<lbrace>A\<rbrace>\<^sup>2"
      using ay unfolding pred2set2_def set2pred1_def pred2set1_def by simp
    have "Set.subset_eq \<lbrace>X\<rbrace>\<^sup>1 \<lbrace>Y\<rbrace>\<^sup>1 \<or> Set.subset_eq \<lbrace>Y\<rbrace>\<^sup>1 \<lbrace>X\<rbrace>\<^sup>1"
      by (rule ordered[unfolded chain_subset_def, rule_format, OF xm ym])
    then show "X \<subseteq> Y \<or> Y \<subseteq> X"
      by (simp add: pred2set1_def subset_iff)
  qed
qed

lemma chainsEq: "(X::'a set set) \<in> Zorn.chains \<lbrace>A\<rbrace>\<^sup>2 \<longleftrightarrow> chains (A::'a Set Set) \<lbrakk>X\<rbrakk>\<^sup>2" 
proof -
  have sub: "Set.subset_eq X \<lbrace>A\<rbrace>\<^sup>2 \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sup>2 \<subseteq> A"
  proof
    assume h: "Set.subset_eq X \<lbrace>A\<rbrace>\<^sup>2"
    show "\<lbrakk>X\<rbrakk>\<^sup>2 \<subseteq> A"
    proof (intro allI impI)
      fix Y assume y: "\<lbrakk>X\<rbrakk>\<^sup>2 Y"
      have "\<lbrace>Y\<rbrace>\<^sup>1 \<in> \<lbrace>A\<rbrace>\<^sup>2"
        using h y unfolding set2pred2_def by (blast 8)
      then show "A Y" unfolding pred2set2_def set2pred1_def pred2set1_def by simp
    qed
  next
    assume h: "\<lbrakk>X\<rbrakk>\<^sup>2 \<subseteq> A"
    show "Set.subset_eq X \<lbrace>A\<rbrace>\<^sup>2"
    proof
      fix Y assume y: "Y \<in> X"
      have "\<lbrakk>X\<rbrakk>\<^sup>2 \<lbrakk>Y\<rbrakk>\<^sup>1"
        using y unfolding set2pred2_def pred2set1_def set2pred1_def by simp
      then have "A \<lbrakk>Y\<rbrakk>\<^sup>1" using h by (blast 8)
      then show "Y \<in> \<lbrace>A\<rbrace>\<^sup>2" unfolding pred2set2_def by simp
    qed
  qed
  have ordered: "chain \<lbrakk>X\<rbrakk>\<^sup>2 \<longleftrightarrow> chain\<^sub>\<subseteq> X"
    using chainEq[of "\<lbrakk>X\<rbrakk>\<^sup>2"] trans2b[of X] by simp
  show ?thesis using sub ordered unfolding Zorn.chains_def chains_def by simp
qed

lemma ZornLemma: "allChainsHaveUB A \<Longrightarrow> \<exists>M. maximal A M id"
proof -
  fix A::"'a Set Set"
  let ?A = "\<lbrace>A\<rbrace>\<^sup>2"
  assume bounds: "allChainsHaveUB A"
  have library_bounds: "\<forall>C\<in>Zorn.chains ?A. \<exists>U\<in>?A. \<forall>X\<in>C. Set.subset_eq X U"
  proof (intro ballI)
    fix C assume cm: "C \<in> Zorn.chains ?A"
    have c: "chains A \<lbrakk>C\<rbrakk>\<^sup>2" using cm chainsEq by (blast 8)
    have sub: "\<lbrakk>C\<rbrakk>\<^sup>2 \<subseteq> A" and ordered: "chain \<lbrakk>C\<rbrakk>\<^sup>2"
      using c unfolding chains_def by simp_all
    obtain V where av: "A V" and uv: "UB \<lbrakk>C\<rbrakk>\<^sup>2 V"
      using bounds[unfolded allChainsHaveUB_def, THEN spec, THEN mp, THEN mp, OF sub ordered] by (blast 8)
    have vm: "\<lbrace>V\<rbrace>\<^sup>1 \<in> ?A"
      using av unfolding pred2set2_def set2pred1_def pred2set1_def by simp
    have upper: "\<forall>X\<in>C. Set.subset_eq X \<lbrace>V\<rbrace>\<^sup>1"
    proof (intro ballI)
      fix X assume xm: "X \<in> C"
      have cx: "\<lbrakk>C\<rbrakk>\<^sup>2 \<lbrakk>X\<rbrakk>\<^sup>1"
        using xm unfolding set2pred2_def pred2set1_def set2pred1_def by simp
      have "\<lbrakk>X\<rbrakk>\<^sup>1 \<subseteq> V" using uv cx unfolding upper_bound_def by (blast 8)
      then show "Set.subset_eq X \<lbrace>V\<rbrace>\<^sup>1"
        unfolding pred2set1_def set2pred1_def by (blast 8)
    qed
    show "\<exists>U\<in>?A. \<forall>X\<in>C. Set.subset_eq X U" using vm upper by (blast 8)
  qed
  obtain M where mm: "M \<in> ?A" and max: "\<forall>X\<in>?A. Set.subset_eq M X \<longrightarrow> X = M"
    using Zorn.Zorn_Lemma2[OF library_bounds] by (blast 8)
  have am: "A \<lbrakk>M\<rbrakk>\<^sup>1" using mm unfolding pred2set2_def by simp
  have equal: "\<And>X. A X \<and> \<lbrakk>M\<rbrakk>\<^sup>1 \<subseteq> X \<Longrightarrow> X \<approx> \<lbrakk>M\<rbrakk>\<^sup>1"
  proof -
    fix X assume x: "A X \<and> \<lbrakk>M\<rbrakk>\<^sup>1 \<subseteq> X"
    have xm: "\<lbrace>X\<rbrace>\<^sup>1 \<in> ?A"
      using x unfolding pred2set2_def set2pred1_def pred2set1_def by simp
    have sub: "Set.subset_eq M \<lbrace>X\<rbrace>\<^sup>1"
      using x unfolding set2pred1_def pred2set1_def by (blast 8)
    have "\<lbrace>X\<rbrace>\<^sup>1 = M" using max xm sub by (blast 8)
    then show "X \<approx> \<lbrakk>M\<rbrakk>\<^sup>1"
      unfolding pred2set1_def set2pred1_def by (blast 8)
  qed
  have "maximal A \<lbrakk>M\<rbrakk>\<^sup>1 id"
    using am equal unfolding maximal_def id_apply by (blast 8)
  then show "\<exists>M. maximal A M id" by (blast 8)
qed

lemma ZornLemma2: "allChainsHaveUB A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)"
proof -
  fix A::"'a Set Set"
  assume bounds: "allChainsHaveUB A"
  {
    fix X assume *: "A X"
    let ?F= "\<lambda>Y. A Y \<and> X \<subseteq> Y"
    have "allChainsHaveUB ?F"
    proof (unfold allChainsHaveUB_def, intro allI impI)
      fix C assume sub: "C \<subseteq> ?F" and ordered: "chain C"
      show "\<exists>V. ?F V \<and> UB C V"
      proof (cases "\<exists>Y. C Y")
        case False
        then show ?thesis using "*" unfolding upper_bound_def by (blast 8)
      next
        case True
        obtain Y where cy: "C Y" using True by (blast 8)
        have subA: "C \<subseteq> A" using sub by (blast 8)
        obtain V where av: "A V" and uv: "UB C V"
          using bounds[unfolded allChainsHaveUB_def, THEN spec, THEN mp, THEN mp, OF subA ordered] by (blast 8)
        have "X \<subseteq> V" using sub cy uv unfolding upper_bound_def by (blast 8)
        then show ?thesis using av uv by (blast 8)
      qed
    qed
    hence "\<exists>M. maximal ?F M id" by (simp add: ZornLemma)
    then obtain M where max: "maximal ?F M id" by (rule exE)
    hence gtX: "X \<subseteq> M" by (simp add: maximal_def)
    have am: "A M" using max by (simp add: maximal_def)
    have equal: "\<And>Y. A Y \<Longrightarrow> M \<subseteq> Y \<Longrightarrow> Y \<approx> M"
    proof -
      fix Y assume ay: "A Y" and my: "M \<subseteq> Y"
      have fy: "?F Y" using ay gtX my by (blast 8)
      show "Y \<approx> M"
        by (rule max[unfolded maximal_def id_apply, THEN conjunct2, THEN spec, THEN mp, OF conjI[OF fy my]])
    qed
    have "maximal A M id" using am equal unfolding maximal_def id_apply by (blast 8)
    then have "\<exists>M. maximal A M id \<and> X \<subseteq> M" using gtX by (blast 8)
  }
  thus "\<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)" by (blast 8)
qed

lemma ZornLemma_\<omega>: "\<omega>-cpo A \<Longrightarrow> \<exists>M. maximal A M id" by (simp add: ZornLemma omegaCompleteUB)
lemma ZornLemma2_\<omega>: "\<omega>-cpo A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal A M id \<and> X \<subseteq> M)" by (simp add: ZornLemma2 omegaCompleteUB)


(****************************************************************)
(************* Relativized variants *****************************)
(****************************************************************)

(* Inclusion relative to U is a preorder: distinct predicates may agree on U.
   Apply ordinary Zorn to their restrictions to U, where inclusion is a partial
   order. The former bridge1 and bridge2 statements were false and are removed. *)
lemma restricted_chains_have_UB:
  assumes bounds: "allChainsHaveUB\<^sup>U A"
  shows "allChainsHaveUB (\<lambda>Y. \<exists>X. A X \<and> Y = (X \<inter> U))"
proof (unfold allChainsHaveUB_def, intro allI impI)
  fix C
  assume members: "C \<subseteq> (\<lambda>Y. \<exists>X. A X \<and> Y = (X \<inter> U))"
    and ordered: "chain C"
  let ?D = "\<lambda>X. A X \<and> C (X \<inter> U)"
  have sub: "?D \<subseteq> A" by simp
  have ordered_rel: "chain\<^sup>U ?D"
  proof (unfold chain_rel_def, intro allI impI)
    fix X Y assume dx: "?D X" and dy: "?D Y"
    have "(X \<inter> U) \<subseteq> (Y \<inter> U) \<or> (Y \<inter> U) \<subseteq> (X \<inter> U)"
      by (rule ordered[unfolded chain_def, rule_format, OF conjunct2[OF dx] conjunct2[OF dy]])
    then show "X \<subseteq>\<^sup>U Y \<or> Y \<subseteq>\<^sup>U X" by (blast 8)
  qed
  obtain V where av: "A V" and upper: "UB\<^sup>U ?D V"
    using bounds[unfolded allChainsHaveUB_rel_def, THEN spec, THEN mp, OF conjI[OF sub ordered_rel]] by (blast 8)
  have bound: "\<And>Y. C Y \<Longrightarrow> Y \<subseteq> (V \<inter> U)"
  proof -
    fix Y assume cy: "C Y"
    obtain X where ax: "A X" and y: "Y = (X \<inter> U)"
      using members cy by (blast 8)
    have dx: "?D X" using ax cy y by simp
    have "X \<subseteq>\<^sup>U V"
      using upper dx unfolding upper_bound_rel_def by (blast 8)
    then show "Y \<subseteq> (V \<inter> U)" unfolding y by (blast 8)
  qed
  have "UB C (V \<inter> U)" using bound unfolding upper_bound_def by (blast 8)
  then show "\<exists>Y. (\<exists>X. A X \<and> Y = (X \<inter> U)) \<and> UB C Y"
    using av by (blast 8)
qed

lemma ZornLemma_rel: "allChainsHaveUB\<^sup>U A \<Longrightarrow> \<exists>M. maximal\<^sup>U A M id"
proof -
  assume bounds: "allChainsHaveUB\<^sup>U A"
  let ?R = "\<lambda>Y. \<exists>X. A X \<and> Y = (X \<inter> U)"
  have rb: "allChainsHaveUB ?R" by (rule restricted_chains_have_UB[OF bounds])
  obtain N where max: "maximal ?R N id"
    using ZornLemma[OF rb] by (blast 8)
  obtain M where am: "A M" and n: "N = (M \<inter> U)"
    using max unfolding maximal_def by (blast 8)
  have equal: "\<And>Y. A Y \<Longrightarrow> M \<subseteq>\<^sup>U Y \<Longrightarrow> Y \<approx>\<^sup>U M"
  proof -
    fix Y assume ay: "A Y" and my: "M \<subseteq>\<^sup>U Y"
    have ry: "?R (Y \<inter> U)" using ay by (blast 8)
    have sub: "N \<subseteq> (Y \<inter> U)" using my unfolding n by (blast 8)
    have "(Y \<inter> U) \<approx> N"
      by (rule max[unfolded maximal_def id_apply, THEN conjunct2, THEN spec, THEN mp, OF conjI[OF ry sub]])
    then show "Y \<approx>\<^sup>U M" unfolding n by (blast 8)
  qed
  have "maximal\<^sup>U A M id"
    using am equal unfolding maximal_rel_def id_apply by (blast 8)
  then show "\<exists>M. maximal\<^sup>U A M id" by (blast 8)
qed

lemma ZornLemma2_rel: "allChainsHaveUB\<^sup>U A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M)"
proof -
  assume bounds: "allChainsHaveUB\<^sup>U A"
  show "\<forall>X. A X \<longrightarrow> (\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M)"
  proof (intro allI impI)
    fix X assume ax: "A X"
    let ?F = "\<lambda>Y. A Y \<and> X \<subseteq>\<^sup>U Y"
    have "allChainsHaveUB\<^sup>U ?F"
    proof (unfold allChainsHaveUB_rel_def, intro allI impI)
      fix C assume c: "C \<subseteq> ?F \<and> chain\<^sup>U C"
      show "\<exists>V. ?F V \<and> UB\<^sup>U C V"
      proof (cases "\<exists>Y. C Y")
        case False
        then show ?thesis using ax unfolding upper_bound_rel_def by (blast 8)
      next
        case True
        obtain Y where cy: "C Y" using True by (blast 8)
        have cA: "C \<subseteq> A \<and> chain\<^sup>U C" using c by (blast 8)
        obtain V where av: "A V" and uv: "UB\<^sup>U C V"
          using bounds[unfolded allChainsHaveUB_rel_def, THEN spec, THEN mp, OF cA] by (blast 8)
        have "X \<subseteq>\<^sup>U V"
          using c cy uv unfolding upper_bound_rel_def by (blast 8)
        then show ?thesis using av uv by (blast 8)
      qed
    qed
    then obtain M where max: "maximal\<^sup>U ?F M id"
      using ZornLemma_rel by (blast 8)
    have am: "A M" and xm: "X \<subseteq>\<^sup>U M"
      using max unfolding maximal_rel_def by simp_all
    have equal: "\<And>Y. A Y \<Longrightarrow> M \<subseteq>\<^sup>U Y \<Longrightarrow> Y \<approx>\<^sup>U M"
    proof -
      fix Y assume ay: "A Y" and my: "M \<subseteq>\<^sup>U Y"
      have fy: "?F Y" using ay xm my by (blast 8)
      show "Y \<approx>\<^sup>U M"
        by (rule max[unfolded maximal_rel_def id_apply, THEN conjunct2, THEN spec, THEN mp, OF conjI[OF fy my]])
    qed
    have "maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M"
      using am xm equal unfolding maximal_rel_def id_apply by (blast 8)
    then show "\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M" by (blast 8)
  qed
qed

lemma ZornLemma_\<omega>_rel: "\<omega>-cpo\<^sup>U A \<Longrightarrow> \<exists>M. maximal\<^sup>U A M id" by (simp add: ZornLemma_rel omegaCompleteUB_rel)
lemma ZornLemma2_\<omega>_rel: "\<omega>-cpo\<^sup>U A \<Longrightarrow> \<forall>X. A X \<longrightarrow> (\<exists>M. maximal\<^sup>U A M id \<and> X \<subseteq>\<^sup>U M)" by (simp add: ZornLemma2_rel omegaCompleteUB_rel)

end
