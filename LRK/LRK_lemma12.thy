\<comment> \<open>Proving proposition 12\<close>

theory LRK_lemma12
  imports LRK 
begin

consts
  w::i 
  v::i
  p::\<sigma>

abbreviation (input) check_subset::"(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>bool" where
  "check_subset S T \<equiv> (\<forall>x. S x \<longrightarrow> T x)"

abbreviation (input) same_set::"(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>bool" where
  "same_set S T \<equiv> check_subset S T  \<and> check_subset T S" 

abbreviation (input) in_list_pred :: "i list \<Rightarrow> i\<Rightarrow>bool" where
  "in_list_pred xs x \<equiv> x \<in> set xs" 

axiomatization where
\<comment> \<open>Restrict the universe to two worlds v and w\<close>
  a0: "\<forall>i. i=w \<or> i=v" and 
  a1:"\<lfloor>\<^sup>Ap\<rfloor>\<^sub>w" and a2:"\<not>\<lfloor>\<^sup>Ap\<rfloor>\<^sub>v" and

  a3: "w \<^bold>\<sim> v" and

  a4: "w \<^bold>\<approx> w" and a5: "\<not>(w \<^bold>\<approx> v)" and 
  a6: "v \<^bold>\<approx> v" and a7: "\<not>(v \<^bold>\<approx> w)" and 

  Nw: "\<exists>H1 H2. (((N w) H1) \<and> (N w) H2) \<and> (H1 \<noteq> H2) \<and> (same_set H1 (in_list_pred[w])) \<and> 
    (same_set H2 (in_list_pred[w, v]))" and
  Nv: "\<exists>H1. ((N v) H1) \<and> (same_set H1 (in_list_pred[v]))"

lemma a: "\<lfloor>(\<^sup>Ap)\<rfloor>\<^sub>w" by (simp add: a1)
lemma b: "\<not>\<lfloor>(\<^sup>Ap)\<rfloor>\<^sub>v" by (simp add: a2)

lemma c: "\<lfloor>((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> (Os (\<^sup>Ap))))\<rfloor>\<^sub>w" 
  apply auto
  using a apply simp 
  using Nw a2 a3 Nax apply simp 
  by (metis til_ref)

lemma d: "\<not>\<lfloor>((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> (Os (\<^sup>Ap))))\<rfloor>\<^sub>v" 
  apply auto
  using b by simp

lemma e: "\<lfloor>(Rr ((\<^sup>Ap) \<^bold>\<and> \<^bold>\<not> (Os \<^sup>Ap)))\<rfloor>\<^sub>w" 
  apply simp 
  using c d a4
  apply simp 
  by (metis (full_types) a0 a2 a5 a7)

lemma f:"\<lfloor>[((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> Os \<^sup>Ap))?](Os \<^sup>Ap)\<rfloor>\<^sub>w"
  apply simp
  using Nax c by blast

lemma g: "\<not>\<lfloor>[((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> Os \<^sup>Ap))?]((\<^sup>Ap) \<^bold>\<and> \<^bold>\<not> Os \<^sup>Ap)\<rfloor>\<^sub>w" 
  using f by fastforce

\<comment> \<open>We can now prove the full lemma\<close>
lemma twelve_final: "\<not>\<lfloor>(Rr ((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> Os \<^sup>Ap))) \<^bold>\<rightarrow> (((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> Os \<^sup>Ap)) \<^bold>\<rightarrow>
  [((\<^sup>Ap) \<^bold>\<and> (\<^bold>\<not> Os \<^sup>Ap))?]((\<^sup>Ap) \<^bold>\<and> \<^bold>\<not> Os \<^sup>Ap))\<rfloor>\<^sub>w"
  apply simp
  using c e 
  apply simp
  by (metis f)
  
end