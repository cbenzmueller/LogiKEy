(* Luca Pasetto, Roberts Tarvids, Apostolos Tzimoulis and Christoph Benzmüller, 2026 *)
theory HP
  imports Main Helper
begin

text \<open>Shallow embedding of single-world causal models in HOL.\<close>

text \<open>Type declarations\<close>
typedecl \<v>  (* Causal variables *)
typedecl \<iota>  (* Individuals *)

type_synonym \<X> = "\<v> \<Rightarrow> bool"              (* Sets of causal variables *)
type_synonym \<R> = "\<v> \<Rightarrow> (\<iota> \<Rightarrow> bool)" (* Ranges of variables *)
type_synonym \<f> = "(\<v> \<Rightarrow> \<iota>) \<Rightarrow> \<iota>" (* Structural equations *)
type_synonym \<F> = "\<v> \<Rightarrow> \<f>"               (* Families of structural equations *)
type_synonym \<t> = "\<v> \<Rightarrow> \<iota>"             (* Total assignments / contexts *)

(* Keeping only one formula type. The old \<alpha>-layer is redundant in this shallow embedding.
   type_synonym \<alpha> = "\<F> \<Rightarrow> bool" *)
type_synonym \<Phi>   = "\<F> \<Rightarrow> bool"

consts
  U  :: \<X>    (* Exogenous variables *)
  V  :: \<X>    (* Endogenous variables *)
  F  :: \<F>    (* Initial structural family *)
  R  :: \<R>    (* Ranges *)
  tx :: \<t>    (* Actual exogenous context *)

text \<open>
  y directly depends on x if changing x while keeping the rest of an assignment fixed
  can change the value produced by the equation for y.
\<close>
abbreviation (input) directly_depends :: "\<v> \<Rightarrow> \<f> \<Rightarrow> \<X>" where
  "directly_depends y f \<equiv>
     \<lambda>x. \<exists>i1 i2 Z. x \<noteq> y \<and> i1 \<noteq> i2 \<and> R x i1 \<and> R x i2 \<and>
          f (fun_upd Z x i1) \<noteq> f (fun_upd Z x i2)"

definition directly_causes :: "\<F> \<Rightarrow> (\<v> \<Rightarrow> \<v> \<Rightarrow> bool)" where
  "directly_causes G \<equiv> \<lambda>x v. directly_depends v (G v) x"

axiomatization where
  disjoint_variables: "\<forall>x. U x \<longleftrightarrow> \<not> V x" and
  exo: "\<forall>x a. U x \<longrightarrow> F x a = tx x" and
  equations_respect_ranges: "\<forall>v t. R v (F v t)" and
  tx_respects_F: "\<forall>v. F v tx = tx v" and
  depends_only_on_direct_causes:
    "\<forall>v a1 a2. (\<forall>x. directly_depends v (F v) x \<longrightarrow> a1 x = a2 x) \<longrightarrow> F v a1 = F v a2"

lemma tx_respects_ranges:
  "\<forall>v. R v (tx v)"
  by (metis equations_respect_ranges tx_respects_F)

lemma nonempty_ranges:
  "\<forall>v. \<exists>i. R v i"
  using tx_respects_ranges by auto

lemma no_self_dependence:
  "\<forall>v a1 a2. (\<forall>w. w \<noteq> v \<longrightarrow> a1 w = a2 w) \<longrightarrow> F v a1 = F v a2"
  using depends_only_on_direct_causes by blast

lemma exo_no_direct_dep:
  "\<forall>x v. U v \<longrightarrow> \<not> directly_depends v (F v) x"
  by (simp add: exo)

text \<open>Fixed-point view of solutions.\<close>
definition next_ctx :: "\<F> \<Rightarrow> \<t> \<Rightarrow> \<t>" where
  "next_ctx G ctx \<equiv> (\<lambda>v. if U v then tx v else G v ctx)"

definition Fix :: "\<F> \<Rightarrow> \<t> \<Rightarrow> bool" where
  "Fix G ctx \<equiv> next_ctx G ctx = ctx"

lemma Fix_iff_solution:
  "Fix G ctx \<longleftrightarrow>
     (\<forall>u. U u \<longrightarrow> ctx u = tx u) \<and> (\<forall>v. V v \<longrightarrow> ctx v = G v ctx)"
  by (metis (lifting) Fix_def disjoint_variables ext next_ctx_def)

text \<open>A fixed topological order for the initial family F.\<close>
consts ord :: "\<v> list"

axiomatization where
  ord_distinct: "distinct ord" and
  ord_complete: "set ord = {v. V v}" and
  topo_ord: "directly_causes F x v \<Longrightarrow> U x \<or> find_index ord x < find_index ord v"

text \<open>
  We take the list ord as the only structural order notion.
  Recursiveness is expressed directly by ord; no separate auxiliary order relation is introduced.
\<close>

(* endo_not_leaves: intentionally not assumed.
   Recursive models may have endogenous roots, e.g. variables that depend only on exogenous inputs. *)

lemma recur_ord:
  "\<forall>x v. x \<noteq> v \<longrightarrow>
      ((U x \<and> V v) \<or> (V x \<and> V v \<and> find_index ord x < find_index ord v)) \<longrightarrow>
      \<not> ((U v \<and> V x) \<or> (V v \<and> V x \<and> find_index ord v < find_index ord x))"
  by (metis disjoint_variables less_irrefl less_trans)

text \<open>
  Constructive solver: traverse the endogenous variables in the fixed order ord,
  updating the current assignment with the value given by the current equation family.
\<close>
definition step_ctx :: "\<F> \<Rightarrow> \<t> \<Rightarrow> \<v> \<Rightarrow> \<t>" where
  "step_ctx G c v \<equiv> fun_upd c v (G v c)"

definition cv :: "\<F> \<Rightarrow> \<t>" where
  "cv G \<equiv> foldl (step_ctx G) tx ord"

lemma foldl_step_notin:
  assumes "x \<notin> set xs"
  shows "foldl (step_ctx G) c xs x = c x"
  using assms
proof (induction xs arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have xa: "x \<noteq> a" and xxs: "x \<notin> set xs"
    using Cons.prems by auto
  have "foldl (step_ctx G) c (a # xs) x = foldl (step_ctx G) (step_ctx G c a) xs x"
    by simp
  also have "... = step_ctx G c a x"
    using Cons.IH[OF xxs] by simp
  also have "... = c x"
    using xa unfolding step_ctx_def by simp
  finally show ?case .
qed

lemma cv_exo [simp]:
  assumes "U u"
  shows "cv G u = tx u"
  using assms cv_def disjoint_variables foldl_step_notin ord_complete by force

lemma index_at_split [simp]:
  assumes dist: "distinct (prefix @ v # suffix)"
  shows "find_index (prefix @ v # suffix) v = length prefix"
proof -
  have mem: "v \<in> set (prefix @ v # suffix)"
    by simp
  have lt1: "find_index (prefix @ v # suffix) v < length (prefix @ v # suffix)"
    using find_index_lt_length_if_mem[OF mem] .
  have nth1: "(prefix @ v # suffix) ! find_index (prefix @ v # suffix) v = v"
    using find_index_nth_if_mem[OF mem] .
  have lt2: "length prefix < length (prefix @ v # suffix)"
    by simp
  have nth2: "(prefix @ v # suffix) ! length prefix = v"
    by simp
  from dist lt1 lt2 nth1 nth2 show ?thesis
    by (metis distinct_conv_nth)
qed

text \<open>Language\<close>

(* Redundant \<alpha>-layer kept only as a comment.
   definition AtomAlpha :: "\<v> \<Rightarrow> \<iota> \<Rightarrow> \<alpha>" ("_=\<^sup>h\<^sup>p\<^sup>a_") where
     "v =\<^sup>h\<^sup>p\<^sup>a i \<equiv> \<lambda>G. V v \<and> R v i \<and> cv G v = i"
   definition NegationAlpha :: "\<alpha> \<Rightarrow> \<alpha>" ("\<not>\<^sup>h\<^sup>p\<^sup>a") where
     "\<not>\<^sup>h\<^sup>p\<^sup>a \<phi> \<equiv> \<lambda>G. \<not> \<phi> G"
   definition ConjunctionAlpha :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<and>\<^sup>h\<^sup>p\<^sup>a" 95) where
     "\<phi> \<and>\<^sup>h\<^sup>p\<^sup>a \<psi> \<equiv> \<lambda>G. \<phi> G \<and> \<psi> G"
   definition ImplicationAlpha :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<rightarrow>\<^sup>h\<^sup>p\<^sup>a" 95) where
     "\<phi> \<rightarrow>\<^sup>h\<^sup>p\<^sup>a \<psi> \<equiv> \<lambda>G. \<phi> G \<longrightarrow> \<psi> G" *)

definition AtomPhi :: "\<v> \<Rightarrow> \<iota> \<Rightarrow> \<Phi>" ("_=\<^sup>h\<^sup>p\<^sup>p_") where
  "v =\<^sup>h\<^sup>p\<^sup>p i \<equiv> \<lambda>G. V v \<and> R v i \<and> cv G v = i"

definition NegationPhi :: "\<Phi> \<Rightarrow> \<Phi>" ("\<not>\<^sup>h\<^sup>p\<^sup>p") where
  "\<not>\<^sup>h\<^sup>p\<^sup>p \<phi> \<equiv> \<lambda>G. \<not> \<phi> G"

definition ConjunctionPhi :: "\<Phi> \<Rightarrow> \<Phi> \<Rightarrow> \<Phi>" (infixr "\<and>\<^sup>h\<^sup>p\<^sup>p" 95) where
  "\<phi> \<and>\<^sup>h\<^sup>p\<^sup>p \<psi> \<equiv> \<lambda>G. \<phi> G \<and> \<psi> G"

definition ImplicationPhi :: "\<Phi> \<Rightarrow> \<Phi> \<Rightarrow> \<Phi>" (infixr "\<rightarrow>\<^sup>h\<^sup>p\<^sup>p" 95) where
  "\<phi> \<rightarrow>\<^sup>h\<^sup>p\<^sup>p \<psi> \<equiv> \<lambda>G. \<phi> G \<longrightarrow> \<psi> G"

text \<open>Pointwise well-formedness for a single intervention target/value pair.\<close>
definition wf_intervention :: "\<v> \<Rightarrow> \<iota> \<Rightarrow> bool" where
  "wf_intervention v i \<equiv> V v \<and> R v i"

lemma wf_intervention_iff [simp]:
  "wf_intervention v i \<longleftrightarrow> V v \<and> R v i"
  unfolding wf_intervention_def by simp

text \<open>
  Intervention replaces selected structural equations by constants.
  The well-formedness check is internalized pointwise in update_F.
\<close>
definition update_F :: "\<F> \<Rightarrow> \<X> \<Rightarrow> (\<v> \<Rightarrow> \<iota>) \<Rightarrow> \<F>" where
  "update_F G Y b \<equiv> \<lambda>v a. if Y v \<and> wf_intervention v (b v) then b v else G v a"

definition Intervention :: "\<X> \<Rightarrow> (\<v> \<Rightarrow> \<iota>) \<Rightarrow> \<Phi> \<Rightarrow> \<Phi>" ("[_\<leftarrow>_]_") where
  "[Y \<leftarrow> b] \<phi> \<equiv> \<lambda>G. \<phi> (update_F G Y b)"

inductive reachable :: "\<F> \<Rightarrow> bool" where
  reachable_base [intro]: "reachable F" |
  reachable_step [intro]: "reachable G \<Longrightarrow> reachable (update_F G Y b)"

lemma directly_causes_update_subset [simp]:
  assumes "directly_causes (update_F G Y b) x v"
  shows "directly_causes G x v"
  using assms unfolding directly_causes_def update_F_def by metis

definition Truth :: "\<F> \<Rightarrow> \<Phi> \<Rightarrow> bool" ("\<langle>_\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p _") where
  "\<langle>G\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p \<phi> \<equiv> \<phi> G"

definition Validity ("\<Turnstile>\<^sup>h\<^sup>p\<^sup>p _") where
  "\<Turnstile>\<^sup>h\<^sup>p\<^sup>p \<phi> \<equiv> \<forall>G. reachable G \<longrightarrow> \<langle>G\<rangle> \<Turnstile>\<^sup>h\<^sup>p\<^sup>p \<phi>"

lemma reachable_update_F [intro]:
  "reachable (update_F F Y b)"
  by (rule reachable_step[OF reachable_base])

lemma reachable_directly_causes_subset_F [simp]:
  assumes rG: "reachable G" and dc: "directly_causes G x v"
  shows "directly_causes F x v"
  using assms by (induction) auto

lemma reachable_respects_ranges [simp]:
  assumes "reachable G"
  shows "\<forall>v t. R v (G v t)"
  using assms
  by (induction) (auto simp: equations_respect_ranges update_F_def)

lemma reachable_exo [simp]:
  assumes "reachable G"
  shows "\<forall>x a. U x \<longrightarrow> G x a = tx x"
  using assms
  by (induction) (auto simp: exo update_F_def disjoint_variables)

lemma reachable_locality [simp]:
  assumes "reachable G"
  shows "\<forall>v a1 a2. (\<forall>x. directly_depends v (G v) x \<longrightarrow> a1 x = a2 x) \<longrightarrow> G v a1 = G v a2"
  using assms 
  apply induction
  using depends_only_on_direct_causes apply blast
  by (smt (verit, del_insts) update_F_def)

lemma reachable_topo_index [simp]:
  assumes rG: "reachable G" and dc: "directly_causes G x v"
  shows "U x \<or> find_index ord x < find_index ord v"
  by (metis dc rG reachable_directly_causes_subset_F topo_ord)

lemma cv_reachable_endo [simp]:
  assumes rG: "reachable G" and Vv: "V v"
  shows "cv G v = G v (cv G)"
proof -
  from ord_complete Vv have vmem: "v \<in> set ord"
    by auto
  then obtain prefix suffix where dec: "ord = prefix @ v # suffix"
    using split_list 
    by metis
  let ?cpre = "foldl (step_ctx G) tx prefix"
  have dist: "distinct (prefix @ v # suffix)"
    using ord_distinct dec by simp
  have vnot: "v \<notin> set suffix"
    using dist by auto
  have cvv: "cv G v = G v ?cpre" 
  proof -
    have "cv G v = foldl (step_ctx G) (step_ctx G ?cpre v) suffix v"
      unfolding cv_def dec by simp
    also have "... = step_ctx G ?cpre v v"
      by (simp add: foldl_step_notin vnot)
    also have "... = G v ?cpre"
      unfolding step_ctx_def by simp
    finally show ?thesis .
  qed
  have agree: "\<forall>x. directly_depends v (G v) x \<longrightarrow> ?cpre x = cv G x"
  proof (intro allI impI)
    fix x
    assume dx: "directly_depends v (G v) x"
    have topo: "U x \<or> find_index ord x < find_index ord v"
      using reachable_topo_index[OF rG] dx
      unfolding directly_causes_def by blast
    show "?cpre x = cv G x"
    proof (cases "U x")
      case True
      have xnotpref: "x \<notin> set prefix"
        using True ord_complete disjoint_variables dec 
        by (metis append_eq_conv_conj in_set_takeD mem_Collect_eq)
      have cprex: "?cpre x = tx x"
        by (simp add: foldl_step_notin xnotpref)
      have cvx: "cv G x = tx x"
        using cv_exo[of x G] True by simp
      show ?thesis
        using cprex cvx by simp
    next
      case False
      then have Vx: "V x"
        using disjoint_variables by blast
      have xmem: "x \<in> set ord"
        using ord_complete Vx by auto
      have idx: "find_index ord x < find_index ord v"
        using topo False by simp
      have idxv: "find_index ord v = length prefix"
        unfolding dec by (rule index_at_split[OF dist])
      have idx_lt_pref: "find_index ord x < length prefix"
        using idx idxv by simp
      have xpref: "x \<in> set prefix"
      proof -
        have nthx: "ord ! find_index ord x = x"
          using find_index_nth_if_mem[OF xmem] .
        have "prefix ! find_index ord x = x"
          using nthx idx_lt_pref unfolding dec 
          by (simp add: nth_append_left)
        then show ?thesis
          using idx_lt_pref nth_mem
          by metis
      qed
      have xnot: "x \<notin> set (v # suffix)"
        using xpref dist by auto
      have cvx: "cv G x = ?cpre x"
      proof -
        have "cv G x = foldl (step_ctx G) (step_ctx G ?cpre v) suffix x"
          unfolding cv_def dec by simp
        also have "... = step_ctx G ?cpre v x"
  using foldl_step_notin xnot by auto
        also have "... = ?cpre x"
          using xnot unfolding step_ctx_def by simp
        finally show ?thesis .
      qed
      then show ?thesis
        by simp
    qed
  qed
  have loc: "G v ?cpre = G v (cv G)"
    using reachable_locality[OF rG] agree by blast
  show ?thesis
    using cvv loc by simp
qed

lemma cv_reachable_fix [simp]:
  assumes rG: "reachable G"
  shows "Fix G (cv G)"
  using Fix_iff_solution cv_exo cv_reachable_endo rG by blast

lemma fix_agree_endo [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2" and Vv: "V v"
  shows "c1 v = c2 v"
  using Vv
proof (induction v rule: measure_induct_rule[of "\<lambda>v. find_index ord v"])
  case (less v) 
  then have Vv: "V v" by simp
  have c1v: "c1 v = G v c1"
    using fix1 Vv unfolding Fix_iff_solution by blast
  have c2v: "c2 v = G v c2"
    using fix2 Vv unfolding Fix_iff_solution by blast
  have agree: "\<forall>x. directly_depends v (G v) x \<longrightarrow> c1 x = c2 x"
  proof (intro allI impI)
    fix x
    assume dx: "directly_depends v (G v) x"
    have topo: "U x \<or> find_index ord x < find_index ord v"
      using reachable_topo_index[OF rG] dx
      unfolding directly_causes_def by blast
    show "c1 x = c2 x"
    proof (cases "U x")
      case True
      then have "c1 x = tx x"
        using fix1 unfolding Fix_iff_solution by blast
      moreover have "c2 x = tx x"
        using fix2 True unfolding Fix_iff_solution by blast
      ultimately show ?thesis by simp
    next
      case False
      then have Vx: "V x"
        using disjoint_variables by blast
      have "find_index ord x < find_index ord v"
        using topo False by simp
      then show ?thesis
        using less.IH[of x] Vx by simp
    qed
  qed
  have "G v c1 = G v c2"
    using reachable_locality[OF rG] agree by blast
  with c1v c2v show ?case by simp
qed

lemma fix_unique [simp]:
  assumes rG: "reachable G" and fix1: "Fix G c1" and fix2: "Fix G c2"
  shows "c1 = c2"
  using assms unfolding Fix_iff_solution
  by (metis (no_types, lifting) ext disjoint_variables fix1 fix2 fix_agree_endo)

lemma reachable_unique_solution [simp]:
  assumes rG: "reachable G"
  shows "\<exists>!ctx. Fix G ctx"
  by (metis cv_reachable_fix fix_unique rG)

lemma cv_eq_if_fix [simp]:
  assumes rG: "reachable G" and fixc: "Fix G c"
  shows "cv G = c"
  using fixc rG by fastforce

lemma cv_intervention_hit [simp]:
  assumes rG: "reachable G" and Yv: "Y v" and Vv: "V v" and Rv: "R v (b v)"
  shows "cv (update_F G Y b) v = b v" 
  by (metis Rv Vv Yv cv_reachable_endo rG reachable_step update_F_def wf_intervention_iff)

lemma cv_update_range [simp]:
  assumes Vv: "V v"
  shows "R v (cv (update_F F Y b) v)"
  by (metis assms cv_reachable_endo reachable_respects_ranges reachable.simps)

lemma fix_strengthen_intervention [simp]:
  assumes base: "Fix (update_F F Y b) c"
      and V1: "V v1" and R1: "R v1 i1" and c1: "c v1 = i1"
  shows "Fix (update_F F (fun_upd Y v1 True) (fun_upd b v1 i1)) c"
  using Fix_iff_solution base c1 update_F_def by fastforce

lemma directly_depends_const [simp]:
  "\<not> directly_depends v (\<lambda>_. (c :: \<iota>)) x"
  by simp

end
