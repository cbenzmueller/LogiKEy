theory "regression-checks"
  imports adequacy "ext-relationships" "lab-relationships"
    "simplified/correspondence-simpl" "simplified/ext-simpl-relationships"
    "simplified/lab-simpl-relationships" "simplified/model-generation"
begin

(* Regression against reintroducing the false relative/global Zorn bridge. *)
definition audit_prefixes :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "audit_prefixes X \<longleftrightarrow> (\<exists>n. X = (\<lambda>k. k < n))"

lemma audit_prefix_member: "audit_prefixes (\<lambda>k. k < n)"
  unfolding audit_prefixes_def by blast

lemma audit_prefix_chain: "chain audit_prefixes"
  unfolding chain_def
  using audit_prefixes_def by force

lemma audit_empty_relative_ub:
  "allChainsHaveUB_rel (\<lambda>(_::nat). False) audit_prefixes"
  using audit_prefix_member[of 0]
  unfolding allChainsHaveUB_rel_def upper_bound_rel_def by blast

lemma audit_no_global_ub: "\<not> allChainsHaveUB audit_prefixes"
proof
  assume h: "allChainsHaveUB audit_prefixes"
  have "\<exists>X. audit_prefixes X \<and> upper_bound audit_prefixes X"
    using h audit_prefix_chain unfolding allChainsHaveUB_def by blast
  then obtain X where member: "audit_prefixes X" and bound: "upper_bound audit_prefixes X"
    by blast
  obtain n where X: "X = (\<lambda>k. k < n)"
    using member unfolding audit_prefixes_def by blast
  have ubn: "\<forall>k. k < Suc n \<longrightarrow> X k"
    using bound audit_prefix_member[of "Suc n"] unfolding upper_bound_def by blast
  have "X n" by (rule ubn[rule_format]) simp
  then show False unfolding X by simp
qed

lemma audit_bridge2_counterexample:
  "allChainsHaveUB_rel (\<lambda>(_::nat). False) audit_prefixes \<and> \<not> allChainsHaveUB audit_prefixes"
  using audit_empty_relative_ub audit_no_global_ub by blast

(* Regression against the other false bridge (bridge1): over marked prefixes,
the global Zorn hypothesis holds and a global maximal element exists, while no
element is maximal relative to the universe of unmarked positions. This
mechanizes the countermodel described in the audit notes. *)
abbreviation audit_S :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool" where
  "audit_S n \<equiv> (\<lambda>(k,b). (\<not> b \<and> k < n) \<or> (b \<and> k = n))"

abbreviation audit_unmarked :: "nat \<times> bool \<Rightarrow> bool" where
  "audit_unmarked \<equiv> (\<lambda>(k,b). \<not> b)"

definition audit_marked :: "(nat \<times> bool \<Rightarrow> bool) \<Rightarrow> bool" where
  "audit_marked X \<longleftrightarrow> (\<exists>n. X = audit_S n)"

lemma audit_S_member: "audit_marked (audit_S n)"
  unfolding audit_marked_def by blast

lemma audit_S_incomparable:
  assumes sub: "audit_S n \<subseteq> audit_S m" shows "n = m"
proof -
  have "audit_S n (n, True)" by simp
  then have "audit_S m (n, True)" using sub by blast
  then show ?thesis by simp
qed

lemma audit_marked_antichain:
  assumes C: "C \<subseteq> audit_marked" and ch: "chain C" and x: "C X" and y: "C Y"
  shows "X = Y"
proof -
  obtain n where xn: "X = audit_S n" using C x unfolding audit_marked_def by blast
  obtain m where ym: "Y = audit_S m" using C y unfolding audit_marked_def by blast
  have "X \<subseteq> Y \<or> Y \<subseteq> X" using ch x y unfolding chain_def by blast
  then show ?thesis
  proof
    assume "X \<subseteq> Y"
    then have "audit_S n \<subseteq> audit_S m" using xn ym by simp
    then have "n = m" by (rule audit_S_incomparable)
    then show "X = Y" by (simp add: xn ym)
  next
    assume "Y \<subseteq> X"
    then have "audit_S m \<subseteq> audit_S n" using xn ym by simp
    then have "m = n" by (rule audit_S_incomparable)
    then show "X = Y" by (simp add: xn ym)
  qed
qed

lemma audit_marked_allUB: "allChainsHaveUB audit_marked"
proof (unfold allChainsHaveUB_def, intro allI impI)
  fix C assume sub: "C \<subseteq> audit_marked" and ch: "chain C"
  show "\<exists>X. audit_marked X \<and> UB C X"
  proof (cases "\<exists>Z. C Z")
    case False
    then show ?thesis
      unfolding upper_bound_def using audit_S_member[of 0] by blast
  next
    case True
    then obtain Z where z: "C Z" by blast
    have eq: "\<And>X. C X \<Longrightarrow> X = Z"
      using audit_marked_antichain[OF sub ch] z by blast
    have "UB C Z" unfolding upper_bound_def using eq by blast
    then show ?thesis using sub z by blast
  qed
qed

lemma audit_global_maximal: "maximal audit_marked (audit_S 0) id"
proof -
  have eqz: "\<And>X. audit_marked X \<Longrightarrow> audit_S 0 \<subseteq> X \<Longrightarrow> X \<approx> audit_S 0"
  proof -
    fix X assume mk: "audit_marked X" and sub: "audit_S 0 \<subseteq> X"
    obtain n where xn: "X = audit_S n" using mk unfolding audit_marked_def by blast
    have "audit_S 0 \<subseteq> audit_S n" using sub xn by simp
    then have "0 = n" by (rule audit_S_incomparable)
    then show "X \<approx> audit_S 0" by (simp add: xn)
  qed
  have "\<forall>X. audit_marked X \<and> audit_S 0 \<subseteq> X \<longrightarrow> X \<approx> audit_S 0"
  proof (intro allI, intro impI)
    fix X assume "audit_marked X \<and> audit_S 0 \<subseteq> X"
    then show "X \<approx> audit_S 0" using eqz[of X] by blast
  qed
  then show ?thesis
    using audit_S_member[of 0] unfolding maximal_def id_def by blast
qed

lemma audit_no_relative_maximal:
  "\<not> (\<exists>N. maximal_rel audit_unmarked audit_marked N id)"
proof
  assume "\<exists>N. maximal_rel audit_unmarked audit_marked N id"
  then obtain N where m: "maximal_rel audit_unmarked audit_marked N id" by blast
  obtain n where nN: "N = audit_S n"
    using m unfolding maximal_rel_def audit_marked_def by blast
  have s1: "audit_S n \<subseteq>\<^sup>audit_unmarked audit_S (Suc n)"
    by auto
  have s2: "\<not> (audit_S (Suc n) \<approx>\<^sup>audit_unmarked audit_S n)"
  proof
    assume eqv: "audit_S (Suc n) \<approx>\<^sup>audit_unmarked audit_S n"
    have g: "audit_unmarked (n, False)" by simp
    from eqv g have "audit_S (Suc n) (n, False) \<longleftrightarrow> audit_S n (n, False)" by blast
    then show False by simp
  qed
  show False
    using m nN s1 s2 audit_S_member[of "Suc n"]
    unfolding maximal_rel_def id_def by blast
qed

lemma audit_bridge1_counterexample:
  "allChainsHaveUB audit_marked \<and> (\<exists>M. maximal audit_marked M id) \<and>
    \<not> (\<exists>N. maximal_rel audit_unmarked audit_marked N id)"
  using audit_marked_allUB audit_global_maximal audit_no_relative_maximal by blast

(* These tests use the repaired source definitions, not restatements. *)
lemma self_attack_complete:
  "labellings.completeLab (\<lambda>_. True) (\<lambda>(_::unit) _. True) L
    \<longleftrightarrow> L () = Undec"
  unfolding labellings.completeLab_def labellings.admissibleLab_def
    labellings.legallyIn_def labellings.legallyOut_def labellings.legallyUndec_def
    inset_def outset_def undecset_def
  by (cases "L ()") auto

lemma self_attack_not_accepted:
  "\<not> sJ (labellings.completeLab (\<lambda>_. True)) (\<lambda>(_::unit) _. True) () \<and>
   \<not> cJ (labellings.completeLab (\<lambda>_. True)) (\<lambda>(_::unit) _. True) ()"
  unfolding skepticallyJustified_def credulouslyJustified_def
  using self_attack_complete[of "\<lambda>_. Undec"] self_attack_complete by auto

lemma unattacked_argument_accepted:
  "sJ (labellings.completeLab (\<lambda>_. True)) (\<lambda>(_::unit) _. False) ()"
  unfolding skepticallyJustified_def labellings.completeLab_def
    labellings.admissibleLab_def labellings.legallyIn_def labellings.legallyOut_def
    labellings.legallyUndec_def inset_def outset_def undecset_def
  by (metis Label.exhaust)

(* Audit project-added named fact collections and their full proof ancestry.
   Isabelle2025's Quickcheck generator itself admits executable support
   equations (HOL/Tools/Quickcheck/quickcheck_common.ML, define_functions).
   Main already contains 30 such facts; our four datatypes add the eight
   exactly named collections below. These generated test-code equations are
   excluded only as audit roots. If any checked mathematical result depends
   on them, its ancestry still contains skip_proof and the audit fails. *)
ML \<open>
val _ =
  let
    val thy = @{theory};
    val generated_quickcheck_support =
      ["base.Label.full_exhaustive_Label.simps",
       "base.Label.narrowing_Label.simps",
       "model-generation.ExFig4.Arg.full_exhaustive_Arg.simps",
       "model-generation.ExFig4.Arg.narrowing_Arg.simps",
       "model-generation.ExFig5.Arg.full_exhaustive_Arg.simps",
       "model-generation.ExFig5.Arg.narrowing_Arg.simps",
       "model-generation.ExFig6.Arg.full_exhaustive_Arg.simps",
       "model-generation.ExFig6.Arg.narrowing_Arg.simps"];
    val project_facts =
      Facts.dest_static true [Global_Theory.facts_of @{theory Main}]
        (Global_Theory.facts_of thy)
      |> map (apsnd (map (Thm.transfer thy)));
    val (support, audited) = List.partition
      (fn (name, _) => member (op =) generated_quickcheck_support name) project_facts;
    val oracles = Thm_Deps.all_oracles (maps snd audited);
    fun isolate test entries =
      if null entries orelse not (test entries) then []
      else (case entries of [entry] => [entry] | _ =>
        let val (left, right) = chop (length entries div 2) entries
        in isolate test left @ isolate test right end);
  in
    writeln ("AA proof audit: excluded " ^ string_of_int (length support) ^
      " generated Quickcheck support collections: " ^ commas (map fst support));
    if null oracles then
      writeln ("AA proof audit: checked " ^ string_of_int (length audited) ^
        " project fact collections; no oracle dependencies")
    else
      let
        val affected = isolate
          (fn facts => not (null (Thm_Deps.all_oracles (maps snd facts)))) audited;
      in
        error ("AA proof audit found oracle dependencies: " ^
          commas (map (fn ((name, _), _) => name) oracles) ^
          "; affected project facts: " ^ commas (map fst affected))
      end
  end;
\<close>

end


