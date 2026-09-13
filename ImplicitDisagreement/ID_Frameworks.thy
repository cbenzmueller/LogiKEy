theory ID_Frameworks
  imports "AA_Fixed.ext-properties"
begin

section \<open>Frameworks, agents, and coalitions\<close>

text \<open>The framework and extension-semantics definitions are given by the import:
a framework is passed as an argument predicate U and an attack relation att. The development reuses
\<^verbatim>\<open>defends_rel\<close>, \<^verbatim>\<open>completeExt\<close>, \<^verbatim>\<open>groundedExt\<close> and
\<^verbatim>\<open>preferredExt\<close>, including conflict-freeness in complete semantics.
Conclusions below have an arbitrary HOL type; no object-language consequence relation
is imposed.\<close>

definition induced_att :: "'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Rel" where
  "induced_att att A = (\<lambda>a b. A a \<and> A b \<and> att a b)"

text \<open>Agents (paper's Agents definition): an agent is an induced subframework of
the ambient graph.\<close>
definition is_agent :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Rel \<Rightarrow> bool" where
  "is_agent U att A r \<longleftrightarrow> A \<subseteq> U \<and> r = induced_att att A"

text \<open>Coalition (paper's Coalition definition) reuses predicate union. Coalition
attacks include all ambient edges between coalition members, including edges absent
from both agents' graphs.\<close>
abbreviation coalition :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" where
  "coalition A B \<equiv> A \<union> B"

abbreviation coalition_att :: "'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Rel" where
  "coalition_att att A B \<equiv> induced_att att (coalition A B)"

text \<open>Argument deletion, as specified just before the weak-spot definition.\<close>
abbreviation remove_argument :: "'a Set \<Rightarrow> 'a \<Rightarrow> 'a Set" where
  "remove_argument U a \<equiv> U \<inter> (\<lambda>x. x \<noteq> a)"

abbreviation remove_att :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a \<Rightarrow> 'a Rel" where
  "remove_att U att a \<equiv> induced_att att (remove_argument U a)"

lemma is_agent_iff:
  "is_agent U att A r \<longleftrightarrow>
    A \<subseteq> U \<and> (\<forall>a b. r a b \<longleftrightarrow> att a b \<and> A a \<and> A b)"
  unfolding is_agent_def induced_att_def by (auto simp: fun_eq_iff)

lemma coalition_is_agent:
  "is_agent U att A r \<Longrightarrow> is_agent U att B s \<Longrightarrow>
    is_agent U att (coalition A B) (coalition_att att A B)"
  unfolding is_agent_def by auto

lemma coalition_commutes: "coalition A B = coalition B A"
  by (auto simp: fun_eq_iff)

lemma coalition_associates: "coalition (coalition A B) C = coalition A (coalition B C)"
  by (auto simp: fun_eq_iff)

lemma deletion_removes_incident_edges:
  "\<not> remove_att U att a a b \<and> \<not> remove_att U att a b a"
  unfolding induced_att_def by simp

lemma deletion_is_agent:
  "is_agent U att (remove_argument U a) (remove_att U att a)"
  unfolding is_agent_def by auto

text \<open>The imported semantics already restrict attack quantifiers to U. These
lemmas justify evaluating an agent either with its induced attack relation or with
the ambient attack relation and its own argument predicate.\<close>
lemma defends_induced [simp]:
  "U a \<Longrightarrow> defends_rel U (induced_att att U) E a = defends_rel U att E a"
  unfolding defends_rel_def induced_att_def by auto

lemma conflictfree_induced [simp]:
  "extensions.conflictfreeExt U (induced_att att U) E = extensions.conflictfreeExt U att E"
  unfolding extensions.conflictfreeExt_def induced_att_def by auto

lemma admissible_induced [simp]:
  "extensions.admissibleExt U (induced_att att U) E = extensions.admissibleExt U att E"
  unfolding extensions.admissibleExt_def by simp

lemma complete_induced [simp]:
  "extensions.completeExt U (induced_att att U) E = extensions.completeExt U att E"
  unfolding extensions.completeExt_def by simp

lemma preferred_induced [simp]:
  "extensions.preferredExt U (induced_att att U) E = extensions.preferredExt U att E"
  unfolding extensions.preferredExt_def maximal_rel_def by simp

lemma preferred_extensions_exist: "\<exists>E. extensions.preferredExt U att E"
  using preferredExist maxAdmissibleComplete
  unfolding extensions.preferredExt_def by blast

text \<open>Deletion versus a fresh unattacked attacker (Sakama's counterfactual
construction): adding an unattacked attacker t of a forces t into and a out of
every complete extension, and otherwise the extended framework behaves exactly
like the framework with a deleted. This substantiates the paper's footnote in
Section 3.\<close>

definition fresh_attacker_att :: "'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Rel" where
  "fresh_attacker_att att U a t = (\<lambda>x y. induced_att att U x y \<or> (x = t \<and> y = a))"

lemma complete_restrict_cong:
  assumes ag: "\<forall>x. VV x \<longrightarrow> (F x \<longleftrightarrow> G x)"
  shows "extensions.completeExt VV att F \<longleftrightarrow> extensions.completeExt VV att G"
proof -
  have d: "\<And>x. defends_rel VV att F x \<longleftrightarrow> defends_rel VV att G x"
    unfolding defends_rel_def using ag by blast
  show ?thesis
    unfolding extensions.completeExt_def extensions.admissibleExt_def
      extensions.conflictfreeExt_def
    using ag d by blast
qed

lemma fresh_attacker_defends:
  assumes t: "\<not> U t" and a: "U a" and Et: "E t" and nEa: "\<not> E a"
      and x: "U x" and xa: "x \<noteq> a"
  shows "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x \<longleftrightarrow>
         defends_rel (remove_argument U a) att E x"
proof
  assume L: "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
  show "defends_rel (remove_argument U a) att E x"
    unfolding defends_rel_def
  proof (intro allI impI)
    fix b assume b: "remove_argument U a b" and batk: "att b x"
    have bU: "(U \<union> \<lbrace>t\<rbrace>) b" using b by auto
    have batk2: "fresh_attacker_att att U a t b x"
      using b batk x unfolding fresh_attacker_att_def induced_att_def by auto
    obtain z where z1: "(U \<union> \<lbrace>t\<rbrace>) z" and z2: "E z"
      and z3: "fresh_attacker_att att U a t z b"
      using L bU batk2 unfolding defends_rel_def by blast
    have "b \<noteq> a" using b by auto
    then have zU: "U z" and zatk: "att z b"
      using z3 unfolding fresh_attacker_att_def induced_att_def by auto
    have "z \<noteq> a" using z2 nEa by auto
    then show "\<exists>z. remove_argument U a z \<and> E z \<and> att z b"
      using zU z2 zatk by auto
  qed
next
  assume R: "defends_rel (remove_argument U a) att E x"
  show "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
    unfolding defends_rel_def
  proof (intro allI impI)
    fix b assume bU: "(U \<union> \<lbrace>t\<rbrace>) b" and batk: "fresh_attacker_att att U a t b x"
    have ind: "induced_att att U b x"
      using batk xa unfolding fresh_attacker_att_def by auto
    have Ub: "U b" and attbx: "att b x"
      using ind unfolding induced_att_def by auto
    show "\<exists>z. (U \<union> \<lbrace>t\<rbrace>) z \<and> E z \<and> fresh_attacker_att att U a t z b"
    proof (cases "b = a")
      case True
      then have "fresh_attacker_att att U a t t b"
        unfolding fresh_attacker_att_def by auto
      then show ?thesis using Et by auto
    next
      case False
      then have "remove_argument U a b" using Ub by auto
      then obtain z where "remove_argument U a z" and "E z" and "att z b"
        using R attbx unfolding defends_rel_def by blast
      then show ?thesis
        using Ub unfolding fresh_attacker_att_def induced_att_def by auto
    qed
  qed
qed

lemma fresh_attacker_complete:
  assumes t: "\<not> U t" and a: "U a"
  shows "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E \<longleftrightarrow>
         E t \<and> \<not> E a \<and> extensions.completeExt (remove_argument U a) att E"
proof
  assume L: "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
  have ta: "t \<noteq> a" using t a by auto
  have dt: "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E t"
    unfolding defends_rel_def fresh_attacker_att_def induced_att_def
    using t ta by auto
  have Et: "E t"
    using L dt unfolding extensions.completeExt_def by blast
  have nEa: "\<not> E a"
    using L Et a unfolding extensions.completeExt_def extensions.admissibleExt_def
      extensions.conflictfreeExt_def fresh_attacker_att_def by blast
  have cf: "extensions.conflictfreeExt (remove_argument U a) att E"
    using L unfolding extensions.completeExt_def extensions.admissibleExt_def
      extensions.conflictfreeExt_def fresh_attacker_att_def induced_att_def by auto
  have sd: "\<forall>x. remove_argument U a x \<longrightarrow> E x \<longrightarrow>
              defends_rel (remove_argument U a) att E x"
  proof (intro allI impI)
    fix x assume xr: "remove_argument U a x" and Ex: "E x"
    have Ux: "U x" and xa2: "x \<noteq> a" using xr by auto
    have dx: "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
      using L Ex Ux unfolding extensions.completeExt_def extensions.admissibleExt_def by blast
    show "defends_rel (remove_argument U a) att E x"
      using fresh_attacker_defends[where att=att and U=U and a=a and t=t and E=E]
        t a Et nEa Ux xa2 dx by blast
  qed
  have cd: "\<forall>x. remove_argument U a x \<longrightarrow>
              defends_rel (remove_argument U a) att E x \<longrightarrow> E x"
  proof (intro allI impI)
    fix x assume xr: "remove_argument U a x"
      and dxx: "defends_rel (remove_argument U a) att E x"
    have Ux: "U x" and xa2: "x \<noteq> a" using xr by auto
    have "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
      using fresh_attacker_defends[where att=att and U=U and a=a and t=t and E=E]
        t a Et nEa Ux xa2 dxx by blast
    then show "E x"
      using L Ux unfolding extensions.completeExt_def by blast
  qed
  show "E t \<and> \<not> E a \<and> extensions.completeExt (remove_argument U a) att E"
    using Et nEa cf sd cd
    unfolding extensions.completeExt_def extensions.admissibleExt_def by blast
next
  assume R: "E t \<and> \<not> E a \<and> extensions.completeExt (remove_argument U a) att E"
  have ta: "t \<noteq> a" using t a by auto
  have Et: "E t" and nEa: "\<not> E a"
    and Rc: "extensions.completeExt (remove_argument U a) att E" using R by auto
  have cf: "extensions.conflictfreeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
    using Rc nEa t unfolding extensions.completeExt_def extensions.admissibleExt_def
      extensions.conflictfreeExt_def fresh_attacker_att_def induced_att_def by auto
  have nda: "\<not> defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E a"
    unfolding defends_rel_def fresh_attacker_att_def induced_att_def
    using t Et ta by auto
  have sd: "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> E x \<longrightarrow>
              defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
  proof (intro allI impI)
    fix x assume xU: "(U \<union> \<lbrace>t\<rbrace>) x" and Ex: "E x"
    show "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
    proof (cases "x = t")
      case True
      then show ?thesis
        unfolding defends_rel_def fresh_attacker_att_def induced_att_def
        using t ta by auto
    next
      case False
      have Ux: "U x" using xU False t by auto
      have xa2: "x \<noteq> a" using Ex nEa by auto
      have dxx: "defends_rel (remove_argument U a) att E x"
        using Rc Ex Ux xa2
        unfolding extensions.completeExt_def extensions.admissibleExt_def by blast
      show ?thesis
        using fresh_attacker_defends[where att=att and U=U and a=a and t=t and E=E]
          t a Et nEa Ux xa2 dxx by blast
    qed
  qed
  have cd: "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow>
              defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x \<longrightarrow> E x"
  proof (intro allI impI)
    fix x assume xU: "(U \<union> \<lbrace>t\<rbrace>) x"
      and dx: "defends_rel (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E x"
    show "E x"
    proof (cases "x = t")
      case True then show ?thesis using Et by simp
    next
      case False
      have Ux: "U x" using xU False t by auto
      have xa2: "x \<noteq> a" using dx nda by auto
      have dxx: "defends_rel (remove_argument U a) att E x"
        using fresh_attacker_defends[where att=att and U=U and a=a and t=t and E=E]
          t a Et nEa Ux xa2 dx by blast
      show "E x"
        using dxx Ux xa2 Rc unfolding extensions.completeExt_def by blast
    qed
  qed
  show "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
    using cf sd cd
    unfolding extensions.completeExt_def extensions.admissibleExt_def by blast
qed

(* Work in progress: the preferred-extension corollary of
   fresh_attacker_complete. The statement follows mathematically since
   preferred extensions are the maximal complete ones and the complete
   extensions of the two constructions coincide (modulo t and a); the
   Isar proof below is drafted but its maximality bookkeeping does not
   yet check within the session timeout.

lemma fresh_attacker_preferred:
  assumes t: "\<not> U t" and a: "U a"
  shows "extensions.preferredExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E \<longleftrightarrow>
         E t \<and> \<not> E a \<and> extensions.preferredExt (remove_argument U a) att E"
proof
  assume L: "extensions.preferredExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
  have comp: "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
    using L unfolding extensions.preferredExt_def maximal_rel_def by blast
  have chr: "E t \<and> \<not> E a \<and> extensions.completeExt (remove_argument U a) att E"
    using fresh_attacker_complete[where att=att and U=U and a=a and t=t and E=E] t a comp by blast
  have Et: "E t" and nEa: "\<not> E a"
    and Ec: "extensions.completeExt (remove_argument U a) att E"
    using chr by auto
  have max: "\<forall>X. extensions.completeExt (remove_argument U a) att X \<and>
      (\<forall>x. remove_argument U a x \<longrightarrow> E x \<longrightarrow> X x) \<longrightarrow>
      (\<forall>x. remove_argument U a x \<longrightarrow> (X x \<longleftrightarrow> E x))"
  proof (intro allI, intro impI)
    fix X assume X: "extensions.completeExt (remove_argument U a) att X \<and>
      (\<forall>x. remove_argument U a x \<longrightarrow> E x \<longrightarrow> X x)"
    define X2 where "X2 = (\<lambda>x. x = t \<or> (x \<noteq> a \<and> x \<noteq> t \<and> X x))"
    have X2eq: "\<forall>x. remove_argument U a x \<longrightarrow> (X2 x \<longleftrightarrow> X x)"
      using t unfolding X2_def by auto
    have X2c: "extensions.completeExt (remove_argument U a) att X2"
      using complete_restrict_cong[of "remove_argument U a" X2 X att] X2eq X by blast
    have X2props: "X2 t \<and> \<not> X2 a"
      using t a unfolding X2_def by auto
    have X2t: "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) X2"
      using fresh_attacker_complete[where att=att and U=U and a=a and t=t and E=X2]
        t a X2props X2c by blast
    have sub: "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> E x \<longrightarrow> X2 x"
      using X Et nEa t unfolding X2_def by auto
    have H: "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> (X2 x \<longleftrightarrow> E x)"
      using L X2t sub
      unfolding extensions.preferredExt_def maximal_rel_def id_def by blast
    have H2: "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow>
        ((x = t \<or> (x \<noteq> a \<and> x \<noteq> t \<and> X x)) \<longleftrightarrow> E x)"
      using H by (simp add: X2_def)
    show "\<forall>x. remove_argument U a x \<longrightarrow> (X x \<longleftrightarrow> E x)"
      using H2 t by blast
  qed
  show "E t \<and> \<not> E a \<and> extensions.preferredExt (remove_argument U a) att E"
    using Et nEa Ec max
    unfolding extensions.preferredExt_def maximal_rel_def id_def by auto
next
  assume R: "E t \<and> \<not> E a \<and> extensions.preferredExt (remove_argument U a) att E"
  have Et: "E t" and nEa: "\<not> E a"
    and Rp: "extensions.preferredExt (remove_argument U a) att E" using R by auto
  have Ec: "extensions.completeExt (remove_argument U a) att E"
    using Rp unfolding extensions.preferredExt_def maximal_rel_def by blast
  have chr2: "E t \<and> \<not> E a \<and> extensions.completeExt (remove_argument U a) att E"
    using Et nEa Ec by auto
  have comp: "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
    using fresh_attacker_complete[where att=att and U=U and a=a and t=t and E=E] t a chr2 by blast
  have max: "\<forall>X. extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) X \<and>
      (\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> E x \<longrightarrow> X x) \<longrightarrow>
      (\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> (X x \<longleftrightarrow> E x))"
  proof (intro allI, intro impI)
    fix X assume X: "extensions.completeExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) X \<and>
      (\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> E x \<longrightarrow> X x)"
    have chrX: "X t \<and> \<not> X a \<and> extensions.completeExt (remove_argument U a) att X"
      using fresh_attacker_complete[where att=att and U=U and a=a and t=t and E=X] t a X by blast
    have Xt: "X t" and nXa: "\<not> X a"
      and Xc: "extensions.completeExt (remove_argument U a) att X"
      using chrX by auto
    have "\<forall>x. remove_argument U a x \<longrightarrow> (X x \<longleftrightarrow> E x)"
      using Rp Xc X
      unfolding extensions.preferredExt_def maximal_rel_def id_def by auto
    then show "\<forall>x. (U \<union> \<lbrace>t\<rbrace>) x \<longrightarrow> (X x \<longleftrightarrow> E x)"
      using Xt nXa Et nEa by auto
  qed
  show "extensions.preferredExt (U \<union> \<lbrace>t\<rbrace>) (fresh_attacker_att att U a t) E"
    using comp max
    unfolding extensions.preferredExt_def maximal_rel_def id_def by auto
qed
*)

end
