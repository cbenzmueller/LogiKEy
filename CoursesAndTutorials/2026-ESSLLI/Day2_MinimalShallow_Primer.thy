theory Day2_MinimalShallow_Primer
  imports Main
begin

\<comment>\<open>A minimal shallow embedding of propositional modal logic in HOL, following
   C. Benzmüller: Faithful Logic Embeddings in HOL — Deep and Shallow, CADE-30,
   2025 (arxiv.org/abs/2502.19311). Modal formulas become predicates on worlds;
   Box quantifies over R-successors; no new logic is needed — HOL does it all.\<close>

  typedecl i                                                     \<comment>\<open>type of possible worlds\<close>
  type_synonym \<sigma> = "i\<Rightarrow>bool"                        \<comment>\<open>modal formulas as world-predicates\<close>
  consts R::"i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>r" 70)             \<comment>\<open>accessibility relation\<close>

  definition mnot::"\<sigma>\<Rightarrow>\<sigma>"       ("\<^bold>\<not>_"[52]53)    where       "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  definition mand::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 51)  where    "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<psi> w"
  definition mimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 49) where   "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w"
  definition mbox::"\<sigma>\<Rightarrow>\<sigma>"      ("\<^bold>\<box>_"[52]53)     where      "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. w\<^bold>rv \<longrightarrow> \<phi> v"
  definition mdia::"\<sigma>\<Rightarrow>\<sigma>"       ("\<^bold>\<diamond>_"[52]53)     where    "  \<^bold>\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. w\<^bold>rv \<and> \<phi> v"
  definition valid::"\<sigma>\<Rightarrow>bool"   ("\<lfloor>_\<rfloor>")               where      "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"

  named_theorems D
  declare mnot_def[D] mand_def[D] mimp_def[D] mbox_def[D] mdia_def[D] valid_def[D]

\<comment>\<open>Warm-up: axiom K and the necessitation rule hold in every frame.\<close>

  lemma K:      "\<lfloor>\<^bold>\<box>(\<phi>\<^bold>\<rightarrow>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>"       unfolding D by auto
  lemma NEC:  "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>"                          unfolding D by auto

\<comment>\<open>Sahlqvist correspondences: modal axiom schemes \<longleftrightarrow> frame conditions on R.\<close>

  lemma corr_T: "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x. x\<^bold>rx)"  \<comment>\<open>reflexive\<close>
    unfolding D by metis                                      
  lemma corr_D: "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x. \<exists>y. x\<^bold>ry)"  \<comment>\<open>serial; base of deontic logic KD, see Day 3\<close>
    unfolding D by metis

  \<comment>\<open>Examplary, more detailled investigation of seriality\<close>
  lemma "\<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>" unfolding D nitpick[show_all,format=2,card=1] oops
  lemma "(\<forall>x. x\<^bold>rx) \<longrightarrow> (\<forall>x. \<exists>y. x\<^bold>ry)" by blast
  lemma "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<longrightarrow> (\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>)" unfolding D by auto
  lemma "(\<forall>x. \<exists>y. x\<^bold>ry) \<longrightarrow> (\<forall>x. x\<^bold>rx)" unfolding D nitpick[show_all,format=2,card=2] oops
  lemma "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>) \<longrightarrow> (\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>)" unfolding D nitpick[show_all,format=2,card=2] oops

  lemma corr_B: "(\<forall>\<phi>. \<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x y. x\<^bold>ry \<longrightarrow> y\<^bold>rx)" \<comment>\<open>symmetric\<close>
    using D by fastforce
  lemma corr_4: "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x y z. x\<^bold>ry \<and> y\<^bold>rz \<longrightarrow> x\<^bold>rz)" \<comment>\<open>transitive\<close>
    unfolding D by metis                                      
  lemma corr_5: "(\<forall>\<phi>. \<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz)" \<comment>\<open>euclidean\<close>
    proof -
      have 1: "(\<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz) \<longrightarrow> (\<forall>\<phi>. \<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>)" using D by (smt (verit, ccfv_threshold))    
      have 2: "(\<forall>\<phi>. \<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>) \<longrightarrow> (\<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz)" unfolding D by force
      then  show ?thesis using 1 2 by blast
    qed

\<comment>\<open>KT5 = S5: reflexive + euclidean = equivalence relation.\<close>

  lemma S5: "((\<forall>x. x\<^bold>rx) \<and> (\<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz)) \<longleftrightarrow> ((\<forall>x. x\<^bold>rx) \<and> (\<forall>x y. x\<^bold>ry \<longrightarrow> y\<^bold>rx) \<and> (\<forall>x y z. x\<^bold>ry \<and> y\<^bold>rz \<longrightarrow> x\<^bold>rz))"
    by metis

\<comment>\<open>KT5 = S5 (KTB4):\<close>

  lemma S5': "((\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>)) \<longleftrightarrow> ((\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>))"
    using corr_5 corr_B corr_4 corr_T S5 by simp

\<comment>\<open>Two simple examples. First: \<diamond>\<box>\<phi> \<rightarrow> \<phi> holds already in KB — the witness world
   for \<diamond>\<box>\<phi> sees w back by symmetry, hence \<phi> holds at w. In basic K it fails:
   nitpick finds a dead-end witness world that makes \<box>\<phi> vacuously true.\<close>

  lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" unfolding D nitpick[show_all,format=2,card=2] oops
  lemma exKB: "(\<forall>x y. x\<^bold>ry \<longrightarrow> y\<^bold>rx) \<Longrightarrow> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" unfolding D by blast

\<comment>\<open>Second: \<diamond>\<box>\<phi> \<rightarrow> \<box>\<phi> needs S5 — it follows from the S5 frame conditions
   (euclideanness does the real work), but in KB it fails: nitpick finds a
   symmetric countermodel, a two-world cycle where only one world satisfies \<phi>.\<close>

  lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" unfolding D nitpick[show_all,format=2,card=2] oops
  lemma "(\<forall>x y. x\<^bold>ry \<longrightarrow> y\<^bold>rx) \<Longrightarrow> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" unfolding D nitpick[show_all,format=2,card=2] oops
  lemma exS5: "\<lbrakk>\<forall>x. x\<^bold>rx; \<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz\<rbrakk> \<Longrightarrow> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" unfolding D by blast

end
