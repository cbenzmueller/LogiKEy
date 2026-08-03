theory Day2_MinimalShallow_Primer
  imports Main
begin

text\<open>A minimal shallow embedding of propositional modal logic in HOL, following
   C. Benzmüller: Faithful Logic Embeddings in HOL — Deep and Shallow, CADE-30,
   2025 (arxiv.org/abs/2502.19311). Modal formulas become predicates on worlds;
   Box quantifies over R-successors; no new logic is needed — HOL does it all.\<close>

typedecl i                                                    \<comment>\<open>type of possible worlds\<close>
type_synonym \<sigma> = "i\<Rightarrow>bool"                       \<comment>\<open>modal formulas as world-predicates\<close>
consts R::"i\<Rightarrow>i\<Rightarrow>bool" (infix "\<^bold>r" 70)             \<comment>\<open>accessibility relation\<close>

definition mnot::"\<sigma>\<Rightarrow>\<sigma>"       ("\<^bold>\<not>_"[52]53)    where    "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
definition mand::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 51)  where  "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<psi> w"
definition mimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w"
definition mbox::"\<sigma>\<Rightarrow>\<sigma>"      ("\<^bold>\<box>_"[52]53)     where    "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. w\<^bold>rv \<longrightarrow> \<phi> v"
definition mdia::"\<sigma>\<Rightarrow>\<sigma>"       ("\<^bold>\<diamond>_"[52]53)     where    "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. w\<^bold>rv \<and> \<phi> v"
definition valid::"\<sigma>\<Rightarrow>bool"   ("\<lfloor>_\<rfloor>")               where     "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"

named_theorems D
declare mnot_def[D] mand_def[D] mimp_def[D] mbox_def[D] mdia_def[D] valid_def[D]

text\<open>Warm-up: axiom K and the necessitation rule hold in every frame.\<close>

lemma K:      "\<lfloor>\<^bold>\<box>(\<phi>\<^bold>\<rightarrow>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>"       unfolding D by auto
lemma NEC:  "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>"                          unfolding D by auto

text\<open>Sahlqvist correspondences: modal axiom schemes \<longleftrightarrow> frame conditions on R.\<close>

lemma corr_T: "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x. x\<^bold>rx)"  \<comment>\<open>reflexive\<close>
  unfolding D by metis                                      
lemma corr_D: "(\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>) \<longleftrightarrow> (\<forall>x. \<exists>y. x\<^bold>ry)"  \<comment>\<open>serial; base of deontic logic KD, see Day 3\<close>
  unfolding D by metis
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

text\<open>S5 = K + T + 5: reflexive + euclidean = equivalence relation.\<close>

lemma S5: "((\<forall>x. x\<^bold>rx) \<and> (\<forall>x y z. x\<^bold>ry \<and> x\<^bold>rz \<longrightarrow> y\<^bold>rz)) \<longleftrightarrow> ((\<forall>x. x\<^bold>rx) \<and> (\<forall>x y. x\<^bold>ry \<longrightarrow> y\<^bold>rx) \<and> (\<forall>x y z. x\<^bold>ry \<and> y\<^bold>rz \<longrightarrow> x\<^bold>rz))"
  by metis

text\<open>Note: T + D + 4 would NOT suffice — reflexive + serial + transitive does not
  imply euclidean (counterexample: \<le> on the naturals); that is the semantic face
  of S4 \<noteq> S5. The correct axiomatic counterpart of an equivalence relation is
  T + B + 4, i.e. KT5 = KTB4:\<close>

lemma S5': "((\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>)) \<longleftrightarrow> ((\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>) \<and> (\<forall>\<phi>. \<lfloor>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>))"
  by (metis corr_T corr_B corr_4 corr_5 S5)

end
