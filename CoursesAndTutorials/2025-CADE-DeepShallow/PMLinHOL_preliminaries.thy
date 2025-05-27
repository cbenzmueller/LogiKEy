theory PMLinHOL_preliminaries  imports Main                                                            (* Christoph Benzmüller, 2025 *)     
begin        
\<comment>\<open>Type declarations common for both the deep and shallow embedding\<close>
  typedecl \<w> \<comment>\<open>Type for possible worlds\<close> 
  typedecl \<S>  \<comment>\<open>Type for propositional constant symbols\<close> 
  consts p::\<S> q::\<S> \<comment>\<open>Some propositional constant symbols\<close> 
  type_synonym \<W> = "\<w>\<Rightarrow>bool"  \<comment>\<open>Type for sets of possible worlds\<close> 
  type_synonym \<R> = "\<w>\<Rightarrow>\<w>\<Rightarrow>bool"  \<comment>\<open>Type for accessibility relations\<close> 
  type_synonym \<V>  = "\<S>\<Rightarrow>\<w>\<Rightarrow>bool"  \<comment>\<open>Type for valuation functions\<close> 
\<comment>\<open>Some useful predicates for accessibility relations\<close>
  abbreviation(input) "reflexive        \<equiv> \<lambda>R::\<R>. \<forall>x. R x x"
  abbreviation(input) "symmetric     \<equiv> \<lambda>R::\<R>. \<forall>x y. R x y \<longrightarrow> R y x"
  abbreviation(input) "transitive       \<equiv> \<lambda>R::\<R>. \<forall>x y z. (R x y \<and> R y z)  \<longrightarrow> R x z"
  abbreviation(input) "equivrel         \<equiv> \<lambda>R::\<R>. reflexive R \<and> symmetric R \<and> transitive R"
  abbreviation(input) "irreflexive      \<equiv> \<lambda>R::\<R>. \<forall>x. \<not>R x x" 
  abbreviation(input) "euclidean       \<equiv> \<lambda>R::\<R>. \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
  abbreviation(input) "wellfounded   \<equiv> \<lambda>R::\<R>. \<forall>P::\<W>. (\<forall>x. (\<forall>y. R y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow>  (\<forall>x. P x)" 
  abbreviation(input) "converserel    \<equiv> \<lambda>R::\<R>. \<lambda>y. \<lambda>x. R x y" 
  abbreviation(input) "conversewf    \<equiv> \<lambda>R::\<R>. wellfounded (converserel R)" 
\<comment>\<open>Bounded universal quantifier: \<open>\<forall>x:W. \<phi>\<close> stands for \<open>\<forall>x. W x \<longrightarrow> \<phi> x\<close>\<close>
  abbreviation(input) "BAll W \<phi> \<equiv> \<forall>x::\<w>. W x \<longrightarrow> \<phi> x" syntax "BAll"::"pttrn\<Rightarrow>\<W>\<Rightarrow>bool\<Rightarrow>bool" ("(3\<forall>(_/:_)./_)" [0,0,10]10)
  translations "\<forall>x:W. \<phi>" \<rightleftharpoons> "CONST BAll W (\<lambda>x. \<phi>)"
\<comment>\<open>Backward implication; useful to have\<close> abbreviation(input) Bimp (infixr "\<longleftarrow>" 50) where "\<phi> \<longleftarrow> \<psi> \<equiv> \<psi> \<longrightarrow> \<phi>"
\<comment>\<open>Further settings\<close> declare[[syntax_ambiguity_warning=false]] nitpick_params[user_axioms,expect=genuine]
end

