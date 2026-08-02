section\<open>Preliminaries\<close>

theory FatioFaithful_preliminaries
  imports Main
begin

typedecl \<w>  \<comment>\<open>type of possible worlds\<close>
typedecl \<S>  \<comment>\<open>type of propositional constant symbols of the content logic\<close>
datatype Speaker = a | b | c  \<comment>\<open>the dialogue participants\<close>

type_synonym \<W> = "\<w>\<Rightarrow>bool"              \<comment>\<open>world domains\<close>
type_synonym \<R> = "Speaker\<Rightarrow>\<w>\<Rightarrow>\<w>\<Rightarrow>bool"  \<comment>\<open>agent-indexed accessibility relations\<close>
type_synonym \<V> = "\<S>\<Rightarrow>\<w>\<Rightarrow>bool"           \<comment>\<open>valuations of content atoms\<close>

\<comment>\<open>Bounded universal quantifier, as in \<^cite>\<open>"FaithfulPMLinHOL-AFP"\<close>\<close>
abbreviation(input) BoundedAll::"\<W>\<Rightarrow>\<W>\<Rightarrow>bool" where "BoundedAll W \<phi> \<equiv> \<forall>x. W x \<longrightarrow> \<phi> x"
syntax "_BoundedAll":: "pttrn\<Rightarrow>\<W>\<Rightarrow>bool\<Rightarrow>bool" ("(3\<forall>(_/:_)./ _)" [0, 0, 10] 10)
translations "\<forall>x:W. \<phi>" \<rightleftharpoons> "CONST BoundedAll W (\<lambda>x. \<phi>)"

end
