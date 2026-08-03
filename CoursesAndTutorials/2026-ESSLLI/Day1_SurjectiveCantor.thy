theory Day1_SurjectiveCantor  imports Main 
begin        
\<comment>\<open>Surjective Cantor theorem: traditional interactive proof\<close>
theorem SurjectiveCantor:  "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" 
 proof
  assume 1: "\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F"      \<comment>\<open>assume surjective G exist ... show contradiction\<close>
  obtain g::"'a\<Rightarrow>('a\<Rightarrow>bool)" where                      \<comment>\<open>fix such a mapping G, call it g\<close>
                2: "\<forall>F.\<exists>X. g X = F" using 1 by auto     \<comment>\<open>this g is surjective by assumption\<close>                        
  let ?F = "\<lambda>X.\<not> g X X"                                          \<comment>\<open>consider ?F = {X | \<not> X \<in> (g X)} — diagonalization\<close>
  have      3: "\<exists>Y. g Y = ?F" using 2 by metis      \<comment>\<open>obviously, there is Y s.t. g Y = ?F — since g surjective\<close>
  obtain a::'a where                                            \<comment>\<open>fix such a Y, call it y\<close>
                4: "g a = ?F" using 3 by auto               \<comment>\<open>obviously, g a = ?F \<close>
  have      5: "g a a = ?F a"  using 4 by metis      \<comment>\<open>obviously, g a a = ?F a — by functional extensionality\<close>
  have      6: "g a a = (\<not> g a a)" using 5 by auto  \<comment>\<open>hence, g a a = \<not> g a a  — by def. of ?F\<close>
  show False using 6 by auto                               \<comment>\<open>thus, contradiction\<close>
 qed
\<comment>\<open>Avoiding proof by contradiction (Fuenmayor & Benzmüller); doi: 10.13140/RG.2.2.31069.95201/1\<close>
theorem SurjectiveCantor':    "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" 
 proof - 
  {fix g :: "'a\<Rightarrow>('a\<Rightarrow>bool)"
    have 1: "\<forall>X.\<exists>Y.(\<not>g X Y) = (\<not>g Y Y)" by auto                          \<comment>\<open>trivial statement: choose Y=X\<close>
    have 2: "\<forall>X.\<exists>Y.(\<not>g X Y) = ((\<lambda>Z.\<not>g Z Z) Y)" using 1 by auto  \<comment>\<open>by \<lambda>-conversion & replacement\<close>
    have 3: "\<exists>F.\<forall>X.\<exists>Y.(\<not>g X Y) = (F Y)" using 2 by auto             \<comment>\<open>\<exists>-introduction applied to (\<lambda>Z.\<not> g Z Z)\<close>
    have 4: "\<exists>F.\<forall>X.\<not>(\<forall>Y.(g X Y) = (F Y))" using 3 by auto           \<comment>\<open>pull negation outwards\<close>
    have      "\<exists>F.\<forall>X.\<not>(g X = F)" using 4 by metis                        \<comment>\<open>by functional extensionality\<close>
   }
  hence 5: "\<forall>G.\<exists>F::'a\<Rightarrow>bool.\<forall>X::'a.\<not>(G X = F)" by auto              \<comment>\<open>\<forall>-introduction: g was chosen arbitrary\<close>
  have   6: "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" using 5 by auto \<comment>\<open>pull negation outwards\<close>
  thus ?thesis .                                                                           \<comment>\<open>done, avoiding proof by contradiction\<close>
qed
\<comment>\<open>Surjective Cantor theorem: automated proof by some internal/external theorem provers\<close>
theorem SurjectiveCantor'':    "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)"   
  nitpick                                                         \<comment>\<open>no counterexample found\<close>
  sledgehammer                                            \<comment>\<open>most internal provers give up\<close>
  sledgehammer[remote_leo2 remote_leo3]   \<comment>\<open>proof found — external leo provers succeed\<close>
  oops
\<comment>\<open>Surjective Cantor theorem (wrong formalization attempt): the types are crucial\<close>
theorem SurjectiveCantor''':    "\<not>(\<exists>G.\<forall>F::'b.\<exists>X::'a. G X = F)"   
  nitpick                     \<comment>\<open>counterexample found for card 'a = 1 and card 'b = 1: G =  G =  (\<lambda>x. (a1 := b1)\<close>
  nitpick[satisfy]        \<comment>\<open>model  found for card 'a = 1 and card 'b = 2\<close>
  nitpick[card 'a=2, card 'b=3]     \<comment>\<open>no counterexample found\<close>                                                                              
  oops 
end





