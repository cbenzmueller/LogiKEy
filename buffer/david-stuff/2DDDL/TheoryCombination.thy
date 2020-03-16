(*<*)
theory TheoryCombination
  imports Main
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>Semantic Embedding of Carmo and Jones' Dyadic Deontic Logic (DDL) augmented with Kaplanian contexts\<close>

subsection \<open>Definition of Types\<close>

typedecl w   \<comment> \<open>  Type for possible worlds (Kaplan's "circumstances of evaluation" or "counterfactual situations")  \<close>
typedecl e   \<comment> \<open>  Type for individuals (entities eligible to become agents) \<close>
typedecl c   \<comment> \<open>  Type for Kaplanian "contexts of use" \<close>
type_synonym wo = "w\<Rightarrow>bool" \<comment> \<open>  contents/propositions are identified with their truth-sets \<close>
type_synonym cwo = "c\<Rightarrow>wo"  \<comment> \<open>  sentence meaning (Kaplan's "character") is a function from contexts to contents \<close>
type_synonym m = "cwo"      \<comment> \<open>  we use the letter 'm' for characters (reminiscent of "meaning") \<close>

subsection \<open>Semantic Characterisation of DDL\<close>

abbreviation subset::"wo\<Rightarrow>wo\<Rightarrow>bool" (infix "\<sqsubseteq>" 46) where "\<alpha> \<sqsubseteq> \<beta> \<equiv> \<forall>w. \<alpha> w  \<longrightarrow> \<beta> w"
abbreviation intersection::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<sqinter>" 48) where "\<alpha> \<sqinter> \<beta> \<equiv> \<lambda>x. \<alpha> x \<and> \<beta> x"
abbreviation union::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<squnion>" 48) where "\<alpha> \<squnion> \<beta> \<equiv> \<lambda>x. \<alpha> x \<or> \<beta> x"
abbreviation complement::"wo\<Rightarrow>wo" ("\<sim>_"[45]46) where "\<sim>\<alpha> \<equiv> \<lambda>x. \<not>\<alpha> x"
abbreviation instantiated::"wo\<Rightarrow>bool" ("\<I>_"[45]46) where "\<I> \<phi> \<equiv> \<exists>x. \<phi> x"
abbreviation setEq::"wo\<Rightarrow>wo\<Rightarrow>bool" (infix "=\<^sub>s" 46) where "\<alpha> =\<^sub>s \<beta> \<equiv> \<forall>x. \<alpha> x \<longleftrightarrow> \<beta> x"
abbreviation univSet :: "wo" ("\<top>") where "\<top> \<equiv> \<lambda>w. True"
abbreviation emptySet :: "wo" ("\<bottom>") where "\<bottom> \<equiv> \<lambda>w. False"

consts
av::"w\<Rightarrow>wo"   \<comment> \<open> set of worlds that are open alternatives (aka. actual versions) of w \<close>
pv::"w\<Rightarrow>wo"   \<comment> \<open> set of worlds that are possible alternatives (aka. potential versions) of w \<close>
ob::"wo\<Rightarrow>wo\<Rightarrow>bool" \<comment> \<open> set of propositions which are obligatory in a given context (of type wo)  \<close>

axiomatization where
sem_3a: "\<forall>w. \<I>(av w)" and \<comment> \<open>  av is serial: in every situation there is always an open alternative \<close>
sem_4a: "\<forall>w. av w \<sqsubseteq> pv w" and \<comment> \<open>  open alternatives are possible alternatives \<close>
sem_4b: "\<forall>w. pv w w" and \<comment> \<open>  pv is reflexive: every situation is a possible alternative to itself \<close>
sem_5a: "\<forall>X. \<not>(ob X \<bottom>)" and \<comment> \<open>  contradictions cannot be obligatory \<close>
sem_5b: "\<forall>X Y Z. (X \<sqinter> Y) =\<^sub>s (X \<sqinter> Z) \<longrightarrow> (ob X Y \<longleftrightarrow> ob X Z)" and
sem_5c: "\<forall>X Y Z. \<I>(X \<sqinter> Y \<sqinter> Z) \<and> ob X Y \<and> ob X Z \<longrightarrow> ob X (Y \<sqinter> Z)" and
sem_5d: "\<forall>X Y Z. (Y \<sqsubseteq> X \<and> ob X Y \<and> X \<sqsubseteq> Z) \<longrightarrow> ob Z ((Z \<sqinter> (\<sim>X)) \<squnion> Y)" and
sem_5e: "\<forall>X Y Z. Y \<sqsubseteq> X \<and> ob X Z \<and> \<I>(Y \<sqinter> Z) \<longrightarrow> ob Y Z"

subsection \<open>Verifying Semantic Conditions\<close>

lemma sem_5b1: "ob X Y \<longrightarrow> ob X (Y \<sqinter> X)" by (metis (no_types, lifting) sem_5b)
lemma sem_5b2: "(ob X (Y \<sqinter> X) \<longrightarrow> ob X Y)" by (metis (no_types, lifting) sem_5b) 
lemma sem_5ab: "ob X Y \<longrightarrow> \<I>(X \<sqinter> Y)" by (metis (full_types) sem_5a sem_5b)
lemma sem_5bd1: "Y \<sqsubseteq> X \<and> ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> Y)" using sem_5b sem_5d by smt
lemma sem_5bd2: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((Z \<sqinter> (\<sim>X)) \<squnion> Y)"  using sem_5b sem_5d  by (smt sem_5b1)  
lemma sem_5bd3: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> Y)"  by (smt sem_5bd2 sem_5b) 
lemma sem_5bd4: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> (X \<sqinter>  Y))" using sem_5bd3 by auto
lemma sem_5bcd: "(ob X Z \<and> ob Y Z) \<longrightarrow> ob (X \<squnion> Y) Z" using sem_5b sem_5c sem_5d oops
(* 5e and 5ab justify redefinition of @{cite "O\<langle>\<phi>|\<sigma>\<rangle>"} as (ob A B)*)
lemma "ob A B \<longleftrightarrow>  (\<I>(A \<sqinter> B) \<and> (\<forall>X. X \<sqsubseteq> A \<and> \<I>(X \<sqinter> B) \<longrightarrow> ob X B))" using sem_5e sem_5ab by blast

abbreviation pand::"m\<Rightarrow>m\<Rightarrow>m" (infixr"\<^bold>\<and>" 51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<and>(\<psi> c w)"
abbreviation por::"m\<Rightarrow>m\<Rightarrow>m" (infixr"\<^bold>\<or>" 50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<or>(\<psi> c w)"
abbreviation pimp::"m\<Rightarrow>m\<Rightarrow>m" (infix"\<^bold>\<rightarrow>" 49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<longrightarrow>(\<psi> c w)"
abbreviation pequ::"m\<Rightarrow>m\<Rightarrow>m" (infix"\<^bold>\<leftrightarrow>" 48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<longleftrightarrow>(\<psi> c w)"
abbreviation pnot::"m\<Rightarrow>m" ("\<^bold>\<not>_" [52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>c w. \<not>(\<phi> c w)"

abbreviation cjboxa :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sub>a_" [52]53) where "\<^bold>\<box>\<^sub>a\<phi> \<equiv> \<lambda>c w. \<forall>v. (av w) v \<longrightarrow> (\<phi> c v)"
abbreviation cjdiaa :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sub>a_" [52]53) where "\<^bold>\<diamond>\<^sub>a\<phi> \<equiv> \<lambda>c w. \<exists>v. (av w) v \<and> (\<phi> c v)"
abbreviation cjboxp :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sub>p_" [52]53) where "\<^bold>\<box>\<^sub>p\<phi> \<equiv> \<lambda>c w. \<forall>v. (pv w) v \<longrightarrow> (\<phi> c v)"
abbreviation cjdiap :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sub>p_" [52]53) where "\<^bold>\<diamond>\<^sub>p\<phi> \<equiv> \<lambda>c w. \<exists>v. (pv w) v \<and> (\<phi> c v)"
abbreviation cjtaut :: "m" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>c w. True"
abbreviation cjcontr :: "m" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>c w. False"

abbreviation cjod :: "m\<Rightarrow>m\<Rightarrow>m" ("\<^bold>O\<langle>_|_\<rangle>"54) where "\<^bold>O\<langle>\<phi>|\<sigma>\<rangle> \<equiv> \<lambda>c w. ob (\<sigma> c) (\<phi> c)"
abbreviation cjos :: "m\<Rightarrow>m" ("\<^bold>O\<langle>_\<rangle>"[53]54) where "\<^bold>O\<langle>\<phi>\<rangle> \<equiv> \<^bold>O\<langle>\<phi>|\<^bold>\<top>\<rangle>"
abbreviation cjoa :: "m\<Rightarrow>m" ("\<^bold>O\<^sub>a_" [53]54) where "\<^bold>O\<^sub>a\<phi> \<equiv> \<lambda>c w. (ob (av w)) (\<phi> c) \<and> (\<exists>x. (av w) x \<and> \<not>(\<phi> c x))"
abbreviation cjop :: "m\<Rightarrow>m" ("\<^bold>O\<^sub>i_" [53]54) where "\<^bold>O\<^sub>i\<phi> \<equiv> \<lambda>c w. (ob (pv w)) (\<phi> c) \<and> (\<exists>x. (pv w) x \<and> \<not>(\<phi> c x))"

abbreviation modvalidctx :: "m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>M") where "\<lfloor>\<phi>\<rfloor>\<^sup>M \<equiv> \<lambda>c. \<forall>w. \<phi> c w" \<comment> \<open> context-dependent modal validity \<close>
abbreviation modvalid :: "m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sup>M c" \<comment> \<open> general modal validity (modally valid in each context) \<close>

abbreviation mboxS5 :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sup>S\<^sup>5_" [52]53) where "\<^bold>\<box>\<^sup>S\<^sup>5\<phi> \<equiv> \<lambda>c w. \<forall>v. \<phi> c v"
abbreviation mdiaS5 :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sup>S\<^sup>5_" [52]53) where "\<^bold>\<diamond>\<^sup>S\<^sup>5\<phi> \<equiv> \<lambda>c w. \<exists>v. \<phi> c v"


subsection \<open>Verifying the Embedding\<close>

lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>aP\<rfloor>" nitpick oops \<comment> \<open> (actual) deontic modal collapse is countersatisfiable \<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>iP\<rfloor>" nitpick oops \<comment> \<open> (ideal) deontic modal collapse is countersatisfiable \<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aP\<rfloor>" nitpick oops \<comment> \<open> alethic modal collapse is countersatisfiable (implies all other necessity operators) \<close>

lemma NecDDLa: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>"    by simp (* Valid only using classical (not  Kaplan's indexical) validity*)
lemma NecDDLp:  "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>pA\<rfloor>"   by simp (* Valid only using classical (not  Kaplan's indexical) validity*)


subsection \<open>Verifying Axiomatic Characterisation and C&J Theorems\<close>

lemma C_2: "\<lfloor>\<^bold>O\<langle>A | B\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>S\<^sup>5(B \<^bold>\<and> A)\<rfloor>"   by (simp add: sem_5ab)
lemma C_3:  "\<lfloor>((\<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> B \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>(B \<^bold>\<and> C)| A\<rangle>\<rfloor>"   by (simp add: sem_5c)
lemma C_4: "\<lfloor>(\<^bold>\<box>\<^sup>S\<^sup>5(A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<langle>C|B\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>C|A\<rangle>\<rfloor>"   using sem_5e by blast
lemma C_5: "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<langle>C|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>C|B\<rangle>)\<rfloor>"   using sem_5ab sem_5e by blast
lemma C_6: "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O\<langle>A|C\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>B|C\<rangle>)\<rfloor>"   by (metis sem_5b)
lemma C_7: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>S\<^sup>5\<^bold>O\<langle>B|A\<rangle>\<rfloor>"   by blast 
lemma C_8: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>A \<^bold>\<rightarrow> B| \<^bold>\<top>\<rangle>\<rfloor>" using sem_5bd4   by presburger

lemma CJ_3: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aA\<rfloor>"   by (simp add: sem_4a)
lemma CJ_4: "\<lfloor>\<^bold>\<not>\<^bold>O\<langle>\<^bold>\<bottom>|A\<rangle>\<rfloor>"   by (simp add: sem_5a)
lemma CJ_5: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>B\<^bold>\<and>C|A\<rangle>\<rfloor>"   nitpick oops \<comment> \<open> countermodel found \<close>
lemma CJ_5_minus: "\<lfloor>\<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> (\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>B\<^bold>\<and>C|A\<rangle>\<rfloor>"   by (simp add: sem_5c)
lemma CJ_6: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>B|A\<^bold>\<and>B\<rangle>\<rfloor>"   by (smt C_2 C_4)
lemma CJ_7: "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<longrightarrow> \<lfloor>\<^bold>O\<langle>C|A\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>C|B\<rangle>\<rfloor>"   using sem_5ab sem_5e by blast (* Valid only using classical (not Kaplan's indexical) validity*)
lemma CJ_8: "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>O\<langle>A|C\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>B|C\<rangle>\<rfloor>"   using C_6 by simp (* Valid only using classical (not Kaplan's indexical) validity*)
lemma CJ_9a: "\<lfloor>\<^bold>\<diamond>\<^sub>p\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p\<^bold>O\<langle>B|A\<rangle>\<rfloor>"   by simp
lemma CJ_9p: "\<lfloor>\<^bold>\<diamond>\<^sub>a\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>a\<^bold>O\<langle>B|A\<rangle>\<rfloor>"   by simp
lemma CJ_9_var_a: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>a\<^bold>O\<langle>B|A\<rangle>\<rfloor>"   by simp
lemma CJ_9_var_b: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p\<^bold>O\<langle>B|A\<rangle>\<rfloor>"   by simp
lemma CJ_10: "\<lfloor>\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<langle>C|B\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>C|A\<^bold>\<and>B\<rangle>\<rfloor>"   by (smt C_4)
lemma CJ_11a: "\<lfloor>(\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^sub>aB) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>"   nitpick oops \<comment> \<open>  countermodel found \<close>
lemma CJ_11a_var: "\<lfloor>\<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> (\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^sub>aB) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>"   using sem_5c by auto
lemma CJ_11p: "\<lfloor>(\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>O\<^sub>iB) \<^bold>\<rightarrow> \<^bold>O\<^sub>i(A \<^bold>\<and> B)\<rfloor>" nitpick oops \<comment> \<open>  countermodel found \<close>
lemma CJ_11p_var: "\<lfloor>\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> (\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>O\<^sub>iB) \<^bold>\<rightarrow> \<^bold>O\<^sub>i(A \<^bold>\<and> B)\<rfloor>" using sem_5c by auto
lemma CJ_12a: "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a(\<^bold>\<not>A))\<rfloor>" using sem_5ab by blast (*using C_2 by blast *)
lemma CJ_12p: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>i(\<^bold>\<not>A))\<rfloor>" using sem_5ab by blast (*using C_2 by blast*) 
lemma CJ_13a: "\<lfloor>\<^bold>\<box>\<^sub>a(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>aA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>aB)\<rfloor>" using sem_5b by metis (*using C_6 by blast *)
lemma CJ_13p: "\<lfloor>\<^bold>\<box>\<^sub>p(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>iA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>iB)\<rfloor>" using sem_5b by metis (*using C_6 by blast *)
lemma CJ_O_O: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>A \<^bold>\<rightarrow> B|\<^bold>\<top>\<rangle>\<rfloor>" using sem_5bd4 by presburger
lemma CJ_Oi_Oa: "\<lfloor>(\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>\<diamond>\<^sub>aA \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>A)) \<^bold>\<rightarrow> \<^bold>O\<^sub>aA\<rfloor>" using sem_5e sem_4a by blast
lemma CJ_14a: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>aA \<^bold>\<and> \<^bold>\<diamond>\<^sub>aB \<^bold>\<and> \<^bold>\<diamond>\<^sub>a\<^bold>\<not>B \<^bold>\<rightarrow> \<^bold>O\<^sub>aB\<rfloor>" using sem_5e by blast
lemma CJ_14p: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>pA \<^bold>\<and> \<^bold>\<diamond>\<^sub>pB \<^bold>\<and> \<^bold>\<diamond>\<^sub>p\<^bold>\<not>B \<^bold>\<rightarrow> \<^bold>O\<^sub>iB\<rfloor>" using sem_5e by blast
lemma CJ_15a: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow>  \<^bold>O\<^sub>a(A \<^bold>\<rightarrow> B)\<rfloor>" using CJ_O_O sem_5e by fastforce (*using CJ_O_O CJ_14a by blast*)
lemma CJ_15p: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow>  \<^bold>O\<^sub>i(A \<^bold>\<rightarrow> B)\<rfloor>" using CJ_O_O sem_5e by fastforce (*using CJ_O_O CJ_14p by blast*)

section \<open>Extending the Carmo and Jones DDL Logical Framework\<close>

consts Agent::"c\<Rightarrow>e"  \<comment> \<open> function retrieving the agent corresponding to context c \<close>   
consts World::"c\<Rightarrow>w"  \<comment> \<open> function retrieving the world corresponding to context c \<close>

abbreviation ldtruectx::"m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>_") where "\<lfloor>\<phi>\<rfloor>\<^sub>c \<equiv> \<phi> c (World c)" \<comment> \<open>  truth in the given context \<close>
abbreviation ldvalid::"m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>D") where "\<lfloor>\<phi>\<rfloor>\<^sup>D \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sub>c" \<comment> \<open> LD validity (true in every context) \<close>

lemma "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>A\<rfloor>\<^sup>D" by simp
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>A\<rfloor>" nitpick oops \<comment> \<open> countermodel found \<close>

lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>aP\<rfloor>\<^sup>D" nitpick oops
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aP\<rfloor>\<^sup>D" nitpick oops

lemma NecLDa: "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>\<^sup>D"  nitpick oops
lemma NecLDp:  "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>pA\<rfloor>\<^sup>D" nitpick oops

abbreviation ldvalidbox :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sup>D_" [52]53) where "\<^bold>\<box>\<^sup>D\<phi> \<equiv> \<lambda>c w. \<lfloor>\<phi>\<rfloor>\<^sup>D" \<comment> \<open> notice the D superscript \<close>
lemma "\<lfloor>\<^bold>\<box>\<^sup>D\<phi>\<rfloor>\<^sub>C \<equiv> \<forall>c.\<lfloor>\<phi>\<rfloor>\<^sub>c" by simp \<comment> \<open>  this operator works analogously to the box operator in modal logic S5 \<close>

lemma NecLD: "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sup>DA\<rfloor>\<^sup>D"  by simp

abbreviation mforall::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>c w.\<forall>x. (\<Phi> x c w)"
abbreviation mexists::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>c w.\<exists>x. (\<Phi> x c w)"    
abbreviation mforallBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. (\<phi> x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexistsBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. (\<phi> x) \<equiv> \<^bold>\<exists>\<phi>"


type_synonym cwe = "c\<Rightarrow>w\<Rightarrow>e" \<comment> \<open>type alias for indexical individual terms\<close>
abbreviation cthe::"(c\<Rightarrow>w\<Rightarrow>e\<Rightarrow>bool)\<Rightarrow>cwe" ("the") where "the \<phi> \<equiv> \<lambda>c w. THE x. \<phi> c w x"
abbreviation ctheBinder::"(c\<Rightarrow>w\<Rightarrow>e\<Rightarrow>bool)\<Rightarrow>cwe" (binder"the"[8]9) where "the x. (\<phi> x) \<equiv> the \<phi>"

abbreviation dthat::"cwe\<Rightarrow>cwe" ("dthat[_]" [62]63) where "dthat[\<alpha>] \<equiv> \<lambda>c w. \<alpha> c (World c)"
abbreviation Dthat::"(c\<Rightarrow>w\<Rightarrow>e\<Rightarrow>bool)\<Rightarrow>cwe" ("Dthat[_]" [62]63) where "Dthat[\<alpha>] \<equiv> dthat[the \<alpha>] "

abbreviation ceq:: "cwe\<Rightarrow>cwe\<Rightarrow>m" (infix "\<^bold>\<approx>" 60)  where "\<alpha> \<^bold>\<approx> \<beta> \<equiv> \<lambda>c w. \<alpha> c w = \<beta> c w" (**standard equality for characters*)

lemma "\<lfloor>\<alpha> \<^bold>\<approx> dthat[\<alpha>]\<rfloor>\<^sup>D" by simp \<comment> \<open>using indexical validity\<close>
lemma "\<lfloor>\<alpha> \<^bold>\<approx> dthat[\<alpha>]\<rfloor>" nitpick oops  \<comment> \<open>counterexample if using classical validity\<close>
lemma "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(\<alpha> \<^bold>\<approx> dthat[\<alpha>])\<rfloor>\<^sup>D" nitpick oops  \<comment> \<open>counterexample\<close>
lemma "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(dthat[\<beta>] \<^bold>\<approx> dthat[\<alpha>])\<rfloor>\<^sub>x\<Longrightarrow>\<lfloor>(dthat[\<beta>] \<^bold>\<approx> dthat[\<alpha>])\<rfloor>\<^sup>D" nitpick oops  \<comment> \<open>counterexample\<close>
lemma "\<lfloor>dthat[\<beta>] \<^bold>\<approx> dthat[\<alpha>]\<rfloor>\<^sup>D \<longleftrightarrow> \<lfloor>\<beta> \<^bold>\<approx> \<alpha>\<rfloor>\<^sup>D" by simp
lemma "\<lfloor>dthat[\<beta>] \<^bold>\<approx> dthat[\<alpha>] \<^bold>\<leftrightarrow> (\<beta> \<^bold>\<approx> \<alpha>) \<rfloor>\<^sup>D" by simp

abbreviation cactually :: "m\<Rightarrow>m" ("\<^bold>\<A>_" [52]53) where "\<^bold>\<A>\<phi> \<equiv> \<lambda>c w. \<phi> c (World c)"

lemma "\<lfloor>\<phi> \<^bold>\<leftrightarrow> \<^bold>\<A>\<phi>\<rfloor>\<^sup>D" by simp
lemma "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(\<phi> \<^bold>\<leftrightarrow> \<^bold>\<A>\<phi>)\<rfloor>\<^sup>D" nitpick oops
lemma "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(\<phi> \<^bold>\<leftrightarrow> \<^bold>\<A>\<phi>)\<rfloor>" nitpick oops
lemma "\<lfloor>\<phi>\<rfloor>\<^sup>D \<longleftrightarrow>  \<lfloor>\<^bold>\<A>\<phi>\<rfloor> " by simp

abbreviation stable::"m\<Rightarrow>c\<Rightarrow>bool" where "stable \<phi> c \<equiv> \<forall>w. \<phi> c w \<longrightarrow> \<lfloor>\<phi>\<rfloor>\<^sup>M c"
abbreviation stableCharacter::"m\<Rightarrow>bool" where "stableCharacter \<phi> \<equiv> \<forall>c. stable \<phi> c"

lemma "\<forall>c. stable (\<^bold>\<A>\<phi>) c" by simp \<comment> \<open> (i)\<close>
lemma "stableCharacter \<phi> \<longrightarrow> (\<lfloor>\<phi>\<rfloor>\<^sup>D \<longrightarrow> \<lfloor>\<phi>\<rfloor>)" by blast \<comment> \<open> (ii)\<close>
lemma "stableCharacter \<phi> \<longrightarrow> (\<lfloor>\<phi>\<rfloor>\<^sup>D \<longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>a\<phi>\<rfloor>\<^sup>D)" by blast  \<comment> \<open> (iii)\<close>
lemma "\<lfloor>\<phi>\<rfloor>\<^sup>D \<longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>a\<phi>\<rfloor>\<^sup>D" nitpick oops \<comment> \<open>counterexample in the general case\<close>


(*<*)
end
(*>*)
