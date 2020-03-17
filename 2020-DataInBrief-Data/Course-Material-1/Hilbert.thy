(*<*)
theory Hilbert
  imports Main "HOL-Eisbach.Eisbach"

abbrevs   
 not="\<^bold>\<not>" and disj="\<^bold>\<or>" and conj="\<^bold>\<and>" and impl="\<^bold>\<rightarrow>" and equiv="\<^bold>\<leftrightarrow>"  
 and true="\<^bold>\<top>" and false="\<^bold>\<bottom>"
 and ob="\<^bold>\<circle>" and perm="\<^bold>P" and forb="\<^bold>F"

 and derivable="\<turnstile>"
begin
(*>*)


section \<open>Proving first theorems\<close>

subsection \<open>Hilbert Calculus for Classical Logic\<close>
text \<open>Technical remark at the beginning: In order to distinguish our connectives
from the usual logical connectives of the Isabelle/HOL system, we use @{text "\<^bold>b\<^bold>o\<^bold>l\<^bold>d"}-face written
versions of them. You may use the abbreviations at the top of the document (in the theory file)
to write things down, e.g. if you start writing "dis..." (the abbreviation is "disj"),
Isabelle should suggest the autocompletion for @{text "\<^bold>\<or>"}, etc.\<close>

typedecl \<sigma> \<comment> \<open>Introduce new type for syntactical formulae (propositions).\<close>

text \<open>
For our classical propositional language, we introduce two primitive symbols:
Implication and negation. The others can be defined in terms of these two.
\<close>
consts PLimpl :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<rightarrow>" 49) 
       PLnot :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<not>_" [52]53)

consts PLatomicProp :: "\<sigma>" 
      
definition PLdisj :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<or>" 50) where "a \<^bold>\<or> b \<equiv> \<^bold>\<not>a \<^bold>\<rightarrow> b"
definition PLconj :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<and>" 51) where "a \<^bold>\<and> b \<equiv> \<^bold>\<not>(\<^bold>\<not>a \<^bold>\<or> \<^bold>\<not>b)"
definition PLequi :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infix "\<^bold>\<leftrightarrow>" 48) where "a \<^bold>\<leftrightarrow> b \<equiv> (a \<^bold>\<rightarrow> b) \<^bold>\<and> (b \<^bold>\<rightarrow> a)"
definition PLtop :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> PLatomicProp \<^bold>\<or> \<^bold>\<not>PLatomicProp" 
definition PLbot :: "\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<^bold>\<not>\<^bold>\<top>"

text \<open>Next we define the notion of syntactical derivability and consequence: \<close>

consts derivable :: "\<sigma> \<Rightarrow> bool" ("\<turnstile> _" 40)
definition consequence :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> bool" ("_ \<turnstile> _" 40) where
"A \<turnstile> B \<equiv> \<turnstile> (A \<^bold>\<rightarrow> B)"

text \<open>We can now axiomatize the derivability relation using a Hilbert-style system:\<close>

axiomatization where
  A2:  "\<turnstile> A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)" and (* Three Hilbert-style axioms *)
  A3:  "\<turnstile> (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C))" and
  A4:  "\<turnstile> (\<^bold>\<not>A \<^bold>\<rightarrow> \<^bold>\<not>B) \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)" and 
  MP:  "\<turnstile> (A \<^bold>\<rightarrow> B) \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> B" (* One inference rule: Modus ponens *)

paragraph \<open>Proof example.\<close>
text \<open>Now we are ready to proof first simple theorems:\<close>

lemma "\<turnstile> A \<^bold>\<rightarrow> A" 
proof -
  have 1: "\<turnstile> (A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A))" by (rule A3[of _ "B \<^bold>\<rightarrow> A" "A"])
  have 2: "\<turnstile> A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)" by (rule A2[of _ "B \<^bold>\<rightarrow> A"])
  from 1 2 have 3: "\<turnstile> (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A)" by (rule MP)
  have 4: "\<turnstile> A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)" by (rule A2[of _ _])
  from 3 4 have "\<turnstile> A \<^bold>\<rightarrow> A" by (rule MP)
  then show ?thesis .
qed

text \<open>The same proof a little bit nicer with syntactic sugar:\<close>
lemma "\<turnstile> A \<^bold>\<rightarrow> A" 
proof -
  have "\<turnstile> (A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A))" by (rule A3[of _ "B \<^bold>\<rightarrow> A" "A"])
  moreover have "\<turnstile> A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)" by (rule A2[of _ "B \<^bold>\<rightarrow> A"])
  ultimately have "\<turnstile> (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A)" by (rule MP)
  moreover have "\<turnstile> A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)" by (rule A2[of _ _])
  ultimately show "\<turnstile> A \<^bold>\<rightarrow> A" by (rule MP)
qed


subsection \<open>Exercises\<close>
paragraph \<open>Exercise 2.\<close>
text \<open>Prove one of the following statements by giving an explicit proof within
the given Hilbert calculus. Please make sure that every inference step in your
proof is fine-grained and annotated with the respective calculus rule name.

Hint: Find a proof first by pen-and-paper work and then formalize it within Isabelle.\<close>

text \<open>
  \<^item> @{prop "\<turnstile> \<^bold>\<not>(F \<^bold>\<rightarrow> F) \<^bold>\<rightarrow> G"}
  \<^item> @{prop "\<turnstile> \<^bold>\<not>\<^bold>\<not>F \<^bold>\<rightarrow> F"}
\<close>

text "We will later see that many proofs can in fact be done almost automatically by Isabelle,
see e.g. the example from further above:"

lemma PL1: "\<turnstile> A \<^bold>\<rightarrow> A" using A2 A3 MP by blast
lemma PL2: "\<turnstile> \<^bold>\<not>(F \<^bold>\<rightarrow> F) \<^bold>\<rightarrow> G" by (metis A2 A3 A4 MP)
lemma PL3: "\<turnstile> \<^bold>\<not>\<^bold>\<not>F \<^bold>\<rightarrow> F" by (metis A2 A3 A4 MP)



text \<open>Also, to make things look a bit nicer, we define a compound strategy @{text "PL"}
(for "Propositional Logic") that applies an internal automated theorem prover with the
respective axioms for propositional logic (A2, A3, A4 and MP)\<close>
(*<*)
named_theorems add \<comment> \<open>Needed for technical reasons\<close>
(*>*)
method PL declares add = (metis A2 A3 A4 MP add)

text \<open>In the following, we can simply use @{text "by PL"} for proving propositional
tautologies. However, as proofs can be arbitrarily complicated, this method may fail
for difficult formulas.\<close>





section \<open>Hilbert proofs for MDL\<close>

text "We augment the language PL with the new connectives of MDL:"

consts ob :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<circle>_" [52]53) \<comment> \<open>New atomic connective for obligation\<close>

text \<open>The other new deontic logic connective can be defined as usual:\<close>

definition perm :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>P_" [52]53) where "\<^bold>P a \<equiv> \<^bold>\<not>(\<^bold>\<circle>(\<^bold>\<not>a))"
definition forbidden :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>F_" [52]53) where "\<^bold>F a \<equiv> \<^bold>\<circle>(\<^bold>\<not>a)"

text \<open>Next, we additionally augment the axiomatization of our proof system for PL
with the rules of the system D for MDL:\<close>

axiomatization where
  K:   "\<turnstile> \<^bold>\<circle>(A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (\<^bold>\<circle>A \<^bold>\<rightarrow> \<^bold>\<circle>B)" and
  D:   "\<turnstile> \<^bold>\<circle>A \<^bold>\<rightarrow> \<^bold>PA" and
  NEC: "\<turnstile> A \<Longrightarrow> \<turnstile> (\<^bold>\<circle>A)" 

subsection \<open>MDL Proof Examples\<close>

lemma "\<turnstile> \<^bold>\<circle>(p \<^bold>\<and> q) \<^bold>\<rightarrow> \<^bold>\<circle>p"
proof -
  have 1: "\<turnstile> (p \<^bold>\<and> q) \<^bold>\<rightarrow> p" by (PL add: PLconj_def PLdisj_def) 
  from 1 have 2: "\<turnstile> \<^bold>\<circle>((p \<^bold>\<and> q) \<^bold>\<rightarrow> p)" by (rule NEC)
  have 3: "\<turnstile> \<^bold>\<circle>((p \<^bold>\<and> q) \<^bold>\<rightarrow> p) \<^bold>\<rightarrow> \<^bold>\<circle>(p \<^bold>\<and> q) \<^bold>\<rightarrow> \<^bold>\<circle>p" by (rule K)
  from 3 2 show "\<turnstile> \<^bold>\<circle>(p \<^bold>\<and> q) \<^bold>\<rightarrow> \<^bold>\<circle>p" by (rule MP)
qed


text \<open>Note that, although we have the necessitation rule @{thm "NEC"} , the formula
@{term "A \<^bold>\<rightarrow> \<^bold>\<circle>A"} is not generally valid:\<close>

lemma "\<turnstile> a \<^bold>\<rightarrow> \<^bold>\<circle>a" nitpick[user_axioms,expect=genuine] oops



subsection \<open>Exercises\<close>
paragraph \<open>Exercise 2.\<close>
text \<open>Prove the following statement by giving an explicit proof within
the given Hilbert calculus. Please make sure that every inference step in your
proof is fine-grained and annotated with the respective calculus rule name. You may use
the general @{method "PL"} method for inferring propositional tautologies.

Hint: Reuse your proof from the previous exercise sheet and formalize it within Isabelle.\<close>

text \<open>
  \<^item> @{prop "\<turnstile> \<^bold>\<not>\<^bold>\<circle>\<^bold>\<bottom>"}
\<close>

(*<*)
end
(*>*)