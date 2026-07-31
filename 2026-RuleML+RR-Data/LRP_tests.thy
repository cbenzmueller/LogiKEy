(* 
Luca Pasetto, Christoph Benzmüller, and Réka Markovich. 2026.
Right on Thought, Left Private: Reasoning about Mental Privacy in LogiKEy.
*)

section \<open>Tests on Right to Privacy in HOL\<close>

text \<open>\<close>

theory LRP_tests imports LRP begin
nitpick_params[user_axioms=true,assms=true,expect=genuine]

(* agents *)
consts a::ag b::ag c::ag s::ag

(* 5.1 Right to be left alone: the right to control who has access *)
(* (3) *)
  term "(\<^bold>O[s\<rightarrow>a](\<^bold>E s (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>K b \<phi>))))))"
  term "\<forall>a b. ((a\<noteq>b \<and> s\<noteq>a \<and> s\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>O[s\<rightarrow>a](\<^bold>E s (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>K b \<phi>))))))\<rfloor> )"
lemma "\<forall>a b. ((a\<noteq>b \<and> s\<noteq>a \<and> s\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>O[s\<rightarrow>a](\<^bold>E s (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>K b \<phi>))))))\<rfloor> )"
  (* nitpick[satisfy, eval="ag_n",  card ag=3] *)
  nitpick[satisfy] nitpick
  oops

(* (5) *)
  term "\<forall>a b. ((a\<noteq>b \<and> s\<noteq>a \<and> s\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>O[s\<rightarrow>a](\<^bold>E s (\<^bold>O[c\<rightarrow>a](\<^bold>E c (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>K b \<phi>))))))))\<rfloor> )"
lemma "\<forall>a b. ((a\<noteq>b \<and> s\<noteq>a \<and> s\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>O[s\<rightarrow>a](\<^bold>E s (\<^bold>O[c\<rightarrow>a](\<^bold>E c (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>K b \<phi>))))))))\<rfloor> )"
  nitpick[satisfy] nitpick
  oops

(* (6) *)
  term "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>O[c\<rightarrow>a](\<^bold>\<not>\<^bold>E c (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>\<not>\<^bold>E a (\<^bold>K b \<phi>)))))\<rfloor> )"
lemma "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>O[c\<rightarrow>a](\<^bold>\<not>\<^bold>E c (\<^bold>\<not>\<^bold>\<diamond> (\<^bold>\<not>\<^bold>E a (\<^bold>K b \<phi>)))))\<rfloor> )"
   nitpick[satisfy] nitpick 
  oops

(* (7) *)
  term "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b \<phi>)))\<rfloor> )"
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>K b \<phi>)))\<rfloor> )"
  nitpick[satisfy,eval="ag_k"] nitpick
  oops

(* (8) *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>\<diamond>(\<^bold>K b \<phi>))))\<rfloor> )"
  nitpick[satisfy,card ag=2, card i=2] nitpick
  oops

(* (9) *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<not>\<^bold>\<diamond>(\<^bold>E b (\<^bold>O[a\<rightarrow>b](\<^bold>E a (\<^bold>\<diamond>(\<^bold>K b \<phi>))))))\<rfloor> )"
  nitpick[satisfy,eval="ag_k"] nitpick
  oops

(* (10) *)
  term "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> \<^bold>E b (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>\<diamond> (\<^bold>K c \<phi>)))))) )\<rfloor> )"
lemma "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> \<^bold>E b (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>\<diamond> (\<^bold>K c \<phi>)))))) )\<rfloor> )"
   nitpick[satisfy] nitpick 
  oops

(* (11) *)
lemma "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>\<diamond> (\<^bold>K c \<phi>)))))) )\<rfloor> )"
   nitpick[satisfy] nitpick 
  oops

(* premise of (10) implies premise of (11) *)
lemma prem10:"\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> \<lfloor>(  (\<^bold>\<box>\<^bold>\<diamond> \<^bold>E b (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<diamond> (\<^bold>K b \<phi>))  )\<rfloor> )"
  unfolding LRP_Defs apply simp 
  using Reflexive_n by blast

(* then (11) implies (10) *)
lemma "\<forall>b c. ((a\<noteq>b \<and> a\<noteq>c) \<longrightarrow>
                     (\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>\<diamond> (\<^bold>K c \<phi>)))))) \<Turnstile>
                     (\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> \<^bold>E b (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>\<diamond> (\<^bold>K c \<phi>)))))) ) ))"
  using Reflexive_n mbox_def mimp_def mstit_def mneg_def by fastforce

(* (12) *)
lemma "\<forall>b. ((a\<noteq>b) \<longrightarrow> \<lfloor>(\<^bold>\<box> ((\<^bold>\<box>\<^bold>\<diamond> (\<^bold>K b \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<diamond> \<^bold>E a (\<^bold>O[b\<rightarrow>a] (\<^bold>\<not>\<^bold>E b (\<^bold>K a \<phi>))))) )\<rfloor> )"
   nitpick[satisfy] nitpick 
  oops


(* 5.2 Right to transparency *)
(* (13) *)
lemma "\<forall>b. ( (a\<noteq>b \<and> a\<noteq>c) \<longrightarrow> 
        \<lfloor>(\<^bold>O[c\<rightarrow>a] ((\<^bold>E c (\<^bold>K a (\<^bold>\<diamond> (\<^bold>K b \<phi>)))) \<^bold>\<or> \<^bold>E c (\<^bold>K a \<^bold>\<not>(\<^bold>\<diamond> (\<^bold>K b \<phi>))) ) )\<rfloor> )"
   nitpick[satisfy] nitpick 
  oops

(* 5.3 Protection: possibility of enforcement *)
(* (14): power *)
lemma "\<forall>b. ( (a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>j) \<longrightarrow> 
        \<lfloor>\<^bold>\<box>((\<^bold>\<not>\<^bold>E c (\<^bold>\<diamond> \<^bold>E a (\<^bold>\<not>\<^bold>\<diamond>(\<^bold>K b \<phi>) ))) \<^bold>\<rightarrow> \<^bold>O[j\<rightarrow>a] (\<^bold>E j (\<^bold>E c (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not>\<^bold>\<diamond>(\<^bold>K b \<phi>))))) ) )\<rfloor> )"
  nitpick[satisfy, eval="ag_o"] nitpick 
  oops


end

