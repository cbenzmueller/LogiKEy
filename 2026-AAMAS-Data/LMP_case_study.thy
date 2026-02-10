section \<open>Right to Mental Privacy in HOL: Case Study\<close>

theory LMP_case_study
  imports LMP
begin

nitpick_params[user_axioms=true,assms=true,expect=genuine,show_all,format=2,mono=false,dont_box]

consts a :: ag  c :: ag
consts p :: \<sigma>   q :: \<sigma>   r :: \<sigma>
consts w0 :: i  w1 :: i  w2 :: i 

abbreviation (input) assumption_diff_ags where
  "assumption_diff_ags \<equiv> a \<noteq> c"

abbreviation (input) assumption_diff_worlds where
   "assumption_diff_worlds \<equiv> w0 \<noteq> w1 \<and> w0 \<noteq> w2 \<and> w1 \<noteq> w2" 

(* propositional valuation *)
abbreviation (input) assumption_lits where
  "assumption_lits \<equiv>
     (p w0 \<and> p w1) \<and>
     (\<not> q w0 \<and> q w1) \<and>
     (\<not> r w0 \<and> \<not> r w1)"

(* --- Belief assumptions  --- *)
abbreviation (input) assumption_B where
  "assumption_B \<equiv>
     \<lfloor>\<^bold>B a \<^sup>Ap\<rfloor>w0 \<and>
     \<lfloor>(<\<^bold>B a> \<^sup>Aq) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<^sup>Aq)\<rfloor>w0 \<and>
     \<lfloor>(<\<^bold>B a> \<^sup>Ar) \<^bold>\<and> (<\<^bold>B a> \<^bold>\<not>\<^sup>Ar)\<rfloor>w0 \<and>
     \<lfloor>\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar)\<rfloor>w0 \<and>
     \<lfloor>\<^bold>B a \<^sup>Ap\<rfloor>w1 \<and>
     \<lfloor>\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar)\<rfloor>w1"

(* --- Knowledge assumptions  --- *)
(* no knowledge at w0 *)
abbreviation (input) assumption_K where
  "assumption_K \<equiv>
     \<lfloor> \<^bold>\<not> (\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<rfloor>w0 \<and>
     \<lfloor> \<^bold>\<not> (\<^bold>K c (\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar))) \<rfloor>w0 \<and>
     \<lfloor>      (\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<rfloor>w1 \<and>
     \<lfloor>      (\<^bold>K c (\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar))) \<rfloor>w1"

abbreviation (input) can_prevent_KB :: "ag \<Rightarrow> ag \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" where
  "can_prevent_KB a1 a2 \<phi> w \<equiv> \<lfloor> \<^bold>\<diamond> (\<^bold>E a1 (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K a2 (\<^bold>B a \<phi>))))) \<rfloor>w"

lemma "assumption_K \<longrightarrow> \<not>can_prevent_KB a c (\<^sup>Ap) w1"
  by (metis AxiomS5_box Reflexive_n mbox_def mneg_def mstit_def symmetric_def)

lemma "assumption_K \<longrightarrow> \<not>can_prevent_KB a c ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar) w1" 
  by (metis AxiomS5_box Reflexive_n mbox_def mneg_def mstit_def symmetric_def)

lemma "( \<lfloor> (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K c (\<^bold>B a \<phi>))))))) \<^bold>\<rightarrow> (\<^bold>K c (\<^bold>B a \<phi>))  \<rfloor>w1)" nitpick
  oops

lemma "( \<lfloor>  (\<^bold>K c (\<^bold>B a \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K c (\<^bold>B a \<phi>)))))))  \<rfloor>w1)" 
  by (metis (full_types) AxiomS5_box Reflexive_n mbox_def mimp_def mneg_def mstit_def symmetric_def)

(* protecting mental privacy implies that others do not know *)
lemma "( \<forall>\<phi>. \<lfloor> ((\<^bold>\<diamond> (\<^bold>E a (\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>K c (\<^bold>B a \<phi>))))))) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>K c (\<^bold>B a \<phi>))  \<rfloor>w1)" 
  unfolding LMP_Defs
  apply simp
  by (smt (verit) AxiomS5_box Reflexive_n symmetric_def)

(* --- Mental privacy leak (Alice cannot ensure non-access) --- *)
abbreviation (input) mp_leak_w1 where
  "mp_leak_w1 \<equiv> (\<not>can_prevent_KB a c (\<^sup>Ap) w1) \<or> (\<not>can_prevent_KB a c ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar) w1)"

abbreviation (input) mp_leak_w0 where
  "mp_leak_w0 \<equiv> (\<not>can_prevent_KB a c (\<^sup>Ap) w0) \<or> (\<not>can_prevent_KB a c ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar) w0)"

(* set of assumptions is consistent *)
lemma "assumption_diff_ags \<and> assumption_diff_worlds \<and>
       assumption_lits \<and>
       assumption_B \<and> assumption_K"
  nitpick[satisfy]
  oops

(* w1 Mental privacy leak *)
lemma "assumption_diff_ags \<and> assumption_diff_worlds \<and>
       assumption_lits \<and>
       assumption_B \<and> assumption_K \<longrightarrow>
       mp_leak_w1"   
  by (metis AxiomS5_box Reflexive_n mbox_def mneg_def mstit_def symmetric_def)

(* w0 no Mental privacy leak *)
lemma "assumption_diff_ags \<and> assumption_diff_worlds \<and>
       assumption_lits \<and>
       assumption_B \<and> assumption_K \<longrightarrow>
       mp_leak_w0"
   nitpick 
(* Nitpick found a counterexample *)
   oops

(* --- Freedom of Thought assumption on r (obligation + fulfillment) --- *)
abbreviation (input) assumption_fot where
  "assumption_fot \<equiv>
     \<lfloor> \<^bold>O[c\<rightarrow>a](
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a r)) \<^bold>\<and>
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>r))) \<^bold>\<and>
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> r) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>r))) )
        ) \<rfloor>
     \<and>
     \<lfloor> (
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a r)) \<^bold>\<and>
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>r))) \<^bold>\<and>
          (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> r) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>r))) )
        ) \<rfloor>"

(* Freedom of Thought is not violated on r *)
lemma "assumption_fot \<longrightarrow>  ((\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>r))) \<^bold>\<and> (\<^bold>\<not> \<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> r) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>r))))) w1" 
  by (simp add: mand_def)

(* indirect violation of fot on q depends on mp_leak_w1 *)
abbreviation (input) assumption_knowledge_enables_influence where
  "assumption_knowledge_enables_influence \<equiv>
     \<lfloor> ((\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<^bold>\<and> (\<^bold>K c (\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar))))
         \<^bold>\<rightarrow> ( (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>q))) \<^bold>\<and> (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> q) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>q))))) \<rfloor>w0 \<and>
     \<lfloor> ((\<^bold>K c (\<^bold>B a \<^sup>Ap)) \<^bold>\<and> (\<^bold>K c (\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar))))
         \<^bold>\<rightarrow> ( (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>q))) \<^bold>\<and> (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> q) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>q))))) \<rfloor>w1"

abbreviation (input) influence_w1 where
  "influence_w1 \<equiv> \<lfloor> ( (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>\<^sup>Aq))) \<^bold>\<and> (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> \<^sup>Aq) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>\<^sup>Aq))))) \<rfloor>w1"

(* complete set of assumptions *)
abbreviation (input) model_assumptions where
  "model_assumptions \<equiv>
     assumption_diff_ags \<and> assumption_diff_worlds \<and>
     assumption_lits \<and>
     assumption_B \<and> assumption_K \<and> assumption_fot \<and>
     assumption_knowledge_enables_influence"

(* set of assumptions is consistent *)
lemma model_assumptions
    nitpick[satisfy]  
    oops

(* Freedom of Thought would be violated, if q were protected *)
lemma "model_assumptions \<longrightarrow> 
         influence_w1"  
  unfolding LMP_Defs
  by blast

(* --- No influence at w0 --- *)
abbreviation (input) no_influence_w0 where
  "no_influence_w0 \<equiv> \<lfloor> \<^bold>\<not>( (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>(\<^bold>B a (\<^bold>\<not>\<^sup>Aq))) \<^bold>\<and> (\<^bold>E c \<^bold>\<not>\<^bold>\<diamond>((<\<^bold>B a> \<^sup>Aq) \<^bold>\<and> (<\<^bold>B a> (\<^bold>\<not>\<^sup>Aq))))) \<rfloor>w0"

lemma "model_assumptions \<longrightarrow> 
         no_influence_w0"
  unfolding LMP_Defs 
  apply simp
  by (smt (verit) AxiomS5_box Reflexive_n reflexive_def)

lemma "influence_w1 \<longrightarrow> \<lfloor> \<^bold>\<box>(\<^bold>B a \<^sup>Aq) \<rfloor>w1" 
  unfolding LMP_Defs 
  using Reflexive_n by blast

lemma "influence_w1 \<longrightarrow> \<lfloor> (\<^bold>B a \<^sup>Aq) \<rfloor>w1" 
  by (metis AxiomS5_box Reflexive_n mand_def matom_def mbel_def mbox_def mneg_def mstit_def reflexive_def)

(* --- Belief-closure: derive Ba r from Ba p, Ba q, and Ba(p\<and>q\<rightarrow>r). *)
lemma belief_closure:"\<lfloor> ((\<^bold>B a \<^sup>Ap) \<^bold>\<and> (\<^bold>B a \<^sup>Aq) \<^bold>\<and> (\<^bold>B a ((\<^sup>Ap \<^bold>\<and> \<^sup>Aq) \<^bold>\<rightarrow> \<^sup>Ar))) \<^bold>\<rightarrow> (\<^bold>B a \<^sup>Ar) \<rfloor>w1"
  by (simp add: mand_def mbel_def mimp_def)

lemma "model_assumptions \<longrightarrow> 
         \<lfloor> (\<^bold>B a \<^sup>Ar) \<rfloor>w1"
  unfolding LMP_Defs
  apply simp 
  by (smt (verit) AxiomS5_box Reflexive_n reflexive_def) 

(* get a nice model *)
(*
abbreviation (input) extra_assumptions where
  "extra_assumptions \<equiv>
     (\<forall>x y. (ag_b c x y \<longleftrightarrow> x=y) \<and> (ag_k c x y \<longleftrightarrow> x=y) \<and> ag_k a x y
        \<and> (\<forall>a1 a2. ag_o a1 a2 x y \<longleftrightarrow> y=w2)) \<and>
     (\<forall>a1 a2 a3 a4. ag_o a1 a2 = ag_o a3 a4) \<and> (p w2 \<and> q w2 \<and> r w2)"
*)
abbreviation (input) extra_assumptions where
  "extra_assumptions \<equiv>
     (\<forall>x y. (ag_b c x y \<longleftrightarrow> x=y) \<and> ag_k a x y
        \<and> (\<forall>a1 a2. ag_o a1 a2 x y \<longleftrightarrow> y=w2)) \<and>
     (\<forall>a1 a2 a3 a4. ag_o a1 a2 = ag_o a3 a4) \<and> (p w2 \<and> q w2 \<and> r w2)"
 
  lemma "model_assumptions \<and> extra_assumptions"  
  unfolding LMP_Defs
  apply simp
  nitpick[satisfy, card ag = 2, card i = 4]
  (* nitpick[satisfy, card ag = 7, card i = 7] *)
  oops

(* model needs at least 4 worlds *)

end
