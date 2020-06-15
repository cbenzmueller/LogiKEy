theory PreferenceLogicTests1                (*Benzmüller & Fuenmayor, 2020*)  
   imports PreferenceLogicBasics 
begin (*Tests for the SSE of van Benthem, Girard and Roy, JPL 2009, in HOL*)
(*Fact 1: definability of the four principal operators and verification*)
lemma Fact1_9:  "(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) u" by smt
lemma Fact1_10: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>) u" by smt
lemma Fact1_11: "(\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>E\<^sub>E \<psi>) u" by smt
lemma Fact1_12: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>E \<psi>) u" by smt
(*Fact 2: definability of remaining preference operators and verification*)
lemma Fact2_13: "is_total SBR \<longrightarrow> ((\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u)"  by smt
lemma Fact2_14: "is_total SBR \<longrightarrow> ((\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u)"  by smt
lemma Fact2_15: "is_total SBR \<longrightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u)"  by smt
lemma Fact2_16: "is_total SBR \<longrightarrow> ((\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u)"  by smt
(*Section 3.5 "Axiomatization" -- verify interaction axioms*)
lemma Inclusion_1:   "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<preceq>\<phi>)\<rfloor>"      by auto
lemma Interaction_1: "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>"   using transBR by blast
lemma Trans_le:      "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>"   using transBR by blast 
lemma Interaction_2: "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow>  ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor>" by blast
lemma Fact4:         "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor> \<longleftrightarrow> 
                       (\<forall>w. \<forall>v. (((w \<preceq> v) \<and> \<not>(v \<preceq> w)) \<longrightarrow> (w \<prec> v)))" by smt
lemma Interaction_3:   "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>" using transBR by blast
lemma Inclusion_2:     "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>E\<phi>)\<rfloor>"      by blast
(*Section 3.6 "A binary preference fragment"*)
(* \<^bold>\<preceq>\<^sub>E\<^sub>E is the dual of \<^bold>\<prec>\<^sub>A\<^sub>A *)
lemma "\<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor> \<and> \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>"  by simp
(* \<preceq>\<^sub>E\<^sub>E is the dual of \<prec>\<^sub>A\<^sub>A only if totality is assumed*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>"  nitpick oops (*countermodel*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>"  by blast (* only this direction holds*)
lemma "is_total SBR \<longrightarrow> \<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>"  by blast
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>"  nitpick oops (*countermodel*)
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>"  by blast (* only this direction holds*)
lemma "is_total SBR \<longrightarrow> \<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>"  by blast
(* verify p.97-98 *)
lemma monotonicity:  "\<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<^bold>A(\<phi>\<^bold>\<rightarrow>\<xi>)) \<^bold>\<rightarrow> (\<xi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<rfloor>" by blast
lemma reducibility:  
         "\<lfloor>(((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<alpha>) \<preceq>\<^sub>E\<^sub>E \<beta>) \<^bold>\<leftrightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> (\<alpha> \<preceq>\<^sub>E\<^sub>E \<beta>))\<rfloor>" by blast
lemma reflexivity:   "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" using reflBR by blast
(*The condition below is supposed to enforce totality of the preference 
   relation. However there are countermodels. See p.98?*)
lemma "is_total SBR \<longrightarrow> 
       \<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<^bold>\<and>(\<psi> \<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<^bold>\<or>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>"  by auto
lemma "\<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>
       \<longrightarrow> is_total SBR" nitpick oops (*countermodel -- error in paper?*)
lemma "is_total SBR \<longrightarrow> 
       \<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>" by auto
lemma "\<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>
       \<longrightarrow> is_total SBR" nitpick oops (*countermodel -- error in paper?*)
(*Application-specific tests for the value ontology*)
lemma "\<lfloor>A \<prec>\<^sub>A\<^sub>E (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>E (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*ctngt*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>E B)\<rfloor>" by blast
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*ctngt*)
lemma "\<lfloor>A \<prec>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*ctngt*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<prec>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" by blast 
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>A A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A B)\<rfloor>" by blast
end

