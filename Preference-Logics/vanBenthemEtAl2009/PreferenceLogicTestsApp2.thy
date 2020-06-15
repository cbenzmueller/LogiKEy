theory PreferenceLogicTestsApp2                (*Benzmüller & Fuenmayor, 2020*)  
   imports PreferenceLogicBasics 
begin

(*****Application-specific tests for the value ontology****)
(* EE variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>E\<^sub>E (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>E\<^sub>E (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>E\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>E\<^sub>E B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(* EE variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>E\<^sub>E (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>E\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>E\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>E\<^sub>E B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>E\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast
(* total EE variant (\<and>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>E\<^sub>E (A\<^bold>\<and>B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<and>B) \<preceq>\<^sub>E\<^sub>E A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>E\<^sub>E (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>E\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>E\<^sub>E B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<and>B) \<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast
(* total EE variant (\<or>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>E\<^sub>E (A\<^bold>\<or>B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<or>B) \<preceq>\<^sub>E\<^sub>E A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>E\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>E\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>E\<^sub>E B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<or>B) \<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<preceq>\<^sub>E\<^sub>E A)\<rfloor>" by blast

(* AE variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>A\<^sub>E (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A\<rfloor>" using rBR by blast (*change wrt. strict*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>E (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>E B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>A\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast
(* AE variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>A\<^sub>E (A\<^bold>\<or>B)\<rfloor>" using rBR by blast (*change wrt. strict*)
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>E B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(* total AE variant (\<and>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>A\<^sub>E (A\<^bold>\<and>B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>E A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>E (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>E B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast
(* total AE variant (\<or>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>A\<^sub>E (A\<^bold>\<or>B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>E A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>E B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>E A)\<rfloor>" by blast

(* AA variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent - change wrt. strict*)
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by simp (*change wrt. strict*)
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent - change wrt. strict*)
(*--------------------------------------------------*)
lemma "\<lfloor>A \<preceq>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast
(* AA variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<preceq>\<^sub>A\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<preceq>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<preceq>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent - change wrt. strict*)
lemma "\<lfloor>(B \<^bold>\<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by simp (*change wrt. strict*)
(*---------------------------------------------------*)
lemma "\<lfloor>A \<preceq>\<^sub>A\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(B \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
(* total AA variant (\<and>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" by blast 
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast
(* total AA variant (\<or>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<preceq>\<^sub>A\<^sub>A (A\<^bold>\<or>B)\<rfloor>" by blast 
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<preceq>\<^sub>A\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<preceq>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<preceq>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<preceq>\<^sub>A\<^sub>A A)\<rfloor>" by blast

(* EA variant (\<and>)*)
lemma "\<not>\<lfloor>(A\<^bold>\<and>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent - change wrt. strict*)
lemma "\<lfloor>A \<^bold>\<succeq>\<^sub>E\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<succeq>\<^sub>E\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<^bold>\<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
(*--------------------------------------------*)
lemma "\<lfloor>(A\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>A \<succeq>\<^sub>E\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
(* EA variant (\<or>)*)
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<not>\<lfloor>A \<^bold>\<succeq>\<^sub>E\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent - change wrt. strict*) 
lemma "\<lfloor>(B \<^bold>\<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<succeq>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<^bold>\<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<succeq>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
(*------------------------------------------------*)
lemma "\<lfloor>(A\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>A \<succeq>\<^sub>E\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(B \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>((C\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>(A \<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
(* total EA variant (\<and>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A\<rfloor>" by blast 
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<succeq>\<^sub>E\<^sub>A (A\<^bold>\<and>B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<and>B) \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
(* total EA variant (\<or>)*)
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>A \<succeq>\<^sub>E\<^sub>A (A\<^bold>\<or>B)\<rfloor>" by blast 
lemma "is_total SBR \<Longrightarrow> \<lfloor>(B \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>((C\<^bold>\<or>B) \<succeq>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<succeq>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "is_total SBR \<Longrightarrow> \<lfloor>(A \<succeq>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<succeq>\<^sub>E\<^sub>A (C\<^bold>\<or>B))\<rfloor>" by blast
end

