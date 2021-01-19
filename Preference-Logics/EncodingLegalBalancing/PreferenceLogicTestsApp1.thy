theory PreferenceLogicTestsApp1     (*** Benzmüller & Fuenmayor, 2021 ***)  
   imports PreferenceLogicBasics 
begin (*****Application-specific tests for the value ontology****)
(* EE variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>E\<^sub>E (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>E (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>E B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>E\<^sub>E A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(* EE variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>E\<^sub>E (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>E B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>E\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>E\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>E A)\<rfloor>" by blast
(* AE variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>A\<^sub>E (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>E (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>E (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>E B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>A\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>E A)\<rfloor>" by blast
(* AE variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>A\<^sub>E (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>E A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>E B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>E (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>E (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>E B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>A\<^sub>E A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>A\<^sub>E A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>E A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(* AA variant (\<and>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>A\<^sub>A A)\<rfloor>" by blast
(*--------------------------------------------------*)
lemma "\<lfloor>A \<prec>\<^sub>A\<^sub>A (A\<^bold>\<and>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<prec>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<prec>\<^sub>A\<^sub>A A)\<rfloor>" by blast
(* AA variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>A\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>A\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>A\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(*---------------------------------------------------*)
lemma "\<lfloor>A \<prec>\<^sub>A\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A\<^bold>\<or>B) \<prec>\<^sub>A\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<or>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>A\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>A\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<or>B) \<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> (B \<prec>\<^sub>A\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(B \<prec>\<^sub>A\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<prec>\<^sub>A\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)

(* EA variant (\<and>)*)
lemma "\<not>\<lfloor>A \<^bold>\<prec>\<^sub>E\<^sub>A (A\<^bold>\<and>B)\<rfloor>" using rBR by blast 
lemma "\<lfloor>(A\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>A (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<^bold>\<prec>\<^sub>E\<^sub>A A)\<rfloor>" by blast
(*--------------------------------------------*)
lemma "\<not>\<lfloor>A \<prec>\<^sub>E\<^sub>A (A\<^bold>\<and>B)\<rfloor>" using rBR SBR_def by blast
lemma "\<lfloor>(A\<^bold>\<and>B) \<prec>\<^sub>E\<^sub>A A\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*) 
lemma "\<lfloor>(A \<prec>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>E\<^sub>A (C\<^bold>\<and>B))\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(A \<prec>\<^sub>E\<^sub>A (C\<^bold>\<and>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>E\<^sub>A B)\<rfloor>" by blast
lemma "\<lfloor>((C\<^bold>\<and>B) \<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<prec>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(B \<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<and>B) \<prec>\<^sub>E\<^sub>A A)\<rfloor>" by blast
(* EA variant (\<or>)*)
lemma "\<lfloor>A \<^bold>\<prec>\<^sub>E\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<not>\<lfloor>(A\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>A A\<rfloor>" using rBR by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>A (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<^bold>\<prec>\<^sub>E\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<^bold>\<prec>\<^sub>E\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<^bold>\<prec>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(B \<^bold>\<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<^bold>\<prec>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
(*------------------------------------------------*)
lemma "\<lfloor>A \<prec>\<^sub>E\<^sub>A (A\<^bold>\<or>B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<not>\<lfloor>(A\<^bold>\<or>B) \<prec>\<^sub>E\<^sub>A A\<rfloor>" using SBR_def by blast 
lemma "\<lfloor>(A \<prec>\<^sub>E\<^sub>A B) \<^bold>\<rightarrow> (A \<prec>\<^sub>E\<^sub>A (C\<^bold>\<or>B))\<rfloor>" by blast
lemma "\<lfloor>(A \<prec>\<^sub>E\<^sub>A (C\<^bold>\<or>B)) \<^bold>\<rightarrow> (A \<prec>\<^sub>E\<^sub>A B)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>((C\<^bold>\<or>B) \<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> (B \<prec>\<^sub>E\<^sub>A A)\<rfloor>" by blast
lemma "\<lfloor>(B \<prec>\<^sub>E\<^sub>A A) \<^bold>\<rightarrow> ((C\<^bold>\<or>B) \<prec>\<^sub>E\<^sub>A A)\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
end
