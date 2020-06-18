theory ValueOntologyTest     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports ValueOntologyNew 
begin

(*polymorph operators for sets of worlds/values*)
abbreviation subs (infix "\<^bold>\<sqsubseteq>" 70) where "A\<^bold>\<sqsubseteq>B \<equiv> \<forall>x. A x \<longrightarrow> B x"

(*the pair of Ext/Int operators satisfies the main properties of Galois connections *)
lemma G:  "B \<^bold>\<sqsubseteq> A\<up> \<longleftrightarrow> A \<^bold>\<sqsubseteq> B\<down>" by blast

lemma G1:      "A \<^bold>\<sqsubseteq> A\<up>\<down>" by simp
lemma G2:      "B \<^bold>\<sqsubseteq> B\<down>\<up>" by simp
lemma G3:     "A\<^sub>1 \<^bold>\<sqsubseteq> A\<^sub>2 \<longrightarrow> A\<^sub>2\<up> \<^bold>\<sqsubseteq> A\<^sub>1\<up>" by simp
lemma G4:     "B\<^sub>1 \<^bold>\<sqsubseteq> B\<^sub>2 \<longrightarrow> B\<^sub>2\<down> \<^bold>\<sqsubseteq> B\<^sub>1\<down>" by simp

lemma cl1:    "A\<up> = A\<up>\<down>\<up>" by blast
lemma cl2:    "B\<down> = B\<down>\<up>\<down>" by blast
lemma dual1a: "(A\<^sub>1 \<^bold>\<squnion> A\<^sub>2)\<up> = (A\<^sub>1\<up> \<^bold>\<sqinter> A\<^sub>2\<up>)" by blast
lemma dual1b: "(B\<^sub>1 \<^bold>\<squnion> B\<^sub>2)\<down> = (B\<^sub>1\<down> \<^bold>\<sqinter> B\<^sub>2\<down>)" by blast

lemma          "(A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up> \<^bold>\<sqsubseteq> (A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>)" nitpick oops
lemma          "(B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down> \<^bold>\<sqsubseteq> (B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>)" nitpick oops
lemma dual2a: "(A\<^sub>1\<up> \<^bold>\<squnion> A\<^sub>2\<up>) \<^bold>\<sqsubseteq>  (A\<^sub>1 \<^bold>\<sqinter> A\<^sub>2)\<up>" by blast
lemma dual2b: "(B\<^sub>1\<down> \<^bold>\<squnion> B\<^sub>2\<down>) \<^bold>\<sqsubseteq>  (B\<^sub>1 \<^bold>\<sqinter> B\<^sub>2)\<down>" by blast

(* TODO fix:
lemma "\<lfloor>(\<^bold>\<not>INDIFF d) \<^bold>\<and> (\<^bold>\<not>INDIFF p) \<^bold>\<and> (\<^bold>\<not>INCONS d) \<^bold>\<and> (\<^bold>\<not>INCONS p) \<^bold>\<and>
  d\<upharpoonleft>RELI \<^bold>\<and> p\<upharpoonleft>WILL\<rfloor>"  nitpick[satisfy,max_genuine=10,show_all] oops

(*exploring implied knowledge*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>GAIN\<oplus>EFFI\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  nitpick oops (*two noq \<oplus>: consistent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>EFFI\<oplus>RELI] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  by simp (*three quadrants \<oplus>: inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>[RESP\<oplus>STAB] \<^bold>\<rightarrow> INCONS x\<rfloor>" 
  by simp (*two opposed quadrants \<oplus> (oq): inconsistent*)
lemma "\<lfloor>x\<upharpoonleft>EQUI \<^bold>\<and> y\<upharpoonleft>EFFI \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two noq (different parties): consistent*)
lemma "\<lfloor>x\<upharpoonleft>RESP \<^bold>\<and> y\<upharpoonleft>STAB \<^bold>\<rightarrow> (INCONS x \<^bold>\<or> INCONS y)\<rfloor>" 
  nitpick oops (*two oq (different parties): consistent*)

(*Important: only \<^bold>\<preceq>\<^sub>A\<^sub>A is suitable for logic of value aggregation*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[WILL\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>[RELI\<oplus>STAB]\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>WILL \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>STAB\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>[RELI\<oplus>STAB] \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor>" by blast
lemma "\<lfloor>x\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>[WILL\<oplus>STAB] \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>x\<upharpoonleft>STAB \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor> \<longrightarrow> \<lfloor>x\<upharpoonleft>[RELI\<oplus>STAB] \<^bold>\<preceq>\<^sub>A\<^sub>A x\<upharpoonleft>WILL\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
*)

end

