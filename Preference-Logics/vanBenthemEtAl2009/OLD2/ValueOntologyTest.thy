theory ValueOntologyTest     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports ValueOntologyNew 
begin

(*exploring the consistency and models of the ontology*)
lemma "True" nitpick[satisfy,show_all,card i=1] oops
lemma "True" nitpick[satisfy,show_all,card i=10] oops

lemma "\<lfloor>INCONS\<^sup>p\<rfloor>" nitpick[satisfy,card i=4] nitpick oops (*contingent*)
lemma "\<lfloor>INDIFF\<^sup>p\<rfloor>" nitpick[satisfy,card i=4] nitpick oops (*contingent*)

(****the pair of Ext/Int operators satisfies the main properties of Galois connections ****)
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

(***** test notation **)
lemma "(let y = x\<inverse> in WILL\<^sup>y) = WILL\<^sup>x\<inverse>" by meson
(*both notations do the same. TODO: do we want to do away with rhs?*)
lemma "\<lfloor>[WILL\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor> \<equiv> \<lfloor>(WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x)\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp

(********* value ontology tests *****************)
lemma "SECU\<^sup>x \<^bold>\<sqsubseteq> RELI\<^sup>x" by simp
lemma "RELI\<^sup>x\<down> \<^bold>\<sqsubseteq> SECU\<^sup>x\<down>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> SECU\<^sup>x\<down>\<rfloor>" by simp
lemma "EQUA\<^sup>x \<^bold>\<sqsubseteq> RELI\<^sup>x" by simp
lemma "RELI\<^sup>x\<down> \<^bold>\<sqsubseteq> EQUA\<^sup>x\<down>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> EQUA\<^sup>x\<down>\<rfloor>" by simp
lemma "\<lfloor>RELI\<^sup>x\<down> \<^bold>\<rightarrow> (SECU\<^sup>x\<down> \<^bold>\<and> EQUA\<^sup>x\<down>)\<rfloor>" by simp

lemma "\<lfloor>RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down> \<^bold>\<rightarrow> INCONS\<^sup>p\<rfloor>" by simp 
lemma "\<lfloor>INCONS\<^sup>p \<^bold>\<rightarrow> RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" by simp 

lemma "\<lfloor>RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>FAIR\<^sup>d\<down> \<^bold>\<and> EFFI\<^sup>d\<down>\<rfloor>" nitpick[satisfy] nitpick oops (*contingent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [FAIR\<^sup>d] \<^bold>\<and> [EFFI\<^sup>d]\<rfloor>"
   nitpick[satisfy,show_all] nitpick oops (*contingent: p & d are independent*)
lemma "\<lfloor>(\<^bold>\<not>INCONS\<^sup>d) \<^bold>\<and> (\<^bold>\<not>INCONS\<^sup>p) \<^bold>\<and> [RELI\<^sup>d] \<^bold>\<and> [WILL\<^sup>p]\<rfloor>" 
  nitpick[satisfy,show_all] nitpick oops (*contingent: p & d are independent*)

(*more tests*)
lemma "\<lfloor>[WILL\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*two non-opposed quadrants \<oplus> (noq): consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*two non-opposed quadrants \<and> (noq): consistent*)

lemma "\<lfloor>[WILL\<^sup>x\<oplus>GAIN\<^sup>X\<oplus>EFFI\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*two noq \<oplus>: consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> GAIN\<^sup>X\<down> \<^bold>\<and> EFFI\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*two noq \<and>: consistent*)

lemma "\<lfloor>[WILL\<^sup>x\<oplus>EFFI\<^sup>x\<oplus>RELI\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*three quadrants \<oplus>: consistent*)
lemma "\<lfloor>WILL\<^sup>x\<down> \<^bold>\<and> EFFI\<^sup>x\<down> \<^bold>\<and> RELI\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp (*three quadrants \<and>: inconsistent*)

lemma "\<lfloor>[RESP\<^sup>x\<oplus>STAB\<^sup>x] \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" nitpick oops (*two opposed quadrants \<oplus> (oq): consistent*)
lemma "\<lfloor>RESP\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>x\<down> \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by simp (*two opposed quadrants \<and> (oq): inconsistent*)

lemma "\<lfloor>[EQUI\<^sup>x\<oplus>EFFI\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*two noq (different parties) \<oplus>: consistent*)
lemma "\<lfloor>EQUI\<^sup>x\<down> \<^bold>\<and> EFFI\<^sup>y\<down> \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*two noq (different parties) \<and>: consistent*)

lemma "\<lfloor>[RESP\<^sup>x\<oplus>STAB\<^sup>y] \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*two oq (different parties) \<oplus>: consistent*)
lemma "\<lfloor>RESP\<^sup>x\<down> \<^bold>\<and> STAB\<^sup>y\<down> \<^bold>\<rightarrow> (INCONS\<^sup>x \<^bold>\<or> INCONS\<^sup>y)\<rfloor>" nitpick oops (*two oq (different parties) \<and>: consistent*)

(* value preferences tests*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>" by blast
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor>" by blast
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x \<^bold>\<prec>\<^sub>v STAB\<^sup>x\<rfloor>"
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<not>\<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" using rBR by auto
lemma "\<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" by auto
lemma "\<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" by auto
lemma "\<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>WILL\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)
lemma "\<lfloor>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor> \<longrightarrow> \<lfloor>RELI\<^sup>x\<^bold>\<oplus>STAB\<^sup>x \<^bold>\<prec>\<^sub>v WILL\<^sup>x\<rfloor>" 
  nitpick nitpick[satisfy] oops (*contingent*)

end

