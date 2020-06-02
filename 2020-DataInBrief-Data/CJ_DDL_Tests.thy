theory CJ_DDL_Tests imports CJ_DDL           (* Christoph Benzmüller, Ali Farjami, Xavier Parent, 2020  *)
begin (* Some Tests on the Meta-Theory of DDL*)
lemma True nitpick [satisfy,user_axioms,expect=genuine] oops  (* Consistency confirmed by Nitpick *)  
 
lemma MP: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma Nec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>A\<rfloor>" by simp
lemma Neca: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>"  by simp
lemma Necp: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>p A\<rfloor>"  by simp

(* "\<^bold>\<box>" is an S5 modality *)
lemma C_1_refl: "\<lfloor>\<^bold>\<box>A \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma C_1_trans: "\<lfloor>\<^bold>\<box>A \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<box>A))\<rfloor>"  by simp
lemma C_1_sym: "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<diamond>A))\<rfloor>"  by simp

(* "\<^bold>\<box>\<^sub>p" is an KT modality *)
lemma C_9_p_refl: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> A\<rfloor>"  by (simp add: ax_4b)
lemma "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>p(\<^bold>\<box>\<^sub>pA))\<rfloor>" nitpick [user_axioms] oops (* countermodel *)
lemma "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>p(\<^bold>\<diamond>\<^sub>pA))\<rfloor>"   nitpick [user_axioms] oops (* countermodel *)

(* "\<^bold>\<box>\<^sub>a" is an KD modality *)
lemma C_10_a_serial: "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sub>aA\<rfloor>"  by (simp add: ax_3a) 
lemma "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> A\<rfloor>" nitpick [user_axioms] oops (* countermodel *)
lemma "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>a(\<^bold>\<box>\<^sub>aA))\<rfloor>" nitpick [user_axioms] oops (* countermodel *)
lemma "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>a(\<^bold>\<diamond>\<^sub>aA))\<rfloor>" nitpick [user_axioms] oops (* countermodel *)

(* Relationship between "\<^bold>\<box>,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_11: "\<lfloor>\<^bold>\<box>A \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>pA\<rfloor>" sledgehammer by simp 
lemma C_12: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aA\<rfloor>"  using ax_4a by auto

(* Observation II-2-1 *)
lemma ax_5b': "ob X Y \<longleftrightarrow> ob X (\<lambda>z. X z \<and> Y z)" by (metis (no_types, lifting) ax_5b) 
lemma ax_5b'': "ob X Y \<longleftrightarrow> ob X (\<lambda>z. Y z \<and> X z)" by (metis (no_types, lifting) ax_5b) 

(* Characterisation of "\<^bold>O" *)
lemma C_2: "\<lfloor>\<^bold>O\<^bold>\<langle>A\<^bold>|B\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>(B \<^bold>\<and> A)\<rfloor>"  by (metis ax_5a ax_5b)  
lemma C_3: "\<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> ) \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>" using ax_5c by auto 
lemma C_4: "\<lfloor>(\<^bold>\<box>(A \<^bold>\<rightarrow> B) \<^bold>\<and> (\<^bold>\<diamond>(A \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O\<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"   using ax_5e by blast
lemma C_5: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>)\<rfloor>"  by presburger 
lemma C_6: "\<lfloor>\<^bold>\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O\<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>)\<rfloor>"  by (smt ax_5b) 
lemma C_7: "\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by blast 
lemma C_8: "\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>"  
 proof -   
  have  "\<forall>X Y Z. (ob X Y \<and> (\<forall>w. X w  \<longrightarrow> Z w)) \<longrightarrow> ob Z (\<lambda>w. (Z w \<and> \<not>X w) \<or> Y w)" by  (smt ax_5d  ax_5b ax_5b'')
  thus ?thesis  using ax_5b by fastforce qed

(* Relationship between "\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_13_a: "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a(\<^bold>\<not>A))\<rfloor>"  by (metis (full_types) ax_5a ax_5b)
lemma C_13_b: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>pA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>p(\<^bold>\<not>A))\<rfloor>"   by (metis (full_types) ax_5a ax_5b) 
lemma C_14_a: "\<lfloor>\<^bold>\<box>\<^sub>a(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>aA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>aB)\<rfloor>"  by (metis ax_5b)
lemma C_14_b: "\<lfloor>\<^bold>\<box>\<^sub>p(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>pA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>pB)\<rfloor>"  by (metis ax_5b)

(* Relationship between "\<^bold>O\<^sub>,\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_15_a: "\<lfloor>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>aA \<^bold>\<and> \<^bold>\<diamond>\<^sub>aB \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>aB\<rfloor>"  using ax_5e by blast
lemma C_15_b: "\<lfloor>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>pA \<^bold>\<and> \<^bold>\<diamond>\<^sub>pB \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>pB\<rfloor>"  using ax_5e by blast

(* Soundness and consistency *)
lemma II_3_1: "((\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))) \<longrightarrow> ob(Z)(A \<^bold>\<rightarrow> B)" 
  proof 
    assume "(\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))"
     hence "ob (\<lambda>z. A z \<and> Z z) (\<lambda>z. A z \<and> Z z \<and> B z)" using ax_5e ax_5b  ax_5b' ax_5d by smt
     hence "ob (\<lambda>z. Z z \<and> A z) (\<lambda>z. Z z \<and> A z \<and> B z)" using ax_5e ax_5b  ax_5b' ax_5d by smt
     hence "ob Z (\<lambda>w. (Z w \<and> \<not>(Z w \<and> A w)) \<or> (Z w \<and> A w \<and> B w))" by (metis (mono_tags) ax_5d) 
     from this show  L19: "ob(Z)(A \<^bold>\<rightarrow> B)" by (smt ax_5b)  qed

(* Some theorems and derived (proof) rules *)
lemma II_4_1: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (C(A) \<^bold>\<leftrightarrow> C(B))\<rfloor>"  using ext by blast
lemma obs_II_4_1_a  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>C(A) \<^bold>\<leftrightarrow> C(B)\<rfloor>"  using ext by blast 
lemma obs_II_4_1_b  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"  using ax_5e by blast
lemma obs_II_4_1_c_1: "\<lfloor>\<^bold>\<diamond>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma obs_II_4_1_c_2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by auto
lemma obs_II_4_1_c_3: "\<lfloor>\<^bold>\<diamond>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by blast
lemma obs_II_4_1_c_4: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma res_II_4_1_a_1: "\<lfloor>\<^bold>\<not>(\<^bold>O\<^bold>\<langle>\<^bold>\<bottom>\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by (simp add: ax_5a)  
lemma res_II_4_1_a_2: "\<lfloor>(\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>"  using C_3  by auto
lemma res_II_4_1_a_3: "\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_a_4: "\<lfloor>\<^bold>\<diamond>\<^sub>p(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p(\<^bold>O\<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>)\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_a_5: "\<lfloor>(\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>C\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_b_1:  "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O\<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_b_2:  "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O\<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>\<rfloor>"  by (smt ax_5b)
lemma obs_II_4_2_1: "\<lfloor>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> (\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>(A \<^bold>\<rightarrow> B)))\<rfloor>"  by blast
lemma obs_II_4_2_2: "\<lfloor>\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" by (simp add: C_8)
lemma obs_II_4_2_3: "\<lfloor>(\<^bold>O\<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a\<^bold>\<top> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<rightarrow> B)\<rfloor>"  by (smt ax_5e)
lemma obs_II_4_2_4: "\<lfloor>\<^bold>\<box>\<^sub>a\<^bold>\<top>\<rfloor>"  by simp
lemma obs_II_4_2_5: "\<lfloor>(\<^bold>O\<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<rightarrow> B)\<rfloor>"  by (smt ax_5e)
lemma obs_II_4_2_6: "\<lfloor>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<rightarrow> B)\<rfloor>"   by (simp add: II_3_1)  
lemma obs_II_4_2_6_p: "\<lfloor>(\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p(A \<^bold>\<rightarrow> B)\<rfloor>"   by (simp add: II_3_1)  

lemma Oa_C: "\<lfloor>\<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^sub>aB \<^bold>\<rightarrow>  \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>" using ax_5c by auto
lemma Op_C: "\<lfloor>\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>pA \<^bold>\<and> \<^bold>O\<^sub>pB \<^bold>\<rightarrow>  \<^bold>O\<^sub>p(A \<^bold>\<and> B)\<rfloor>" using ax_5c by auto
lemma Oa_DD: "\<lfloor>(\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>" using ax_5b ax_5c obs_II_4_2_6 by smt 
lemma Op_DD: "\<lfloor>(\<^bold>O\<^sub>pA \<^bold>\<and> \<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p(A \<^bold>\<and> B)\<rfloor>" using ax_5b ax_5c obs_II_4_2_6_p by smt
end