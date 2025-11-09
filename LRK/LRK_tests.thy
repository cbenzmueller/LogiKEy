\<comment> \<open>In this file, we test our embedding and prove that the 
semantic results and the axiomatization provided in the paper hold 
for our embedding.\<close>

theory LRK_tests
 imports LRK
begin 

\<comment> \<open>Validities about the notion of the power to know:\<close>
lemma Ten_One: "\<lfloor>Rr \<^bold>\<top>\<rfloor>"by simp
lemma Ten_Two: "\<lfloor>((Rr \<phi>) \<^bold>\<and> (Rr \<psi>)) \<^bold>\<rightarrow> (Rr (\<phi> \<^bold>\<and> \<psi>))\<rfloor>" by metis
lemma Ten_Three: "\<lfloor>(Rr \<phi>) \<^bold>\<rightarrow> (Rr \<^bold>\<not>\<phi>)\<rfloor>" by auto
lemma Ten_Four: "\<lfloor>(Rr \<phi>) \<^bold>\<leftrightarrow> (U (Rr \<phi>))\<rfloor>" by metis

\<comment> \<open>Logical rules governing the operators of LRK:\<close>
lemma Eleven_One: "\<lfloor>(Os (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((Os \<phi>) \<^bold>\<rightarrow> (Os \<psi>))\<rfloor>" by auto
lemma Eleven_Two: "\<lfloor>(U \<phi>) \<^bold>\<rightarrow> (Os \<phi>)\<rfloor>" by simp
lemma Eleven_Three: "\<lfloor>(\<^bold>\<not> (Os \<^bold>\<bottom>)) \<^bold>\<rightarrow> ((Os \<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" by (metis Nax)
lemma Eleven_Four: "\<lfloor>(Kr (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((Os \<phi>) \<^bold>\<rightarrow> (Os \<psi>))\<rfloor>" by auto
lemma Eleven_Five: "\<lfloor>(Kr \<phi>) \<^bold>\<rightarrow> (Os \<phi>)\<rfloor>" by simp

\<comment> \<open>See other file for the full proof.\<close>
lemma Twelve_1: "\<not>\<lfloor>(Rr \<phi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> [\<phi>?](Os \<phi>))\<rfloor>" 
  (*nitpick[user_axioms, satisfy]*) oops

\<comment> \<open>Further formulas proven to hold:\<close>
lemma Thirteen_One_a: "\<lfloor>(([\<phi>!]\<^sup>Ap) \<^bold>\<leftrightarrow> \<^sup>Ap)\<rfloor>" by simp
lemma Thirteen_One_b: "\<lfloor>(([\<phi>?]\<^sup>Ap) \<^bold>\<leftrightarrow> \<^sup>Ap)\<rfloor>" by simp
lemma Thirteen_Two_a: "\<lfloor>([\<phi>!]\<^bold>\<not>\<psi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>[\<phi>!]\<psi>)\<rfloor>" by simp
lemma Thirteen_Two_b: "\<lfloor>([\<phi>!]\<^bold>\<not>\<psi>) \<^bold>\<leftrightarrow> (\<^bold>\<not>[\<phi>!]\<psi>)\<rfloor>" by simp
lemma Thirteen_Three_a: "\<lfloor>([\<phi>!](\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<leftrightarrow> (([\<phi>!]\<psi>) \<^bold>\<rightarrow> ([\<phi>!]\<chi>))\<rfloor>" by simp
lemma Thirteen_Three_b: "\<lfloor>([\<phi>?](\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<leftrightarrow> (([\<phi>?]\<psi>) \<^bold>\<rightarrow> ([\<phi>?]\<chi>))\<rfloor>" by simp
lemma Thirteen_Four_a: "\<lfloor>([\<phi>!](U \<psi>)) \<^bold>\<leftrightarrow> (U [\<phi>!]\<psi>)\<rfloor>" by simp
lemma Thirteen_Four_b: "\<lfloor>([\<phi>?](U \<psi>)) \<^bold>\<leftrightarrow> (U [\<phi>?]\<psi>)\<rfloor>" by auto
lemma Thirteen_Five_a: "\<lfloor>([\<phi>!](Q \<psi>)) \<^bold>\<leftrightarrow> (Q (([\<phi>!]\<psi>)))\<rfloor>" by auto
lemma Thirteen_Five_b: "\<lfloor>([\<phi>?](Q \<psi>)) \<^bold>\<leftrightarrow> (Q (([\<phi>?]\<psi>)))\<rfloor>" by auto
lemma Thirteen_Six: "\<lfloor>([\<phi>?](Kr \<psi>)) \<^bold>\<leftrightarrow> (Kr ([\<phi>?]\<psi>))\<rfloor>" by simp
lemma Thirteen_Seven: "\<lfloor>([\<phi>!](Kr \<psi>)) \<^bold>\<leftrightarrow> ((\<phi> \<^bold>\<and> (Kr (\<phi> \<^bold>\<rightarrow> ([\<phi>!]\<psi>)))) \<^bold>\<or> 
  ((\<^bold>\<not>\<phi>) \<^bold>\<and> (Kr ((\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> ([\<phi>!]\<psi>)))))\<rfloor>" by blast

\<comment> \<open>Propositional tautologies\<close>
lemma Identity: "\<lfloor>\<phi>\<rfloor>  \<Longrightarrow> \<lfloor>\<phi>\<rfloor>" by simp
lemma NonContradiction: "\<lfloor>\<^bold>\<not> (\<phi> \<^bold>\<and> (\<^bold>\<not>\<phi>))\<rfloor>" by simp
lemma ExcludedMiddle: "\<lfloor>\<phi> \<^bold>\<or> (\<^bold>\<not>\<phi>)\<rfloor>" by simp
lemma DoubleNegation: "\<lfloor>(\<^bold>\<not> (\<^bold>\<not> \<phi>)) \<^bold>\<rightarrow> \<phi>\<rfloor>" by simp
lemma Implication: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" by simp
lemma DeMorgan1: "\<lfloor>(\<^bold>\<not>(\<phi> \<^bold>\<and> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>\<not> \<phi>) \<^bold>\<or> (\<^bold>\<not> \<psi>))\<rfloor>" by simp
lemma DeMorgan2:  "\<lfloor>(\<^bold>\<not>(\<phi> \<^bold>\<or> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<not>\<psi>))\<rfloor>" by simp
lemma Contrapositive: "\<lfloor>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<leftrightarrow> ((\<^bold>\<not>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<not>\<phi>))\<rfloor>" by blast

\<comment> \<open>S5 Axioms\<close>
lemma K_S5_1: "\<lfloor>(Kr (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((Kr \<phi>) \<^bold>\<rightarrow> (Kr \<psi>))\<rfloor>" by simp
lemma K_S5_2: "\<lfloor>(Kr \<phi>) \<^bold>\<rightarrow> \<phi>\<rfloor>" using til_ref dtil_ref by auto
lemma K_S5_3: "\<lfloor>(Kr \<phi>) \<^bold>\<rightarrow> (Kr (Kr \<phi>))\<rfloor>" by (meson til_trans)
lemma K_S5_4: "\<lfloor>(\<^bold>\<not>(Kr \<phi>)) \<^bold>\<rightarrow> Kr (\<^bold>\<not> (Kr \<phi>))\<rfloor>" by (meson til_sym til_trans)
lemma Q_S5_1: "\<lfloor>(Q (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((Q \<phi>) \<^bold>\<rightarrow> (Q \<psi>))\<rfloor>" by simp
lemma Q_S5_2: "\<lfloor>(Q \<phi>) \<^bold>\<rightarrow> \<phi>\<rfloor>" using dtil_ref by blast
lemma Q_S5_3: "\<lfloor>(Q \<phi>) \<^bold>\<rightarrow> (Q (Q (\<phi>)))\<rfloor>" using dtil_trans by blast
lemma Q_S5_4: "\<lfloor>(\<^bold>\<not>(Q \<phi>)) \<^bold>\<rightarrow> Q (\<^bold>\<not> (Q \<phi>))\<rfloor>" using dtil_sym dtil_trans by blast
lemma U_S5_1: "\<lfloor>(U (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((U \<phi>) \<^bold>\<rightarrow> (U \<psi>))\<rfloor>" by simp
lemma U_S5_2: "\<lfloor>(U \<phi>) \<^bold>\<rightarrow> \<phi>\<rfloor>" by simp
lemma U_S5_3: "\<lfloor>(U \<phi>) \<^bold>\<rightarrow> (U (U (\<phi>)))\<rfloor>" by simp
lemma U_S5_4: "\<lfloor>(\<^bold>\<not>(U \<phi>)) \<^bold>\<rightarrow> U (\<^bold>\<not> (U \<phi>))\<rfloor>" by simp

\<comment> \<open>Others\<close>
lemma U: "\<lfloor>(U \<phi>) \<^bold>\<rightarrow> ((Q \<phi>) \<^bold>\<and> (Kr \<phi>))\<rfloor>" by simp
lemma K_O: "\<lfloor>(Kr \<phi>) \<^bold>\<rightarrow> (Os \<phi>)\<rfloor>" by simp
lemma O: "\<lfloor>(\<^bold>\<not> (Os \<^bold>\<bottom>)) \<^bold>\<rightarrow> ((Os \<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" by (simp add: Eleven_Three) 
lemma Dist: "\<lfloor>(Os (\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> ((Os \<phi>) \<^bold>\<rightarrow> (Os \<psi>))\<rfloor>" by simp

lemma U_Excl_a: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> \<psi>))) \<^bold>\<rightarrow> (([\<phi>!]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>!]\<chi>))\<rfloor>" by simp
lemma U_Excl_b: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> (\<^bold>\<not>\<psi>)))) \<^bold>\<rightarrow> (([\<phi>!]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>!]\<chi>))\<rfloor>" by simp
lemma U_Excl: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> \<psi>)) \<^bold>\<or> (U (\<phi> \<^bold>\<leftrightarrow> (\<^bold>\<not>\<psi>)))) \<^bold>\<rightarrow> (([\<phi>!]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>!]\<chi>))\<rfloor>" by simp

lemma U_Ques_a: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> (\<psi>)))) \<^bold>\<rightarrow> (([\<phi>?]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>?]\<chi>))\<rfloor>" by simp
lemma h1: "\<forall>w. (\<phi> til (\<lambda>w X. N w X \<and> ((\<forall>v. X v \<longrightarrow> \<psi> til N v) \<or> (\<forall>v. X v \<longrightarrow> \<not> \<psi> til N v))) w) =
  (\<phi> til (\<lambda>w X. N w X \<and> ((\<forall>v. X v \<longrightarrow> \<not> \<psi> til N v) \<or> (\<forall>v. X v \<longrightarrow> \<psi> til N v))) w)" by meson
lemma h2: "\<lfloor>([\<psi>?]\<phi>) \<^bold>\<leftrightarrow> ([\<^bold>\<not>\<psi>?]\<phi>)\<rfloor>" using h1 by simp 
lemma h3: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> (\<^bold>\<not>\<psi>)))) \<^bold>\<rightarrow> (([\<phi>?]\<chi>) \<^bold>\<leftrightarrow> ([\<^bold>\<not>\<psi>?]\<chi>))\<rfloor>" by simp
lemma U_Ques_b: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> (\<^bold>\<not>\<psi>)))) \<^bold>\<rightarrow> (([\<phi>?]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>?]\<chi>))\<rfloor>" using h2 h3 apply simp by meson
lemma U_Ques: "\<lfloor>((U (\<phi> \<^bold>\<leftrightarrow> \<psi>)) \<^bold>\<or> (U (\<phi> \<^bold>\<leftrightarrow> (\<^bold>\<not>\<psi>)))) \<^bold>\<rightarrow> (([\<phi>?]\<chi>) \<^bold>\<leftrightarrow> ([\<psi>?]\<chi>))\<rfloor>" 
  using U_Ques_a U_Ques_b 
  by simp 

\<comment> \<open>Inference rules:\<close>
lemma Mp: "\<lbrakk>\<lfloor>\<phi>\<rfloor>; \<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>\<psi>\<rfloor>" by simp
lemma Nec: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>U \<phi>\<rfloor>" by simp

\<comment> \<open>Axioms also hold for the updated @{text "til"} and @{text "N"}.\<close>
lemma tilde_ref_update: "\<forall>w t q n \<phi>. t w w \<longrightarrow> (update_t \<phi> n t q) w w" 
  by simp
lemma tilde_sym_update: "(\<forall>w v t q n \<phi>.  (t w v \<longrightarrow> t v w) \<longrightarrow>
  (((update_t \<phi> n t q) w v) \<longrightarrow> ((update_t \<phi> n t q) v w)))" 
  by simp
lemma tilde_trans_update: "\<forall>w v u t q n \<phi>. 
  ((t w v) \<and> (t v u) \<longrightarrow> (t w u))
  \<longrightarrow> ((update_t \<phi> n t q) w v \<and> (update_t \<phi> n t q) v u \<longrightarrow> (update_t \<phi> n t q) w u)" 
  by simp
lemma Nax_update: "\<forall>w t q n \<phi>. (\<forall>H. (((N w) H \<longrightarrow> H w)) 
  \<longrightarrow> (((update_N \<phi> N dtil til) w) H \<longrightarrow> H w))"
  by simp

end
