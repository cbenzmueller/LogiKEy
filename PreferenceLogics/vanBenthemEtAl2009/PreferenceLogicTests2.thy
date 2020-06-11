theory PreferenceLogicTests2                (*Benzmüller & Fuenmayor, 2020*)  
   imports PreferenceLogicCeterisParibus
begin (*Tests for the SSE of van Benthem, Girard and Roy, JPL 2009, in HOL*)
(**** Section 5: Equality-based Ceteris Paribus Preference Logic ****)
(*Some tests: dualities*)
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^sup>\<preceq>\<^bold>\<not>\<phi>)\<rfloor>"  by auto
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^sup>\<prec>\<^bold>\<not>\<phi>)\<rfloor>"  by auto
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)  \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^bold>\<not>\<phi>)\<rfloor>"    by auto
(*Lemma 2*)
lemma lemma2_1: "(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) w" by auto
lemma lemma2_2: "(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) w" by auto  
lemma lemma2_3: "((\<^bold>E\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<phi>) w) \<and> ((\<^bold>A\<phi>) w \<longleftrightarrow> ([\<^bold>\<emptyset>]\<phi>) w)" by auto
(**Axiomatization:**)
(*inclusion and interaction axioms *)
lemma Inc1:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>" by auto
lemma Inc2:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)\<rfloor>"  by auto
lemma Int3:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>"  by (meson transBR) 
lemma Int4:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>)\<rfloor>"  by (metis transBR)
lemma Int5:  "\<lfloor>(\<psi>\<^bold>\<and>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow> ((\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>)\<^bold>\<or>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<phi>\<^bold>\<and>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>))))\<rfloor>" 
              using reflBR by force
(*ceteris paribus reflexivity*)
lemma CetPar6: "\<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> \<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>) \<^bold>\<rightarrow> \<phi>\<rfloor>"    by blast 
lemma CetPar7: "\<phi> \<^bold>\<in> \<Gamma> \<longrightarrow> \<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<phi>\<rfloor>" by blast 
(*monotonicity*)
lemma CetPar8:  "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<longrightarrow> \<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)\<rfloor>"   by auto
lemma CetPar9:  "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<longrightarrow> \<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>" by auto
lemma CetPar10: "\<Gamma> \<^bold>\<subseteq> \<Gamma>' \<longrightarrow> \<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>)\<rfloor>" by auto
(*increase (decrease) of ceteris paribus sets*)
lemma CetPar11a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<alpha>)\<rfloor>"       by auto 
lemma CetPar11b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<alpha>)\<rfloor>"   by auto 
lemma CetPar12a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>"     by auto 
lemma CetPar12b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>" by auto 
lemma CetPar13a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<prec>\<alpha>)\<rfloor>"     by auto 
lemma CetPar13b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<prec>\<alpha>)\<rfloor>" by auto 
(*Example 1, Lemma 4, Corollary 1 and Lemma5*)
lemma Ex1:    "\<lfloor>(([\<Gamma>]\<^sup>\<preceq>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>" using reflBR by auto
lemma Lemma4: "(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) w \<longrightarrow> (\<exists>v. (w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<and> (\<phi> v))"  by simp 
lemma Cor1:   "(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)  w \<longrightarrow> (\<exists>v. (w \<^bold>\<equiv>\<^sub>\<Gamma> v) \<and> (\<phi> v))"  by simp 
lemma Lemma5: "(w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<longleftrightarrow> ((w \<preceq> v) \<and> (w \<^bold>\<equiv>\<^sub>\<Gamma> v))"    by auto  

(**** Section 6: Ceteris Paribus Counterparts of Binary Preference Statements ****)
(*AA-variant (drawing upon von Wright's)*)
lemma lAA_cp_pref:     "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u  \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" nitpick oops (*Countermodel*)
lemma lAA_cp_pref_lr:  "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  nitpick oops (*Countermodel*)
lemma lAA_cp_pref_rl:  "(\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  by auto
lemma lAA_cp_pref:     "is_total SBR \<longrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  by smt 
lemma lqAA_cp_pref:    "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u  \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" nitpick oops (*Countermodel*)
lemma lqAA_cp_pref_lr: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  nitpick oops (*Countermodel*)
lemma lqAA_cp_pref_rl: "(\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  nitpick oops (*Countermodel*)
lemma lqAA_cp_pref:    "is_total SBR \<longrightarrow> (\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  by smt
(*AE-variant*)
lemma leAE_cp_pref: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u" by auto
lemma leqAE_cp_pref: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u" by auto
(*miscelaneous tests*)
lemma  "let \<Gamma> = \<^bold>\<emptyset> in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>"    by simp
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>" by simp  
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>,A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>"     nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>))\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>\<emptyset> in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>"    by simp
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>" by simp  
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>,A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>"     nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>))\<rfloor>"         by auto
lemma  "let \<Gamma> = \<^bold>{A,B\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> ((A \<^bold>\<and> B) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>))\<rfloor>" by auto
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>)\<rfloor>" nitpick oops (*Countermodel*)
end


