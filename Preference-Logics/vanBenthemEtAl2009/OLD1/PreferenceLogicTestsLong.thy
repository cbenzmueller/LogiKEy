theory PreferenceLogicTestsLong imports PreferenceLogicBasics  (*** Benzmüller & Fuenmayor, 2020 ***)            
begin 
(*some conceptually unimportant declarations of defaults for tools*) 
nitpick_params[assms=true,user_axioms=true,expect=genuine,format=3] 

(*Fact 1: definability of the four principal operators and verification*)
lemma Fact1_9:  "(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) u" by smt
lemma Fact1_10: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>E \<psi>) u" by smt
lemma Fact1_11: "(\<phi> \<^bold>\<prec>\<^sub>E\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>E\<^sub>E \<psi>) u" by smt
lemma Fact1_12: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>E \<psi>) u" by smt
(* Fact 2: definition of the remaining preference operators and verification*)
lemma Fact2_13:    "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) u  \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u"  nitpick oops (*Countermodel*)
lemma Fact2_13_lr: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_13_rl: "(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) u"   by blast
lemma Fact2_13: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) u"  by (smt 1) 
lemma Fact2_14:    "(\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi>) u  \<longleftrightarrow> (\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u"  nitpick oops (*Countermodel*)
lemma Fact2_14_lr: "(\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_14_rl: "(\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_14: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<succ>\<^sub>E\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<succ>\<^sub>E\<^sub>A \<psi>) u"  by (smt 1)
lemma Fact2_15:    "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) u  \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u"  nitpick oops (*Countermodel*)
lemma Fact2_15_lr: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_15_rl: "(\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_15: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A \<psi>) u"  by (smt 1)
lemma Fact2_16:    "(\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi>) u  \<longleftrightarrow> (\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u"  nitpick oops (*Countermodel*)
lemma Fact2_16_lr: "(\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_16_rl: "(\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi>) u"   nitpick oops (*Countermodel*)
lemma Fact2_16: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<succeq>\<^sub>E\<^sub>A \<psi>) u \<longleftrightarrow> (\<phi> \<succeq>\<^sub>E\<^sub>A \<psi>) u"  by (smt 1) 

(* Section 3.5 "Axiomatization" - verify interaction axioms *)
lemma Inclusion_1:      "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<preceq>\<phi>)\<rfloor>" by auto
lemma Interaction_1:    "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>" using transBR by blast
lemma Transitivity_le:  "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>" using transBR by blast 
lemma Interaction_2:    "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow>  ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor>" by blast
lemma Fact4:               "\<lfloor>(\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>\<preceq>\<psi>) \<^bold>\<rightarrow>  ((\<^bold>\<diamond>\<^sup>\<prec>\<psi>) \<^bold>\<or> \<^bold>\<diamond>\<^sup>\<preceq>(\<psi> \<^bold>\<and>  \<^bold>\<diamond>\<^sup>\<preceq>\<phi>))\<rfloor> 
                                          \<longleftrightarrow> (\<forall>w. \<forall>v. (((w \<preceq> v) \<and> \<not>(v \<preceq> w)) \<longrightarrow> (w \<prec> v)))"   by smt
lemma Interaction_3:   "\<lfloor>(\<^bold>\<diamond>\<^sup>\<prec>\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<^sup>\<prec>\<phi>)\<rfloor>" using transBR by blast
lemma Inclusion_2:      "\<lfloor>(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>E\<phi>)\<rfloor>"  by blast

(* Section 3.6 "A binary preference fragment" *)
(* \<^bold>\<preceq>\<^sub>E\<^sub>E is the dual of \<^bold>\<prec>\<^sub>A\<^sub>A *)
lemma "\<lfloor>(\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" by blast
lemma "\<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" by simp
(* \<preceq>\<^sub>E\<^sub>E is the dual of \<prec>\<^sub>A\<^sub>A only if totality is assumed*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" nitpick oops (*countermodel*)
lemma "\<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" by blast (* only this direction holds*)
lemma "is_total SBR \<longrightarrow> \<lfloor>(\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<prec>\<^sub>A\<^sub>A \<phi>)\<rfloor>" by blast
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" nitpick oops
lemma "\<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" by blast (* only this direction holds*)
lemma "is_total SBR \<longrightarrow> \<lfloor>(\<phi> \<prec>\<^sub>A\<^sub>A \<psi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" by blast
(* verify p.97-98 *)
lemma monotonicity:  "\<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<^bold>A(\<phi>\<^bold>\<rightarrow>\<xi>)) \<^bold>\<rightarrow> (\<xi> \<preceq>\<^sub>E\<^sub>E \<psi>)\<rfloor>" by blast
lemma reducibility:     "\<lfloor>(((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> \<alpha>) \<preceq>\<^sub>E\<^sub>E \<beta>) \<^bold>\<leftrightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<and> (\<alpha> \<preceq>\<^sub>E\<^sub>E \<beta>))\<rfloor>" by blast
lemma reflexivity:      "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>)\<rfloor>" using reflBR by blast
(* The condition below is supposed to enforce totality of the preference relation.
   However there are countermodels. See p.98 *)
lemma totality_v1: "is_total SBR \<longrightarrow> \<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>" by auto
lemma "\<lfloor>((\<phi> \<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor> \<longrightarrow> is_total SBR" 
  nitpick oops (*countermodel - error in paper?*)
lemma totality_v2: "is_total SBR \<longrightarrow> \<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor>" by auto
lemma "\<lfloor>((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>) \<^bold>\<and> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<psi>) \<^bold>\<or> (\<psi> \<^bold>\<preceq>\<^sub>E\<^sub>E \<phi>))\<rfloor> \<longrightarrow> is_total SBR"
  nitpick oops (*countermodel - error in paper?*)

(**** Section 5: Equality-based Ceteris Paribus Preference Logic ****)
(*Some tests: dualities*)
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^sup>\<preceq>\<^bold>\<not>\<phi>)\<rfloor>"  by auto
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^sup>\<prec>\<^bold>\<not>\<phi>)\<rfloor>"  by auto
lemma "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>([\<Gamma>]\<^bold>\<not>\<phi>)\<rfloor>"  by auto
(*Lemma 2*)
lemma lemma2_1: "(\<^bold>\<diamond>\<^sup>\<preceq>\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) w" by auto
lemma lemma2_2: "(\<^bold>\<diamond>\<^sup>\<prec>\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) w" by auto  
lemma lemma2_3a: "(\<^bold>E\<phi>) w \<longleftrightarrow> (\<^bold>\<langle>\<^bold>\<emptyset>\<^bold>\<rangle>\<phi>) w" by auto
lemma lemma2_3b: "(\<^bold>A\<phi>) w \<longleftrightarrow> ([\<^bold>\<emptyset>]\<phi>) w" by auto
(**Axiomatization:**)
(*inclusion and interaction axioms *)
lemma Inc1: "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>" by auto
lemma Inc2: "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)\<rfloor>" by auto
lemma Int3:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>" by (meson transBR) 
lemma Int4:  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>)\<rfloor>" by (metis transBR)
lemma Int5:  "\<lfloor>(\<psi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)) \<^bold>\<rightarrow> ( (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<or> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>))))\<rfloor>" using reflBR by fastforce
(*ceteris paribus reflexivity*)
lemma CetPar6:   assumes 1:"\<phi> \<^bold>\<in> \<Gamma>"   shows  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>) \<^bold>\<rightarrow> \<phi>\<rfloor>"  using 1 by blast 
lemma CetPar7:   assumes 1:"\<phi> \<^bold>\<in> \<Gamma>"   shows  "\<lfloor>(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<^bold>\<not>\<phi>\<rfloor>"  using 1 by blast 
(*monotonicity*)
lemma CetPar8:   assumes 1:"\<Gamma> \<^bold>\<subseteq> \<Gamma>' " shows  "\<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>)\<rfloor>"  using 1 by auto
lemma CetPar9:   assumes 1:"\<Gamma> \<^bold>\<subseteq> \<Gamma>' " shows  "\<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>)\<rfloor>"  using 1 by auto
lemma CetPar10: assumes 1:"\<Gamma> \<^bold>\<subseteq> \<Gamma>' " shows  "\<lfloor>(\<^bold>\<langle>\<Gamma>'\<^bold>\<rangle>\<^sup>\<prec>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>\<phi>)\<rfloor>"  using 1 by auto
(*increase (decrease) of ceteris paribus sets*)
lemma CetPar11a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<alpha>)\<rfloor>" by auto 
lemma CetPar11b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<alpha>)\<rfloor>" by auto 
lemma CetPar12a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>" by auto 
lemma CetPar12b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>" by auto 
lemma CetPar13a: "\<lfloor>(\<phi> \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<alpha> \<^bold>\<and> \<phi>) )) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<prec>\<alpha>)\<rfloor>" by auto 
lemma CetPar13b: "\<lfloor>((\<^bold>\<not>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<prec>(\<alpha> \<^bold>\<and> \<^bold>\<not>\<phi>))) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<prec>\<alpha>)\<rfloor>" by auto 
(*Example 1*)
lemma Example1: "\<lfloor>(([\<Gamma>]\<^sup>\<preceq>\<phi>) \<^bold>\<and> (\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<langle>\<Gamma>\<^bold>\<union>\<^bold>{\<phi>\<^bold>}\<^bold>\<rangle>\<^sup>\<preceq>\<alpha>)\<rfloor>" using reflBR by auto
(*Lemma 4: Existence Lemma*)
lemma Lemma4: "(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<^sup>\<preceq>\<phi>) w \<longrightarrow> (\<exists>v. (w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<and> (\<phi> v))"  by simp 
(*Corollary 1*)
lemma Corollary1: "(\<^bold>\<langle>\<Gamma>\<^bold>\<rangle>\<phi>) w \<longrightarrow> (\<exists>v. (w \<^bold>\<equiv>\<^sub>\<Gamma> v) \<and> (\<phi> v))"  by simp 
(*Lemma 5*)
lemma Lemma5: "(w \<^bold>\<unlhd>\<^sub>\<Gamma> v) \<longleftrightarrow> ((w \<preceq> v) \<and> (w \<^bold>\<equiv>\<^sub>\<Gamma> v))" by auto  

(**** Section 6: Ceteris Paribus Counterparts of Binary Preference Statements ****)

(*AA-variant (drawing upon von Wright's)*)
lemma leAA_cp_pref:    "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u  \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  nitpick oops (*Countermodel*)
lemma leAA_cp_pref_lr: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" nitpick oops (*Countermodel*)
lemma leAA_cp_pref_rl: "(\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" by auto
lemma leAA_cp_pref: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  by (smt 1)
lemma leqAA_cp_pref:    "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u  \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  nitpick oops (*Countermodel*)
lemma leqAA_cp_pref_lr: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" nitpick oops (*Countermodel*)
lemma leqAA_cp_pref_rl: "(\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longrightarrow> (\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u" nitpick oops (*Countermodel*)
lemma leqAA_cp_pref: assumes 1:"is_total SBR"  shows  "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) u"  by (smt 1)

(*AE-variant*)
lemma leAE_cp_pref: "(\<phi> \<^bold>\<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<preceq>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u" by auto
lemma leqAE_cp_pref: "(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u \<longleftrightarrow> (\<phi> \<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) u" by auto

(*miscelaneous tests*)
lemma  "let \<Gamma> = \<^bold>\<emptyset> in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>" by simp
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>" by simp  
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>,A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>))\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A \<psi>)) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>A\<^sup>\<Gamma> \<psi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>\<emptyset> in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>" by simp
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>" by simp  
lemma  "let \<Gamma> = \<^bold>{\<^bold>\<bottom>,A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)\<rfloor>" nitpick oops (*Countermodel*)
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>))\<rfloor>" by auto
lemma  "let \<Gamma> = \<^bold>{A,B\<^bold>} in \<lfloor>(\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>) \<^bold>\<rightarrow> ((A \<^bold>\<and> B) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>))\<rfloor>" by auto
lemma  "let \<Gamma> = \<^bold>{A\<^bold>} in \<lfloor>(A \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>)) \<^bold>\<rightarrow> (\<phi> \<^bold>\<prec>\<^sub>A\<^sub>E\<^sup>\<Gamma> \<psi>)\<rfloor>" nitpick oops (*Countermodel*)

end


