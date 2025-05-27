theory PMLinHOL_deep_further_tests_2_alt imports PMLinHOL_deep_tests                          (* Christoph Benzmüller, 2025 *)
begin             
\<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
\<comment>\<open>Test with semantic conditions\<close>
abbreviation(input) refl ("\<r>") where "\<r> \<equiv> \<lambda>R. reflexive R"
abbreviation(input) sym ("\<s>") where "\<s> \<equiv> \<lambda>R.  symmetric R"
abbreviation(input) tra ("\<t>") where "\<t> \<equiv> \<lambda>R.  transitive R"
end
consts \<phi>::PML \<psi>::PML
abbreviation(input) "F1   \<equiv> (\<diamond>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<supset>\<^sup>d \<diamond>\<^sup>d\<phi>"                                             \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2   \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"                                      \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3   \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d \<box>\<^sup>d\<phi>"                                             \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4   \<equiv> (\<box>\<^sup>d(\<diamond>\<^sup>d(\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)))) \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"                         \<comment>\<open>holds in KB/K4\<close>
abbreviation(input) "F5   \<equiv> (\<diamond>\<^sup>d(\<phi> \<and>\<^sup>d (\<diamond>\<^sup>d\<psi>))) \<supset>\<^sup>d ((\<diamond>\<^sup>d\<phi>) \<and>\<^sup>d (\<diamond>\<^sup>d\<psi>))"               \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6   \<equiv> ((\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<psi>)) \<and>\<^sup>d (\<diamond>\<^sup>d(\<box>\<^sup>d(\<not>\<^sup>d\<psi>)))) \<supset>\<^sup>d \<not>\<^sup>d(\<diamond>\<^sup>d\<psi>)"     \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7   \<equiv> (\<diamond>\<^sup>d\<phi>) \<supset>\<^sup>d (\<box>\<^sup>d(\<phi> \<or>\<^sup>d \<diamond>\<^sup>d\<phi>))"                                   \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8   \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d (\<phi> \<or>\<^sup>d \<diamond>\<^sup>d\<phi>)"                                   \<comment>\<open>holds in KT/KB\<close>
abbreviation(input) "F9   \<equiv> ((\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and>\<^sup>d (\<box>\<^sup>d(\<diamond>\<^sup>d(\<not>\<^sup>d \<phi>)))) \<supset>\<^sup>d \<diamond>\<^sup>d(\<diamond>\<^sup>d\<phi>)"         \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<box>\<^sup>d\<psi>)) \<and>\<^sup>d (\<box>\<^sup>d(\<diamond>\<^sup>d(\<not>\<^sup>d\<psi>)))) \<supset>\<^sup>d \<not>\<^sup>d(\<box>\<^sup>d\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer            (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R           \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "\<r> R                    \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma K:     "                               (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB4: "          \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer          (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R           \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<r> R                    \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "          \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                               (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "          \<s> R         \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma K:     "                               (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer            (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer            (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB:   "        \<s> R           \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer          (*ctex*)(*no prf*)
                                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma K:     "                               (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8)"  nitpick sledgehammer          (*ctex*)(*no prf*)
                                                                                       apply simp nitpick sledgehammer oops (*unkn*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer            (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB:   "          \<s> R         \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*proof*)
                                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K:     "                              (\<forall>W V. \<forall>w:W.  \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10)"  nitpick sledgehammer           (*none*)(*no prf*)
                                                                                     apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)

\<comment>\<open>Summary of experiments: 
 Nitpick: ctex=32 (with simp 8, without simp 24), none=56 (with simp 0, without simp 56), unknwn=72 (with simp 72, without simp 0)
 Sledgehammer: proof=67 (with simp 38, without simp 29), no prf=93 (with simp 42, without simp 51)\<close>

\<comment>\<open>No conflicts\<close>
end


