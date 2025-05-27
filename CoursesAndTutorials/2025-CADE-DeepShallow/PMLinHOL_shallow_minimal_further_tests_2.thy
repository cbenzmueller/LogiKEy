theory PMLinHOL_shallow_minimal_further_tests_2 imports PMLinHOL_shallow_minimal_tests                    (* C.B., 2025 *)
begin             
\<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
\<comment>\<open>Test with semantic conditions\<close>
abbreviation(input) refl ("\<r>") where "\<r> \<equiv> \<lambda>R. reflexive R"
abbreviation(input) sym ("\<s>") where "\<s> \<equiv> \<lambda>R.  symmetric R"
abbreviation(input) tra ("\<t>") where "\<t> \<equiv> \<lambda>R.  transitive R"

consts \<phi>::\<sigma> \<psi>::\<sigma> 
abbreviation(input) "F1   \<equiv> (\<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<supset>\<^sup>m \<diamond>\<^sup>m\<phi>"                                                 \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"                                          \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m\<phi>"                                                  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4   \<equiv> (\<box>\<^sup>m(\<diamond>\<^sup>m(\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)))) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"                            \<comment>\<open>holds in KB\<close>
abbreviation(input) "F5   \<equiv> (\<diamond>\<^sup>m(\<phi> \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))) \<supset>\<^sup>m ((\<diamond>\<^sup>m\<phi>) \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))"                  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6   \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>)) \<and>\<^sup>m (\<diamond>\<^sup>m(\<box>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<diamond>\<^sup>m\<psi>)"       \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7   \<equiv> (\<diamond>\<^sup>m\<phi>) \<supset>\<^sup>m (\<box>\<^sup>m(\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>))"                                       \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m (\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>)"                                       \<comment>\<open>holds in KT and in KB\<close>
abbreviation(input) "F9   \<equiv> ((\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m \<phi>)))) \<supset>\<^sup>m \<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)"          \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<box>\<^sup>m\<psi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<box>\<^sup>m\<psi>)"   \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R           \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma KT:   "\<r> R                    \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma KB:   "          \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops    (*none*)(*proof*)
lemma K:     "                               (\<Turnstile>\<^sup>m F1)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops  (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "          \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer           (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops    (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R           \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*none*)(*proof*)
                                                  apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KT:   "\<r> R                    \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                  apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "          \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*none*)(*proof*)
                                                  apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                  apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                               (\<Turnstile>\<^sup>m F2)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                  apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops  (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "          \<s> R         \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                              (\<Turnstile>\<^sup>m F3)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops    (*none*)(*proof*)
lemma K:     "                               (\<Turnstile>\<^sup>m F4)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer             (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma K:     "                              (\<Turnstile>\<^sup>m F5)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                              (\<Turnstile>\<^sup>m F6)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                  apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                              (\<Turnstile>\<^sup>m F7)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB:   "        \<s> R           \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer            (*none*)(*proof*)
                                                  apply simp nitpick sledgehammer oops  (*none*)(*proof*)
lemma K4:   "                   \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                  apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)
lemma K:     "                               (\<Turnstile>\<^sup>m F8)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                   apply simp nitpick sledgehammer oops (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer             (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops   (*none*)(*proof*)
lemma KB:   "          \<s> R         \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "                              (\<Turnstile>\<^sup>m F9)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops    (*none*)(*proof*)
lemma S4:   "\<r> R \<and>          \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops     (*none*)(*proof*)
lemma KB4: "         \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma KTB: "\<r> R \<and> \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops     (*none*)(*proof*)
lemma KT:   "\<r> R                   \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*none*)(*proof*)
                                                 apply simp nitpick sledgehammer oops     (*none*)(*proof*)
lemma KB:   "         \<s> R          \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K4:   "                  \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K:     "                              (\<Turnstile>\<^sup>m F10)"  nitpick sledgehammer            (*ctex*)(*no prf*)
                                                 apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)

\<comment>\<open>Summary of experiments: 
 Nitpick: ctex=84 (with simp 42, without simp 42), none=76 (with simp 38, without simp 38), unknwn=0 
 Sledgehammer: proof=76 (with simp 38, without simp 38), no prf=84 (with simp 42, without simp 42) 

MacBookPro 16,1 with 6-Core Intel Core i7 processor, 2,6 GHz, 6 Cores,  256 KB L2 Cache (per Core), 12 MB L3 Cache, 16 GB Memory
\<close>

\<comment>\<open>No conflicts\<close>
end