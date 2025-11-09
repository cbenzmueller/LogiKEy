theory PMLinHOL_deep_further_tests_1_alt imports PMLinHOL_deep_tests                   (* Christoph Benzmüller, 2025 *)
begin             
\<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
\<comment>\<open>Test with schematic axioms\<close>
abbreviation(input) "AxT \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>"
abbreviation(input) "AxB \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"
abbreviation(input) "Ax4 \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)"
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

lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F1"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F1"                      nitpick sledgehammer             (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F2"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F2"                      nitpick sledgehammer             (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F3"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F3"                      nitpick sledgehammer             (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*proof*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*proof*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F4"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F4"                      nitpick sledgehammer             (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F5"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F5"                      nitpick sledgehammer             (*none*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F6"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F6"                      nitpick sledgehammer             (*none*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F7"                       nitpick sledgehammer             (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer              (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops     (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F7"                      nitpick sledgehammer             (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops (*unkn*)(*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F8"                      nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                     apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F9"                      nitpick sledgehammer           (*none*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*unkn*)(*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*unkn*)(*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>d F10"                     nitpick sledgehammer           (*none*)(*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)

\<comment>\<open>Summary of experiments: 
 Nitpick: ctex=8 (with simp 2, without simp 6), none=4 (with simp 0, without simp 4), unknwn=148 (with simp 78, without simp 70)
 Sledgehammer: proof=15 (with simp 11, without simp 4), no prf=145 (with simp 69, without simp 76)\<close>

\<comment>\<open>No conflicts\<close>
end 
