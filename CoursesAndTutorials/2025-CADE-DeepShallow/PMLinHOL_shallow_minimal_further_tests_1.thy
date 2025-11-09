theory PMLinHOL_shallow_minimal_further_tests_1 imports PMLinHOL_shallow_minimal_tests                    (* C.B., 2025 *)
begin             
\<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
\<comment>\<open>Test with schematic axioms\<close>
abbreviation(input) "AxT \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>m (\<box>\<^sup>m\<phi>) \<supset>\<^sup>m \<phi>"
abbreviation(input) "AxB \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>m \<phi> \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"
abbreviation(input) "Ax4 \<equiv> \<forall>\<phi>. \<Turnstile>\<^sup>m (\<box>\<^sup>m\<phi>) \<supset>\<^sup>m \<box>\<^sup>m(\<box>\<^sup>m\<phi>)"

consts \<phi>::\<sigma> \<psi>::\<sigma> 
abbreviation(input) "F1   \<equiv> (\<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<supset>\<^sup>m \<diamond>\<^sup>m\<phi>"                                                 \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"                                          \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m\<phi>"                                                  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4   \<equiv> (\<box>\<^sup>m(\<diamond>\<^sup>m(\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)))) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"                            \<comment>\<open>holds in KB/K4\<close>
abbreviation(input) "F5   \<equiv> (\<diamond>\<^sup>m(\<phi> \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))) \<supset>\<^sup>m ((\<diamond>\<^sup>m\<phi>) \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))"                  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6   \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>)) \<and>\<^sup>m (\<diamond>\<^sup>m(\<box>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<diamond>\<^sup>m\<psi>)"       \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7   \<equiv> (\<diamond>\<^sup>m\<phi>) \<supset>\<^sup>m (\<box>\<^sup>m(\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>))"                                       \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8   \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m (\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>)"                                       \<comment>\<open>holds in KT/KB\<close>
abbreviation(input) "F9   \<equiv> ((\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m \<phi>)))) \<supset>\<^sup>m \<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)"          \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<box>\<^sup>m\<psi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<box>\<^sup>m\<psi>)"   \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*none*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F1"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma K:     "                                  \<Turnstile>\<^sup>m F1"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F2"                     nitpick sledgehammer              (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*none*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*none*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F2"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F2"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*none*) (*proof*))
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F3"                       nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F3"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F4"                     nitpick sledgehammer              (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F4"                      nitpick sledgehammer             (*unkn*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F4"                     nitpick sledgehammer              (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F4"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F4"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F4"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F4"                      nitpick sledgehammer             (*unkn*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*unkn*) (*proof*)
lemma K:     "                                  \<Turnstile>\<^sup>m F4"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*none*)(*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F5"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma K:     "                                  \<Turnstile>\<^sup>m F5"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F6"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F6"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops    (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F7"                      nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F7"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops    (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F8"                     nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F8"                      nitpick sledgehammer           (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F8"                     nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F8"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F8"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F8"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F8"                      nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F8"                     nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F9"                     nitpick sledgehammer             (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F9"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F9"                     nitpick sledgehammer             (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F9"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F9"                      nitpick sledgehammer            (*none*) (*proof*)
                                                                      apply simp nitpick sledgehammer oops   (*none*) (*proof*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F9"                      nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F9"                      nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F9"                     nitpick sledgehammer            (*ctex*) (*no prf*)
                                                                      apply simp nitpick sledgehammer oops   (*ctex*) (*no prf*)


lemma S5:   "AxT \<and> AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer            (*none*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma S4:   "AxT \<and>           Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*none*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma KB4: "          AxB \<and> Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*ctex*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*ctex*) (*no prf*)
lemma KTB: "AxT \<and> AxB           \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*none*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma KT:   "AxT                     \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*none*) (*proof*)
                                                                       apply simp nitpick sledgehammer oops  (*none*) (*proof*)
lemma KB:   "          AxB           \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*ctex*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*ctex*) (*no prf*)
lemma K4:   "                    Ax4 \<longrightarrow> \<Turnstile>\<^sup>m F10"                     nitpick sledgehammer           (*ctex*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*ctex*) (*no prf*)
lemma K:     "                                  \<Turnstile>\<^sup>m F10"                    nitpick sledgehammer           (*ctex*) (*no prf*)
                                                                       apply simp nitpick sledgehammer oops  (*ctex*) (*no prf*)

\<comment>\<open>Summary of experiments: 
 Nitpick: ctex=84 (with simp 42, without simp 42), none=72 (with simp 36, without simp 36), unknwn=4 (with simp 2, without simp 2)
 Sledgehammer: proof=73 (with simp 38, without simp 35), no prf=87  (with simp 42, without simp 45) \<close>

\<comment>\<open>No conflicts\<close>
end 