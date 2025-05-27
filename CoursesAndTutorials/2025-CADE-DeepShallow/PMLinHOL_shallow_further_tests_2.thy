theory PMLinHOL_shallow_further_tests_2 imports PMLinHOL_shallow_tests                    (* Christoph Benzmüller, 2025 *)
begin             
\<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
\<comment>\<open>Test with semantic conditions\<close>
abbreviation(input) refl ("\<r>") where "\<r> \<equiv> \<lambda>R. reflexive R"
abbreviation(input) sym ("\<s>") where "\<s> \<equiv> \<lambda>R.  symmetric R"
abbreviation(input) tra ("\<t>") where "\<t> \<equiv> \<lambda>R.  transitive R"

consts \<phi>::\<sigma> \<psi>::\<sigma>
abbreviation(input) "F1   \<equiv> (\<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<supset>\<^sup>s \<diamond>\<^sup>s\<phi>"                                             \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2   \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"                                      \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3   \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s\<phi>"                                             \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4   \<equiv> (\<box>\<^sup>s(\<diamond>\<^sup>s(\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)))) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"                         \<comment>\<open>holds in KB\<close>
abbreviation(input) "F5   \<equiv> (\<diamond>\<^sup>s(\<phi> \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))) \<supset>\<^sup>s ((\<diamond>\<^sup>s\<phi>) \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))"               \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6   \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>)) \<and>\<^sup>s (\<diamond>\<^sup>s(\<box>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<diamond>\<^sup>s\<psi>)"     \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7   \<equiv> (\<diamond>\<^sup>s\<phi>) \<supset>\<^sup>s (\<box>\<^sup>s(\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>))"                                   \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8   \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s (\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>)"                                   \<comment>\<open>holds in KT and in KB\<close>
abbreviation(input) "F9   \<equiv> ((\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s \<phi>)))) \<supset>\<^sup>s \<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)"         \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<box>\<^sup>s\<psi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<box>\<^sup>s\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

lemma S5:   "\<forall>w:W.  \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer            (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R           \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma KT:   "\<forall>w:W. \<r> R                    \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.           \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops    (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                    \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma K:     "\<forall>w:W.                                (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "\<forall>w:W.           \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer          (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R           \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                            apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<forall>w:W. \<r> R                    \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.           \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                            apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K4:   "\<forall>w:W.                    \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                                (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.           \<s> R         \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.          \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K4:   "\<forall>w:W.                    \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma K:     "\<forall>w:W.                                (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer            (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.          \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.          \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer            (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KB:   "\<forall>w:W.          \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB:   "\<forall>w:W.         \<s> R           \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                            apply simp nitpick sledgehammer oops  (*unkn*)(*proof*)
lemma K4:   "\<forall>w:W.                    \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer          (*ctex*)(*no prf*)
                                                                            apply simp nitpick sledgehammer oops  (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                                (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  nitpick sledgehammer          (*ctex*)(*no prf*)
                                                                             apply simp nitpick sledgehammer oops (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer            (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*unkn*)(*proof*)
                                                                           apply simp nitpick sledgehammer oops   (*unkn*)(*proof*)
lemma KB:   "\<forall>w:W.           \<s> R         \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops   (*ctex*)(*no prf*)


lemma S5:   "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops    (*unkn*)(*proof*)
lemma S4:   "\<forall>w:W. \<r> R \<and>          \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KB4: "\<forall>w:W.          \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KT:   "\<forall>w:W. \<r> R                   \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*unkn*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*unkn*)(*proof*)
lemma KB:   "\<forall>w:W.          \<s> R          \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K4:   "\<forall>w:W.                   \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)
lemma K:     "\<forall>w:W.                               (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  nitpick sledgehammer           (*ctex*)(*no prf*)
                                                                           apply simp nitpick sledgehammer oops     (*ctex*)(*no prf*)

\<comment>\<open>Summary of experiments: 
 Nitpick: ctex=84 (with simp 42, without simp 42), none=0, unknwn=76 (with simp 38, without simp 38) 
 Sledgehammer: proof=66 (with simp 38, without simp 28), no prf=94 (with simp 42, without simp 52) \<close>

\<comment>\<open>No conflicts\<close>
end