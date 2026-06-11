theory IO3_Ex_C
  imports IO3
begin
(* Chisholm *)

consts h :: "\<tau>"
consts t :: "\<tau>"

context
  assumes ax0: "\<^bold>\<top> \<^bold>\<preceq> h"
      and ax1: "h \<^bold>\<preceq> t"
      and ax2: "(\<^bold>\<not>h) \<^bold>\<preceq> (\<^bold>\<not>t)"
begin

lemma ch1: "\<^bold>\<diamond>\<^sup>3\<^sub>o \<^bold>\<top> \<^bold>\<le> h"
  using IO3_from_norm[OF ax0] by simp

lemma ch2: "\<^bold>\<diamond>\<^sup>3\<^sub>o \<^bold>\<top> \<^bold>\<le> t" 
  using IO3T IO3_from_norm ax1 ch1 by blast

lemma ch3: "\<^bold>\<diamond>\<^sup>3\<^sub>o (\<^bold>\<not>h) \<^bold>\<le> (\<^bold>\<not>t)"
  using IO3_from_norm[OF ax2] by simp

lemma ch4: "\<^bold>\<diamond>\<^sup>3\<^sub>o (\<^bold>\<not>h) \<^bold>\<le> \<^bold>\<bottom>" 
  by (metis IO3_mono IO_LogicalBase.monotone_def 
      ch2 ch3 setnot_def settrue_def)

end
end

