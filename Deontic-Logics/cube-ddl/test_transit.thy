theory test_transit  (* Christoph Benzmüller, Xavier Parent, 2022  *)

imports cube

begin

lemma 
  assumes Sp: "\<lfloor>( \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
      and Trans: "\<lfloor>(\<^bold>\<not>\<odot><\<^bold>\<not>\<phi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<and> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|(\<psi>\<^bold>\<or>\<xi>)>)\<^bold>\<rightarrow>\<^bold>\<not>\<odot><\<^bold>\<not>\<phi>|(\<phi>\<^bold>\<or>\<xi>)>\<rfloor>"
  shows wDR: "\<lfloor> \<odot><\<^bold>\<not>\<psi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> (\<odot><\<^bold>\<not>\<psi>|\<psi>> \<^bold>\<or> \<odot><\<^bold>\<not>\<psi>|\<phi>>)\<rfloor>"     
  nitpick[card=3] (* counterexample found *) 
  oops


end