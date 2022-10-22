theory mere_addition imports cube          (* Christoph Benzmüller, Xavier Parent, 2022  *)

begin (* Some Tests*)





lemma assumes "transitivity"    
  shows  Transit: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  sledgehammer (* proof found *)
  nitpick [show_all] (* no counterexample found *) 
  