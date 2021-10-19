(* Sebastian Reiche and Christoph Benzmüller, 2021 *)
theory PAL_WiseMenPuzzle imports PAL_definitions

begin
 (* Parameter settings *)
 declare [[smt_solver=cvc4,smt_oracle,smt_timeout=120]]

 (*** Encoding of the wise men puzzle in PAL ***)
 (* Agents *)
 consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>" (* Agents modeled as accessibility relations *)
 abbreviation  Agent::"\<alpha>\<Rightarrow>bool" ("\<A>") where "\<A> x \<equiv> x = a \<or> x = b \<or> x = c"
 axiomatization where  group_S5: "S5Agents \<A>"

 (* Common knowledge: At least one of a, b and c has a white spot *)
 consts ws::"\<alpha>\<Rightarrow>\<sigma>" 
 axiomatization where WM1: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^sup>Aws a \<^bold>\<or> \<^sup>Aws b \<^bold>\<or> \<^sup>Aws c)\<^bold>\<rfloor>" 

 axiomatization where
   (* Common knowledge: If x does not have a white spot then y know this *)
   WM2ab: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ac: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ba: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2ca: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cb: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" 

 (* Positive introspection principles are implied *)
 lemma WM2ab': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^sup>Aws a)))\<^bold>\<rfloor>" using WM2ab group_S5 unfolding Defs by metis
 lemma WM2ac': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^sup>Aws a)))\<^bold>\<rfloor>" using WM2ac group_S5 unfolding Defs by metis
 lemma WM2ba': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^sup>Aws b)))\<^bold>\<rfloor>" using WM2ba group_S5 unfolding Defs by metis
 lemma WM2bc': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^sup>Aws b)))\<^bold>\<rfloor>" using WM2bc group_S5 unfolding Defs by metis
 lemma WM2ca': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^sup>Aws c)))\<^bold>\<rfloor>" using WM2ca group_S5 unfolding Defs by metis
 lemma WM2cb': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^sup>Aws c)))\<^bold>\<rfloor>" using WM2cb group_S5 unfolding Defs by metis

 (* Automated solutions of the Wise Men Puzzle *)
 theorem whitespot_c_1: "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>a(\<^sup>Aws a)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>b(\<^sup>Aws b)\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb unfolding Defs by (smt (verit)) 

 theorem whitespot_c_2: 
   "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>a (\<^sup>Aws a)) \<^bold>\<or> (\<^bold>K\<^sub>a (\<^bold>\<not>\<^sup>Aws a)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>b (\<^sup>Aws b)) \<^bold>\<or> (\<^bold>K\<^sub>b (\<^bold>\<not>\<^sup>Aws b)))\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb unfolding Defs by (smt (verit)) 
   
 (* Consistency confirmed by nitpick *)
 lemma True nitpick [satisfy,show_all] oops  (* model found *)
end