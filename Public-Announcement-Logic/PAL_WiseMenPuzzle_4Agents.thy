(* Sebastian Reiche and Christoph Benzmüller, 2021 *)
theory PAL_WiseMenPuzzle_4Agents imports PAL_definitions

begin
 (* Parameter settings *)
 declare [[smt_solver=cvc4,smt_oracle,smt_timeout=120]]

 (*** Encoding of the wise men puzzle in PAL ***)
 consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>" d::"\<alpha>" (* Agents modeled as accessibility relations *)
 abbreviation  Agent::"\<alpha>\<Rightarrow>bool" ("\<A>") where "\<A> x \<equiv> x = a \<or> x = b \<or> x = c \<or> x = d"
 axiomatization where  group_S5: "S5Agents \<A>"

 (*** Encoding of the wise men puzzle in PAL ***)
 (* Common knowledge: At least one of a, b, c and d has a white spot *)
 consts ws::"\<alpha>\<Rightarrow>\<sigma>" 
 axiomatization where WM1: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^sup>Aws a \<^bold>\<or> \<^sup>Aws b \<^bold>\<or> \<^sup>Aws c \<^bold>\<or> \<^sup>Aws d)\<^bold>\<rfloor>" 
 axiomatization where
   (* Common knowledge: If x does not have a white spot then y know this *)
   WM2ab: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ac: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ad: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
   WM2ba: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2bd: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
   WM2ca: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cb: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2cd: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>d (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
   WM2da: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" and
   WM2db: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" and
   WM2dc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws d) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws d))))\<^bold>\<rfloor>" 

 (* Positive introspection principles are implied *)
 lemma WM2ab': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> \<^bold>K\<^sub>b (\<^sup>Aws a))\<^bold>\<rfloor>" using WM2ab group_S5 unfolding Defs by (smt (z3))
 lemma WM2ac': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> \<^bold>K\<^sub>c (\<^sup>Aws a))\<^bold>\<rfloor>" using WM2ac group_S5 unfolding Defs by (smt (z3))
 lemma WM2aD': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> \<^bold>K\<^sub>d (\<^sup>Aws a))\<^bold>\<rfloor>" using WM2ad group_S5 unfolding Defs by (smt (z3))
 lemma WM2ba': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> \<^bold>K\<^sub>a (\<^sup>Aws b))\<^bold>\<rfloor>" using WM2ba group_S5 unfolding Defs by (smt (z3))
 lemma WM2bc': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> \<^bold>K\<^sub>c (\<^sup>Aws b))\<^bold>\<rfloor>" using WM2bc group_S5 unfolding Defs by (smt (z3))
 lemma WM2bd': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> \<^bold>K\<^sub>d (\<^sup>Aws b))\<^bold>\<rfloor>" using WM2bd group_S5 unfolding Defs by (smt (z3))
 lemma WM2ca': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> \<^bold>K\<^sub>a (\<^sup>Aws c))\<^bold>\<rfloor>" using WM2ca group_S5 unfolding Defs by (smt (z3))
 lemma WM2cb': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> \<^bold>K\<^sub>b (\<^sup>Aws c))\<^bold>\<rfloor>" using WM2cb group_S5 unfolding Defs by (smt (z3))
 lemma WM2cd': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> \<^bold>K\<^sub>d (\<^sup>Aws c))\<^bold>\<rfloor>" using WM2cd group_S5 unfolding Defs by (smt (z3))
 lemma WM2da': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws d) \<^bold>\<rightarrow> \<^bold>K\<^sub>a (\<^sup>Aws d))\<^bold>\<rfloor>" using WM2da group_S5 unfolding Defs by (smt (z3))
 lemma WM2db': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws d) \<^bold>\<rightarrow> \<^bold>K\<^sub>b (\<^sup>Aws d))\<^bold>\<rfloor>" using WM2db group_S5 unfolding Defs by (smt (z3))
 lemma WM2dc': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws d) \<^bold>\<rightarrow> \<^bold>K\<^sub>c (\<^sup>Aws d))\<^bold>\<rfloor>" using WM2dc group_S5 unfolding Defs by (smt (z3))

 (* Automated solutions of the Wise Men Puzzle with 4 Agents*)
 theorem whitespot_d: "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>a(\<^sup>Aws a)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>b(\<^sup>Aws b)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>c(\<^sup>Aws c)\<^bold>](\<^bold>K\<^sub>d (\<^sup>Aws d))))\<^bold>\<rfloor>" 
   using WM1 WM2ba WM2ca WM2cb WM2da WM2db WM2dc
   unfolding Defs by (smt (verit))

 theorem whitespot_d': 
     "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>a (\<^sup>Aws a)) \<^bold>\<or> (\<^bold>K\<^sub>a (\<^bold>\<not>\<^sup>Aws a)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>b (\<^sup>Aws b)) \<^bold>\<or> (\<^bold>K\<^sub>b (\<^bold>\<not>\<^sup>Aws b)))\<^bold>](
        \<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>c (\<^sup>Aws c)) \<^bold>\<or> (\<^bold>K\<^sub>c (\<^bold>\<not>\<^sup>Aws c)))\<^bold>](\<^bold>K\<^sub>d (\<^sup>Aws d))))\<^bold>\<rfloor>" 
   using whitespot_d 
   unfolding Defs sledgehammer[verbose]() (* finds proof *)
   (* reconstruction timeout *)
   oops

 (* Consistency confirmed by nitpick *)
 lemma True nitpick [satisfy] oops  (* model found *)
end






