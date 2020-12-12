theory WiseMenPuzzle imports HOMML Relations                 (* By Christoph Benzmüller, 2018 *)
begin 
  consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>"  (*Wise men modeled as accessibility relations.*)
 (*Reflexivity, transitivity and euclideaness is postulated for these relations.*)
  axiomatization where
   knowl_abc: "(x = a \<or> x = b \<or> x = c) \<Longrightarrow> (reflexive x \<and> transitive x \<and> euclidean x)" 
 (*Eabc \<phi> stands for "Everyone in group {a,b,c} knows \<phi>".*)
  definition Eabc where "Eabc \<equiv> union_rel (union_rel a b) c"
 (*Cabc \<phi> stands for "The common knowledge of group {a,b,c}".*)
  definition Cabc :: "i\<Rightarrow>i\<Rightarrow>bool" where "Cabc \<equiv> tc Eabc"
 (*Cabc is reflexive, transitive and euclidean; i.e. it is a knowledge operator.*)
  lemma refl_Cabc: "reflexive Cabc" using Cabc_def Eabc_def knowl_abc Defs tc_def by smt
  lemma symm_C_abc: "symmetric Cabc" using Cabc_def Eabc_def knowl_abc symm_tc Defs by smt
  lemma eucl_Cabc: "euclidean Cabc" using Cabc_def Eabc_def knowl_abc symm_C_abc Defs tc_def by smt
 (*We are now ready to model and automate the wise men puzzle.*)
  consts ws :: "\<alpha>\<Rightarrow>\<sigma>" (*ws a: a has a white spot.*) wise :: "\<alpha>\<Rightarrow>bool" (*wise a: a is a wise man.*)
  axiomatization where 
   A0: "wise a \<and> wise b \<and> wise c" (*a, b and c are wise men.*) and
   (*Common knowledge: at least one of a, b and c has a white spot *)
   A1: "\<lfloor>\<^bold>\<box>Cabc (ws a \<^bold>\<or> ws b \<^bold>\<or> ws c)\<rfloor>" and
   (*Common knowledge: if x has a white spot then y can see this (and hence know this).*)
   A2: "wise x \<and> wise y \<and> x \<noteq> y \<Longrightarrow> \<lfloor>\<^bold>\<box>Cabc (ws x \<^bold>\<rightarrow> \<^bold>\<box>y (ws x))\<rfloor>" and
   (*Common knowledge: if x not has a white spot then y can see this (hence know this) *)
   A3: "wise x \<and> wise y \<and> x \<noteq> y \<Longrightarrow> \<lfloor>\<^bold>\<box>Cabc (\<^bold>\<not>(ws x) \<^bold>\<rightarrow> \<^bold>\<box>y (\<^bold>\<not>(ws x)))\<rfloor>" and
   (*Common knowledge: a does not know whether he has a white spot.*)
   A4: "\<lfloor>(\<^bold>\<box>Cabc (\<^bold>\<not>(\<^bold>\<box>a (ws a))))\<rfloor>"  and
   (*Common knowledge: b does not know whether he has a white spot.*)
   A5: "\<lfloor>(\<^bold>\<box>Cabc \<^bold>\<not>(\<^bold>\<box>b (ws b)))\<rfloor>"
  theorem  (*c knows he has a white spot.*)
   T1: "\<lfloor>(\<^bold>\<box>c (ws c))\<rfloor>" using A0 A1 A3 A4 A5 refl_Cabc unfolding Defs sledgehammer()
    by metis
lemma True nitpick [satisfy,user_axioms,expect=genuine,show_all] oops (*Consistency confirmed*)
end