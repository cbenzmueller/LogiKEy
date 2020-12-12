theory Relations imports HOMML                          (* By Christoph Benzmüller, 2018 *)
begin                     
 (*Some useful properties and operations on (accessibility) relations*)
  definition reflexive :: "\<alpha>\<Rightarrow>bool" where "reflexive R \<equiv> \<forall>x. R x x"
  definition symmetric :: "\<alpha>\<Rightarrow>bool" where "symmetric R \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"
  definition transitive :: "\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
  definition euclidean :: "\<alpha>\<Rightarrow>bool" where "euclidean R \<equiv> \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
  definition intersection_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "intersection_rel R Q \<equiv> \<lambda>u v. R u v \<and> Q u v"
  definition union_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" where "union_rel R Q \<equiv> \<lambda>u v. R u v \<or> Q u v"
  definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
  definition inverse_rel :: "\<alpha>\<Rightarrow>\<alpha>" where "inverse_rel R \<equiv> \<lambda>u v. R v u"

 (*In HOL the transitive closure of a relation can be defined in a single line.*)
  definition tc :: "\<alpha>\<Rightarrow>\<alpha>" where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"

 (*Adding the above definitions to the set of definitions Defs.*) 
 declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] euclidean_def[Defs] 
   intersection_rel_def[Defs] union_rel_def[Defs] sub_rel_def[Defs] inverse_rel_def[Defs] 

 (*Some useful lemmata.*) 
  lemma trans_tc: "transitive (tc R)" unfolding Defs tc_def by metis
  lemma trans_inv_tc: "transitive (inverse_rel (tc R))" unfolding Defs tc_def by metis
  lemma sub_rel_tc: "symmetric R \<longrightarrow> (sub_rel R (inverse_rel (tc R)))" 
    unfolding Defs tc_def by metis
  lemma sub_rel_tc_tc: "symmetric R \<longrightarrow> (sub_rel (tc R) (inverse_rel (tc R)))" 
    using sub_rel_def sub_rel_tc tc_def trans_inv_tc by fastforce
  lemma symm_tc: "symmetric R \<longrightarrow> symmetric (tc R)"  sledgehammer [verbose]  nitpick 
    using inverse_rel_def sub_rel_def sub_rel_tc_tc symmetric_def by auto
end