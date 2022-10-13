theory Boolos imports Main
begin

typedecl i
consts 
 e :: "i"  (*one*) 
 s :: "i \<Rightarrow> i"  (*successor*)
 F :: "i \<Rightarrow> i \<Rightarrow> i" (*binary function; will be axiomatised as Ackermann function*)
 D :: "i \<Rightarrow> bool" (*arbitrary unary predicate*)

axiomatization where 
  A1: "\<forall>n. F n e = s e" and 
  A2: "\<forall>y. F e (s y) = s (s (F e y))" and 
  A3: "\<forall>x y. F (s x) (s y) = F x (F (s x) y)" and 
  A4: "D e" and 
  A5: "\<forall>x. D x \<longrightarrow> D (s x)"

definition induct where "induct X \<equiv> (X e) \<and> (\<forall>x. X x \<longrightarrow> X (s x))"  (*X inductively def. Pred.*)
definition N where "N x \<equiv> (\<forall>X::i\<Rightarrow>bool. induct X \<longrightarrow> X x)"    (*Higher-order quantifier*)
definition P1 where "P1 x y \<equiv> N (F x y)"
definition P2 where "P2 x \<equiv> (\<forall>z. N z \<longrightarrow> P1 x z)"

theorem Boolos: "D (F (s (s (s (s e)))) (s (s (s (s e)))))"
proof- 
  have L1: "\<forall>X::i\<Rightarrow>bool. induct X \<longrightarrow> (\<forall>z. N z \<longrightarrow> X z)" using N_def by fastforce 
  have L2: "induct N" by (metis N_def induct_def)
  have L3: "induct D" by (simp add: A4 A5 induct_def)
  have L4: "N (s (s (s (s e))))" by (metis L2 induct_def)
  have L5: "P1 e e" by (metis A1 L2 P1_def induct_def)
  have L6: "\<forall>x. P1 e x \<longrightarrow> P1 e (s x)" by (metis A2 P1_def induct_def L2)
  have L7: "induct (P1 e)" using induct_def L5 L6 by auto
  have L8: "\<forall>x. P1 (s x) e" by (metis A1 P1_def induct_def L2)
  have L9: "P2 e" by (metis L1 L7 P2_def)
  have L10: "\<forall>x. P2 x \<longrightarrow> (\<forall>y. P1 (s x) y \<longrightarrow> P1 (s x) (s y))" by (metis A3 P1_def P2_def)
  have L11: "\<forall>x. P2 x \<longrightarrow> P2 (s x)" by (metis L1 L10 L8 P2_def induct_def)
  have L12: "induct P2" by (simp add: L11 L9 induct_def)
  thus ?thesis using L3 L4 N_def P1_def P2_def by blast 
qed

end