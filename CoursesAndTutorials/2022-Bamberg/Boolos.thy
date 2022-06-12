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


lemma "D (F (s (s (s (s e)))) (s (s (s (s e)))))"
  using A1 A2 A3 A4 A5 sledgehammer[vampire remote_leo2 remote_leo3, overlord]()
  oops

definition induct where "induct X \<equiv> (X e) \<and> (\<forall>x. X x \<longrightarrow> X (s x))"  (*X is is higher-order*)
definition N where "N x \<equiv> (\<forall>X::i\<Rightarrow>bool. induct X \<longrightarrow> X x)"    (*Higher-order quantifier*)
definition P1 where "P1 x y \<equiv> N (F x y)"
definition P2 where "P2 x \<equiv> (\<forall>z. N z \<longrightarrow> P1 x z)"

lemma L1: "\<forall>X::i\<Rightarrow>bool. induct X \<longrightarrow> (\<forall>z. N z \<longrightarrow> X z)" (*Higher-order quantifier*)
  using N_def by fastforce 
lemma L2: "induct N" by (metis N_def induct_def)
lemma L3: "induct D" by (simp add: A4 A5 induct_def)
lemma L4: "N (s (s (s (s e))))" by (metis L2 induct_def)

lemma L5: "P1 e e" by (metis A1 L2 P1_def induct_def)
lemma L6: "\<forall>x. P1 e x \<longrightarrow> P1 e (s x)" by (metis A2 P1_def induct_def L2)
lemma L7: "induct (P1 e)" using induct_def L5 L6 by auto

lemma L8: "\<forall>x. P1 (s x) e" by (metis A1 P1_def induct_def L2)
lemma L9: "P2 e" by (metis L1 L7 P2_def)
lemma L10: "\<forall>x. P2 x \<longrightarrow> (\<forall>y. P1 (s x) y \<longrightarrow> P1 (s x) (s y))" by (metis A3 P1_def P2_def)
lemma L11: "\<forall>x. P2 x \<longrightarrow> P2 (s x)" by (metis L1 L10 L8 P2_def induct_def)
lemma L12: "induct P2" by (simp add: L11 L9 induct_def)

lemma L13: "\<forall>x y. N x \<and> N y \<longrightarrow> N (F x y)" by (metis L1 L12 P1_def P2_def)

lemma L14: "D (F (s (s (s (s e)))) (s (s (s (s e)))))" by (metis L1 L13 L3 L4)



lemma "((\<forall>n. F n e = s e) \<and> (\<forall>y. F e (s y) = s (s (F e y))) \<and>
        (\<forall>x y. F (s x) (s y) = F x (F (s x) y)) \<and> (D e) \<and> (\<forall>x. D x \<longrightarrow> D (s x)))
       \<longrightarrow> D (F (s (s (s (s e)))) (s (s (s (s e)))))"
  sledgehammer[remote_vampire remote_leo2 remote_leo3 vampire cvc4 z3, overlord]()
  oops 

lemma "a \<and> (a \<longrightarrow> b) \<longrightarrow> b" sledgehammer() by simp   (*proof in milliseconds*)

lemma "(a \<and> (a \<longrightarrow> b) \<longrightarrow> b) \<and>
       ((\<forall>n. F n e = s e) \<and> (\<forall>y. F e (s y) = s (s (F e y))) \<and>
        (\<forall>x y. F (s x) (s y) = F x (F (s x) y)) \<and> (D e) \<and> (\<forall>x. D x \<longrightarrow> D (s x)))
       \<longrightarrow> D (F (s (s (s (s e)))) (s (s (s (s e)))))"
  sledgehammer() nitpick nunchaku  (*all provers fail!, including CVC4 and Z3*)
  oops

lemma "(a \<and> (a \<longrightarrow> b) \<longrightarrow> b) \<or>
       ((\<forall>n. F n e = s e) \<and> (\<forall>y. F e (s y) = s (s (F e y))) \<and>
        (\<forall>x y. F (s x) (s y) = F x (F (s x) y)) \<and> (D e) \<and> (\<forall>x. D x \<longrightarrow> D (s x)))
       \<longrightarrow> D (F (s (s (s (s e)))) (s (s (s (s e)))))"
  sledgehammer() nitpick nunchaku  (*all provers fail!, including CVC4 and Z3*)
  oops


end