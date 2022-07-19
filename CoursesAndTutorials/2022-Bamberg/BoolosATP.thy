theory BoolosATP imports Main
begin

typedecl i
consts 
 e :: "i"  (* one *) 
 s :: "i\<Rightarrow>i"  (* successor function *)
 F :: "i\<Rightarrow>i\<Rightarrow>i"  (* binary function; axiomatised below as Ackermann function *)
 D :: "i\<Rightarrow>bool"  (* arbitrary uninterpreted unary predicate *)

axiomatization where 
    A1: "\<forall>n. F n e = s e"  (* Axiom for Ackermann function F *)
and A2: "\<forall>y. F e (s y) = s (s (F e y))"  (* Axiom for Ackermann function F *)
and A3: "\<forall>x y. F (s x) (s y) = F x (F (s x) y)"  (* Axiom for Ackermann function F *)
and A4: "D e"  (* D holds for one *)
and A5: "\<forall>x. D x \<longrightarrow> D (s x)" (* if D holds for x it also holds for the successor of x *)

lemma "D (F (s (s (s (s e)))) (s (s (s (s e)))))" sledgehammer oops (* no proof; hopeless! *)

definition isIndSet where "isIndSet X \<equiv> (X e) \<and> (\<forall>x. X x \<longrightarrow> X (s x))"  (* X is inductive *)
definition N where "N x \<equiv> (\<forall>X::i\<Rightarrow>bool. isIndSet X \<longrightarrow> X x)"   (* N is smallest inductive set *)
definition P where "P x y \<equiv> N (F x y)"   (* P(x,y) iff F(x,y) is in N *)

lemma "D (F (s (s (s (s e)))) (s (s (s (s e)))))"  (* ATPs can now proof this: using the Defs *)
  sledgehammer  (* proof found *)
  by (metis A1 A2 A3 A4 A5 N_def P_def isIndSet_def)  (* proof reconstruction succeeds *)
end 
