theory BoolosATP2 imports Main
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

definition isIndSet where (* X is inductive (over e and s) *)
  "isIndSet \<equiv> \<lambda>X. (X e) \<and> (\<forall>x. X x \<longrightarrow> X (s x))"  
definition P where (* P(x,y) iff F(x,y) is in smallest inductive set (over e and s) *)
  "P \<equiv> \<lambda>x y. (\<lambda>z. (\<forall>X::i\<Rightarrow>bool. isIndSet X \<longrightarrow> X z)) (F x y)" 

lemma "D (F (s (s (s (s e)))) (s (s (s (s e)))))"  (* ATPs can now proof this: using the Defs *)
  sledgehammer  (* proof found *)
  by (metis A1 A2 A3 A4 A5 P_def isIndSet_def)     (* proof reconstruction succeeds *)
end 
