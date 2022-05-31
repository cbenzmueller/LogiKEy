theory Cantor  imports Main 
 
begin  

declare [[show_types]]

typedecl i

consts 
  a::"i"     (* constant symbol of type i - denoting an object in the domain for type i*)
  f::"i\<Rightarrow>i"  (* constant symbol of function type i\<rightarrow>i - denoting an function in the domain 
                for type i\<rightarrow>i*)
  p::"i\<Rightarrow>bool"  (* constant symbol of predicate type i\<rightarrow>bool - denoting an predicate/set in 
                   the domain for type i\<rightarrow>bool*)
 
lemma "(\<lambda>g. \<lambda>y. g (g y)) f a = (f (f a))" by simp

lemma "(\<lambda>x. p x) a = (p a)" by simp

lemma "(\<lambda>x. p x)  = p" by simp

lemma "(\<lambda>y. ((\<lambda>x. p x) y)) a = ((\<lambda>x. p x) a)" by simp

lemma "(\<lambda>y. ((\<lambda>x. p x) y)) a = (p a)" by simp


consts d::bool c::bool

lemma "(d \<or> \<not>d) \<longrightarrow> d" sledgehammer nitpick[show_all] oops

lemma "(d \<and> c) \<longrightarrow> (c \<longrightarrow> d)" by simp

lemma "(d \<and> c) \<longrightarrow> (c \<longrightarrow> d)" 
proof 
  assume 1: "d \<and> c"
  have 2: "d" by (simp add: "1")
  have 3: "\<not>c \<or> d" by (simp add: "2")
  show "c \<longrightarrow> d" sledgehammer (3)
    using "3" by fastforce
qed


lemma "(\<forall>x. p x) \<longrightarrow> (\<exists>y. p y)" sledgehammer nitpick[show_all]  oops

lemma "(\<forall>x. p x) \<longrightarrow> (\<exists>y. p y)" proof
   assume 1: "(\<forall>x. p x)"
   fix a::i 
    have 2: "p a" by (simp add: "1")
    have 3: "\<exists>y. p y" using "2" by auto
  show ?thesis sledgehammer

lemma "(\<exists>y. p y) \<longrightarrow> (\<forall>x. p x)" sledgehammer nitpick[show_all,card=2] oops


(* Simple Example (Exercise 2)*)
definition imp ::"bool\<Rightarrow>bool\<Rightarrow>bool" ("\<^bold>\<Rightarrow>") where "\<^bold>\<Rightarrow> \<equiv> \<lambda>x. \<lambda>y.((\<not>x) \<or> y)"
definition leq ::"i\<Rightarrow>i\<Rightarrow>bool" ("\<doteq>") where "\<doteq> \<equiv> \<lambda>x.\<lambda>y.(\<forall>P. (\<^bold>\<Rightarrow> (P x) (P y)))"


lemma "\<forall>x. ((\<doteq> x) x)"  unfolding leq_def imp_def by simp

lemma "\<forall>x. ((\<lambda>x.\<lambda>y.(\<forall>P. ((\<lambda>x.\<lambda>y.((\<not>x) \<or> y)) (P x) (P y)))) x x)"   by simp

lemma "\<forall>x. \<forall>P. \<not> P x \<or> P x" by simp

lemma "All (\<lambda> x. ((\<lambda>x.\<lambda>y.(\<forall>P. ((\<lambda>x.\<lambda>y.((\<not>x) \<or> y)) (P x) (P y)))) x x))" by simp



(*Church Numerals (Exercise 1)*)
type_synonym num = "(i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i"

definition one ::num   ("1") where "1 \<equiv> (\<lambda>f. \<lambda>x. f x)"
definition two ::num   ("2") where "2 \<equiv> (\<lambda>f. \<lambda>x. f (f x))"
definition three ::num ("3") where "3 \<equiv> (\<lambda>f. \<lambda>x. f (f (f x)))"
definition four ::num  ("4") where "4 \<equiv> (\<lambda>f. \<lambda>x. f ( f (f (f x))))"
definition five ::num  ("5") where "5 \<equiv> (\<lambda>f. \<lambda>x. f (f ( f (f (f x)))))"

definition plus ::"num\<Rightarrow>num\<Rightarrow>num"   ("+") where "+ \<equiv> \<lambda>u.\<lambda>v.(\<lambda>f.\<lambda>y.((u f) ((v f) y)))"
definition mult ::"num\<Rightarrow>num\<Rightarrow>num"   ("*") where "* \<equiv> \<lambda>u.\<lambda>v.(\<lambda>f.\<lambda>y.(u (v f)) y)"

named_theorems Defs declare one_def two_def three_def four_def five_def plus_def mult_def

lemma Homework1: "t = (+ 2 3)" unfolding two_def three_def plus_def oops


(* Some first tests *)    
theorem Test1: "(\<exists>x::i. \<forall>y::i. x = y) \<longrightarrow> (\<forall>x::i. \<exists>y::i. x = y) " 
  nitpick
  sledgehammer
  sledgehammer [remote_leo2]
  by auto  
   
theorem Test2: "(\<forall>x::i. \<exists>y::i. x = y) \<longrightarrow> (\<exists>x::i. \<forall>y::i. x = y) "   
  nitpick [card=2]
  sledgehammer
  sledgehammer [remote_leo2]
  oops  
  
theorem Test3: "\<exists>g::i\<Rightarrow>bool. \<forall>x::i. g(x)" 
  nitpick
  sledgehammer
  sledgehammer [remote_leo2 remote_satallax remote_vampire]
  by auto

(* The surjective Cantor theorem *)  
theorem Cantor: "\<not>(\<exists>f::i\<Rightarrow>(i\<Rightarrow>bool). \<forall>g::i\<Rightarrow>bool. \<exists>x::i. f x = g)" 
  nitpick
  sledgehammer
  sledgehammer [remote_leo2 remote_satallax]  
  oops  


(* Adapted from Makarius Wenzel *)
lemma CantorSurjective: "\<not>(\<exists>f::i\<Rightarrow>i\<Rightarrow>bool.\<forall>p.\<exists>x. f x = p)" 
proof 
  assume "\<exists>f::i\<Rightarrow>i\<Rightarrow>bool.\<forall>p.\<exists>x. f x = p"
  then obtain f :: "i\<Rightarrow>i\<Rightarrow>bool" 
    where 1: "\<forall>p.\<exists>x. f x = p" by blast
  let ?D = "\<lambda>x. \<not> f x x"
  have "\<exists>x. ?D = f x" by (metis "1")
  then obtain a::i 
    where "?D = f a" by blast
  then have "?D a \<longleftrightarrow> f a a" by metis
  then have "\<not> f a a \<longleftrightarrow> f a a" by blast
  then show False by blast
qed


(* By David Fuenmayor and Christoph Benzmüller 2020: avoids refutation  argument *)
lemma CantorSurjectiveTraditional: "\<not>(\<exists>f::i\<Rightarrow>i\<Rightarrow>bool.\<forall>p.\<exists>x. f x = p)"    
proof -
 { fix F::"i\<Rightarrow>i\<Rightarrow>bool"
    have "\<forall>w. \<exists>v. (F v v) \<longleftrightarrow> (F w v)" proof - (*also automatically:  by auto*)
    { fix w::i
      let ?v=w
      have "(F w w) \<longleftrightarrow> (F w w)" by simp    (*tautology*)
      hence "(F ?v ?v) \<longleftrightarrow> (F w ?v)" by simp    (*(partial) var substitution*)
      hence "\<exists>v. (F v v) \<longleftrightarrow> (F w v)" by blast (*Ex-I*)
    } thus ?thesis by simp qed
    hence "\<forall>w. \<exists>v. \<not>(F v v) \<longleftrightarrow> \<not>(F w v)" by simp (*replacement*)
    hence "let P=(\<lambda>x. \<not>F x x) in \<forall>w. \<exists>v. (P v) \<longleftrightarrow> \<not>(F w v)" by simp (*beta-exp + replacement*)
    hence "\<exists>p. \<forall>w. \<exists>v::i. (p v) \<longleftrightarrow> \<not>(F w v)" by auto (*Ex-I*) 
    hence "\<exists>p. \<forall>w. \<not>(\<forall>v::i. (p v) \<longleftrightarrow> (F w v))" by simp
    hence "\<exists>p. \<forall>w. \<not>(p = F w)" by metis
    hence "\<exists>p. \<forall>w. \<not>(F w = p)" by metis
    hence "\<exists>p. \<not>(\<exists>w. F w = p)" by simp
    hence "\<not>(\<forall>p. \<exists>w. F w = p)" by simp
  } thus ?thesis  by simp
qed
       
end
