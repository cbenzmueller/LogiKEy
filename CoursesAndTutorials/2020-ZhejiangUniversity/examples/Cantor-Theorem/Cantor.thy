theory Cantor  imports Main 
  
  
begin  
typedecl i  

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
