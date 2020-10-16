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
       
end
