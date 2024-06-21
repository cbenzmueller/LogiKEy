theory paradoxes  imports SDL  (*paradoxes*)
begin
(*Unimportant.*) sledgehammer_params [max_facts=20,timeout=20,verbose] 
(*Unimportant.*) nitpick_params [user_axioms,show_all,dont_box] 


lemma MP: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma Nec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>OB A\<rfloor>" by simp

lemma RCOM: "\<lfloor>A \<^bold>\<rightarrow> B \<rfloor> \<Longrightarrow> \<lfloor>OB A \<^bold>\<rightarrow> OB B\<rfloor>" 
sledgehammer oops

lemma "\<lfloor>(OB A) \<^bold>\<rightarrow> A\<rfloor>" 
nitpick oops

lemma "\<lfloor>OB (A\<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (OB A \<^bold>\<rightarrow> OB B) \<rfloor>"  
sledgehammer oops


lemma "\<lfloor>OB A \<^bold>\<rightarrow> OB (A \<^bold>\<or> B) \<rfloor>"  
sledgehammer

(*Chisholm*)

consts go::\<sigma> tell::\<sigma> 

nitpick_params [user_axioms,expect=genuine,show_all,format=2] (*settings for the model finder*)

(*It ought to be that Jones goes to assist his neighbors.*)
  abbreviation  "D1 \<equiv> OB go"  
(*It ought to be that if Jones goes, then he tells them he is coming.*)
  abbreviation  "D2w \<equiv> OB (go \<^bold>\<rightarrow> tell)"  
  abbreviation  "D2n \<equiv> go \<^bold>\<rightarrow> OB tell"  
(*If Jones doesn't go, then he ought not tell them he is coming.*)
  abbreviation  "D3w \<equiv> OB (\<not>go \<^bold>\<rightarrow> \<^bold>\<not>tell)" 
  abbreviation  "D3n \<equiv> \<^bold>\<not>go \<^bold>\<rightarrow> OB (\<not>tell)" 
(*Jones doesn't go. (This is encoded as a locally valid statement.)*)
  abbreviation  "D4 \<equiv> \<^bold>\<not>go" 

lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by auto (*Should James tell? Yes*)
lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops

end



 (*Should James kill? No*



(***Some Experiments***) 
 lemma True nitpick [satisfy] oops (*Consistency-check: Nitpick finds no model.*)
 lemma F: False by (metis A0 F1 A1 A2 A3 Situation D) (*Prove of Falsum.*)

(*Should the data be erased? — Yes, proof found by ATPs*)
 lemma "\<lfloor>\<^bold>\<circle><erase d1>\<rfloor>\<^sub>l"  sledgehammer by (metis A0 A2 F1 Situation) 
(*Should the data be kept? — Yes, proof found by ATPs*)







end

