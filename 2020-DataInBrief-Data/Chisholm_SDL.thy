theory Chisholm_SDL imports SDL                          (*Christoph Benzmüller & Xavier Parent, 2019*)
begin     (*Unimportant*) nitpick_params [user_axioms,show_all,format=2] 

(*** Chisholm Example ***)
  consts go::\<sigma> tell::\<sigma> kill::\<sigma>
  abbreviation  "D1 \<equiv> \<^bold>\<circle><go>"  (*It ought to be that Jones goes to assist his neighbors.*)
  abbreviation  "D2w \<equiv> \<^bold>\<circle><go \<^bold>\<rightarrow> tell>"  (*It ought to be that if Jones goes, then he tells them he is coming.*)
  abbreviation  "D2n \<equiv> go \<^bold>\<rightarrow> \<^bold>\<circle><tell>"  
  abbreviation  "D3w \<equiv> \<^bold>\<circle><\<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>\<not>tell>" (*If Jones doesn't go, then he ought not tell them he is coming.*)
  abbreviation  "D3n \<equiv> \<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>\<circle><\<^bold>\<not>tell>" 
  abbreviation  "D4 \<equiv> \<^bold>\<not>go" (*Jones doesn't go. (This is encoded as a locally valid statement.)*)

(*** Chisholm_A: All-wide scoping is leading to an inadequate, dependent set of the axioms.***)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D3w) \<^bold>\<rightarrow> D4\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  sledgehammer by blast  (*proof*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"  nitpick oops (*countermodel*)
 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by blast (*Should J. tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)

(*** Chisholm_B: All-narrow scoping is leading to a inadequate, dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops  (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2n\<rfloor>"  sledgehammer by blast  (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms by smt (*Should J. not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  nitpick oops (*Should James tell? No*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)

(*** Chisholm_C: Wide-narrow scoping is leading to an adequate, independence of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4) \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy]  (*Consistent? No HERE*) 
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using D assms by smt (*Shld J. not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by blast (*Should J. tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  using D assms by blast (*Should J. kill? Yes*)

(*** Chisholm_D: Narrow-wide scoping is leading to a  inadequate, dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D3w) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2n\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  nitpick oops (*Should James tell? No*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)
end 


