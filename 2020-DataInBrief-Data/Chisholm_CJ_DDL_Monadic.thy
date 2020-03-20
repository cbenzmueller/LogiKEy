theory Chisholm_CJ_DDL_Monadic imports CJ_DDL           (*Christoph Benzmüller & Xavier Parent, 2019*)

begin (* Chisholm Example *)
consts go::\<sigma> tell::\<sigma> kill::\<sigma>

 nitpick_params [user_axioms,show_all,format=2] (*Settings for model finder.*)

(*It ought to be that Jones goes to assist his neighbors.*)
  abbreviation  "D1 \<equiv> \<^bold>\<circle><go>"  
(*It ought to be that if Jones goes, then he tells them he is coming.*)
  abbreviation  "D2w \<equiv> \<^bold>\<circle><go \<^bold>\<rightarrow> tell>"  
  abbreviation  "D2n \<equiv> go \<^bold>\<rightarrow> \<^bold>\<circle><tell>"  
(*If Jones doesn't go, then he ought not tell them he is coming.*)
  abbreviation  "D3w \<equiv> \<^bold>\<circle><\<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>\<not>tell>" 
  abbreviation  "D3n \<equiv> \<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>\<circle><\<^bold>\<not>tell>" 
(*Jones doesn't go. (This is encoded as a locally valid statement.)*)
  abbreviation  "D4 \<equiv> \<^bold>\<not>go" 


(*** Chisholm_A ***)
 (* All-wide scoping is not leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D3w) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  sledgehammer nitpick oops (*timeout, no confirmation yet*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_A is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  nitpick oops (*Should James tell? No*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)


(*** Chisholm_B ***)
 (* All-narrow scoping is leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D4) \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D2n\<rfloor>"  by simp (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D1\<rfloor>"  nitpick oops (*countermodel*)
 (* Chisholm_B is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms by auto (*Should James not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms ax_5a ax_5b by metis (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)


(*** Chisholm_C ***)
 (* Wide-narrow scoping is leading to independence of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4) \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3n \<^bold>\<and> D4) \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_C is thus fine from this perspective. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms by auto (*Should James not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  nitpick oops (*Should James tell? No*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)
 (* Chisholm_C is thus fine and as expected. *)

(*** Chisholm_D ***)
 (* Narrow-wide scoping is leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D3w) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  sledgehammer nitpick oops (*timeout, no confirmation yet*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2n\<rfloor>"  by auto  (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_D is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms ax_5a ax_5b by force (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)
end 

