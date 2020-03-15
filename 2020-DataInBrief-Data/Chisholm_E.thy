theory Chisholm_E imports E                 (*Christoph Benzmüller & Xavier Parent, 2019*)


begin (* Chisholm Example *)
consts go::\<sigma> tell::\<sigma> kill::\<sigma>

  nitpick_params [user_axioms,expect=genuine,show_all,format=2] (*settings for the model finder*)

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
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_A is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by auto (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)


(*** Chisholm_B ***)
 (* All-narrow scoping is leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops  (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2n\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_B is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms by auto (*Should James not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by auto (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  using assms by smt (*Should James kill? Yes*)


(*** Chisholm_C ***)
 (* Wide-narrow scoping is leading to independence of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D3n) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3n\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2w\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2w \<^bold>\<and> D3n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_C is thus fine from this perspective. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms by auto (*Should James not tell? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by blast (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2w \<^bold>\<and> D3n)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  using assms by blast (*Should James kill? Yes*)


(*** Chisholm_D ***)
 (* Narrow-wide scoping is leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D3w) \<^bold>\<rightarrow> D4\<rfloor>"   nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D2n \<^bold>\<and> D4)  \<^bold>\<rightarrow> D3w\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D1  \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D2n\<rfloor>"  by blast  (*proof*)
 lemma "\<lfloor>(D2n \<^bold>\<and> D3w \<^bold>\<and> D4)  \<^bold>\<rightarrow> D1\<rfloor>"   nitpick oops (*countermodel*)
 (* Chisholm_D is thus an inadequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms by blast (*Should James tell? Yes*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2n \<^bold>\<and> D3w)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)



(* old stuff

(*** Chisholm_A ***)
 (* All-wide scoping is not leading to an independent set of the axioms.*)
 lemma assumes D1 and D2w and D3w        shows D4     nitpick oops (*countermodel*)
 lemma assumes D1 and D2w            and D4 shows D3w using assms(1) by auto
 lemma assumes D1            and D3w and D4 shows D2w nitpick  oops (*countermodel*)
 lemma assumes        D2w and D3w and D4 shows D1     nitpick  oops (*countermodel*)
 (* Chisholm_A is thus an inadequate modeling. *)

 (* Conistency *)
 lemma assumes D1 and D2w and D3w and D4 shows True nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes D1 and D2w and D3w and D4 shows False nitpick oops (*Inconsistent? No*) 
 (* Queries *)
 lemma assumes D1 and D2w and D3w and D4 shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes D1 and D2w and D3w and D4 shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms(1) assms(2) cjactual_def by blast (*Should James tell? Yes*)
 lemma assumes D1 and D2w and D3w and D4 shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill?     No*)



(*** Chisholm_B ***)
 (* All-narrow scoping is leading to an independent set of the axioms.*)
 lemma assumes D1 and D2n and D3n        shows D4     nitpick oops (*countermodel*)
 lemma assumes D1 and D2n            and D4 shows D3n nitpick oops (*countermodel*)
 lemma assumes D1            and D3n and D4 shows D2n nitpick oops (*countermodel*)
 lemma assumes        D2n and D3n and D4 shows D1     nitpick oops (*countermodel*)
 (* Chisholm_B is thus fine from this perspective. *)

 (* Conistency *)
 lemma assumes D1 and D2n and D3n and D4 shows True nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes D1 and D2n and D3n and D4 shows False nitpick oops (*Inconsistent? No*) 
 (* Queries *)
 lemma assumes D1 and D2n and D3n and D4 shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms(3) assms(4) cjactual_def by auto (*Should James not tell? Yes*) 
 lemma assumes D1 and D2n and D3n and D4 shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms(1) assms(2) cjactual_def by auto (*Should James tell? Yes*)
 lemma assumes D1 and D2n and D3n and D4 shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  using assms(1) assms(2) assms(3) assms(4) cjactual_def by auto (*Should James kill? Yes*)



(*** Chisholm_C ***)
 (* Wide-narrow scoping is leading to independence of the axioms.*)
 lemma assumes D1 and D2w and D3n        shows D4     nitpick oops (*countermodel*)
 lemma assumes D1 and D2w            and D4 shows D3n nitpick oops (*countermodel*)
 lemma assumes D1            and D3n and D4 shows D2w nitpick oops (*countermodel*)
 lemma assumes        D2w and D3n and D4 shows D1     nitpick oops (*countermodel*)
 (* Chisholm_C is thus fine from this perspective. *)

 (* Conistency *)
 lemma assumes D1 and D2w and D3n and D4 shows True nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes D1 and D2w and D3n and D4 shows False nitpick oops (*Inconsistent? No*) 
 (* Queries *)
 lemma assumes D1 and D2w and D3n and D4 shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" using assms(3) assms(4) cjactual_def by auto (*Should James not tell? Yes*) 
 lemma assumes D1 and D2w and D3n and D4 shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms(1) assms(2) cjactual_def by auto (*Should James tell? Yes*)
 lemma assumes D1 and D2w and D3n and D4 shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  using assms(1) assms(2) assms(3) assms(4) cjactual_def by force (*Should James kill? Yes*)



(*** Chisholm_D ***)
 (* Narrow-wide scoping is not leading to independence of the axioms.*)
 lemma assumes D1 and D2n and D3w        shows D4     nitpick oops (*countermodel*)
 lemma assumes D1 and D2n            and D4 shows D3w using assms(1) by auto
 lemma assumes D1            and D3w and D4 shows D2n nitpick  oops (*countermodel*)
 lemma assumes        D2n and D3w and D4 shows D1     nitpick  oops (*countermodel*)
 (* Chisholm_D is thus an inadequate modeling. *)

 (* Consistency *)
 lemma assumes D1 and D2n and D3w and D4 shows True nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes D1 and D2n and D3w and D4 shows False nitpick oops (*Inconsistent? No*) 
 (* Queries *)
 lemma assumes D1 and D2n and D3w and D4 shows "\<lfloor>\<^bold>\<circle><\<^bold>\<not>tell>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes D1 and D2n and D3w and D4 shows "\<lfloor>\<^bold>\<circle><tell>\<rfloor>\<^sub>l"  using assms(1) assms(2) cjactual_def by auto (*Should James tell? Yes*)
 lemma assumes D1 and D2n and D3w and D4 shows "\<lfloor>\<^bold>\<circle><kill>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)

*)

end 