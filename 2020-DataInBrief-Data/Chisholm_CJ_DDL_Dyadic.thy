theory Chisholm_CJ_DDL_Dyadic imports CJ_DDL  CJ_DDL_Tests (*Christoph Benzmüller & Xavier Parent, 2019*)

begin (* Chisholm Example *)
consts go::\<tau> tell::\<tau> kill::\<tau>

 nitpick_params [user_axioms,show_all,format=2] (*Settings for model finder.*)

(*It ought to be that Jones goes to assist his neighbors.*)
  definition  "D1 \<equiv> \<^bold>O\<^bold>\<langle>go\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  
(*It ought to be that if Jones goes, then he tells them he is coming.*)
  definition  "D2 \<equiv> \<^bold>O\<^bold>\<langle>tell\<^bold>|go\<^bold>\<rangle>"  
(*If Jones doesn't go, then he ought not tell them he is coming.*)
  definition  "D3 \<equiv> \<^bold>O\<^bold>\<langle>\<^bold>\<not>tell\<^bold>|\<^bold>\<not>go\<^bold>\<rangle>"
(*Jones doesn't go. (This is encoded as a locally valid statement.)*)
  definition  "D4 \<equiv> \<^bold>\<not>go" 


(*** Chisholm ***)
 (* All-wide scoping is not leading to a dependent set of the axioms.*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3) \<^bold>\<rightarrow> D4\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D4) \<^bold>\<rightarrow> D3\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D1 \<^bold>\<and> D3 \<^bold>\<and> D4) \<^bold>\<rightarrow> D2\<rfloor>"  nitpick oops (*countermodel*)
 lemma "\<lfloor>(D2 \<^bold>\<and> D3 \<^bold>\<and> D4) \<^bold>\<rightarrow> D1\<rfloor>"  nitpick oops (*countermodel*)
 (* Chisholm is thus an adequate modeling. *)

 (* Consistency *)
 lemma "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" nitpick [satisfy] oops (*Consistent? Yes*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows False nitpick oops (*Inconsistent? No*)
 (* Queries *)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>O\<^bold>\<langle>\<^bold>\<not>tell\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>\<^sub>l" nitpick oops (*Should James not tell? No*) 
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>O\<^bold>\<langle>tell\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>\<^sub>l"
   sledgehammer nitpick oops (*Should James tell? Timeout*)
 lemma assumes "\<lfloor>(D1 \<^bold>\<and> D2 \<^bold>\<and> D3)\<rfloor> \<and> \<lfloor>D4\<rfloor>\<^sub>l" shows "\<lfloor>\<^bold>O\<^bold>\<langle>kill\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>\<^sub>l"  nitpick oops (*Should James kill? No*)

end 





