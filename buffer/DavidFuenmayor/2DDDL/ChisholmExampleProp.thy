(*<*)
theory ChisholmExampleProp
  imports TheoryCombination
begin

declare [[smt_solver=cvc4]]
declare [[smt_oracle]]
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 2]
(*>*)

(****Chisholm Example (Propositional)****)
consts go::m tell::m
consts C::c
axiomatization where
 D1: "\<lfloor>\<^bold>O\<langle>go\<rangle>\<rfloor>" and (*It ought to be that Jones goes to assist his neighbour*)
 D2: "\<lfloor>\<^bold>O\<langle>tell|go\<rangle>\<rfloor>" and (*It ought to be that if Jones goes, then he tells them he is coming*)
 D3: "\<lfloor>\<^bold>O\<langle>\<^bold>\<not>tell|\<^bold>\<not>go\<rangle>\<rfloor>" and (*If Jones doesn't go, then he ought not tell them he is coming*)
 D4: "\<lfloor>\<^bold>\<not>(go)\<rfloor>\<^sub>C"  (*Jones doesn't go (locally valid statement)*)

lemma True nitpick [satisfy] oops

abbreviation "violated \<phi> \<equiv> \<^bold>O\<^sub>i(\<phi>) \<^bold>\<and> \<^bold>\<not>\<phi>"

lemma "(\<lfloor>\<^bold>\<box>\<^sub>a\<^bold>\<not>(go)\<rfloor>\<^sub>C \<and> \<lfloor>\<^bold>\<diamond>\<^sub>p(go \<^bold>\<and> tell)\<rfloor>\<^sub>C \<and> \<lfloor>\<^bold>\<diamond>\<^sub>p(go \<^bold>\<and> \<^bold>\<not>tell)\<rfloor>\<^sub>C \<and> \<lfloor>\<^bold>\<not>tell\<rfloor>\<^sub>C \<and> \<lfloor>\<^bold>\<diamond>\<^sub>atell\<rfloor>\<^sub>C \<and>  \<lfloor>\<^bold>\<diamond>\<^sub>a(\<^bold>\<not>tell)\<rfloor>\<^sub>C)
       \<longrightarrow> (\<lfloor>violated go\<rfloor>\<^sub>C \<and> \<lfloor>\<^bold>O\<^sub>a(\<^bold>\<not>tell)\<rfloor>\<^sub>C)" 
  using sem_4a sem_4b sem_5e D1 D3 D4 sem_5b by smt