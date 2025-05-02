theory DDL_agents_mod  (*DDL including STIT operator and agentive obligations*)
  imports 
    Main
    types_2
begin 

consts
 cw::i (*current world*)
 av::"i\<Rightarrow>\<sigma>" pv::"i\<Rightarrow>\<sigma>" ob::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*general accessibility relations*)

 av_g::"ag\<Rightarrow>i\<Rightarrow>\<sigma>" pv_g::"ag\<Rightarrow>i\<Rightarrow>\<sigma>" ob_g::"ag\<Rightarrow>(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))" (*agent-dependent accessibility relations*)
  
 (*stit operator*) 
 stit::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*ag sees to it that*)

axiomatization where
 ax_3a: "\<forall>w.\<exists>x. av(w)(x)" and ax_4a: "\<forall>w x. av(w)(x) \<longrightarrow> pv(w)(x)" and ax_4b: "\<forall>w. pv(w)(w)" and
 ax_5a: "\<forall>X.\<not>ob(X)(\<lambda>x. False)" and
 ax_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))" and
 ax_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> ob(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> ob(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
 ax_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  ob(X)(Y)  \<and>  ob(X)(Z))  \<longrightarrow>  ob(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
 ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> ob(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
 ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)" and

 (*agent-dependent axioms*)
 axg_3a: "\<forall>w a.\<exists>x. av_g a (w)(x)" and axg_4a: "\<forall>w x a. av_g a (w)(x) \<longrightarrow> pv_g a (w)(x)" and axg_4ba: "\<forall>w a. pv_g a (w)(w)" and
 axg_5a: "\<forall>X a.\<not>ob_g a (X)(\<lambda>x. False)" and
 axg_5b: "\<forall>X Y Z a. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (ob_g a(X)(Y) \<longleftrightarrow> ob_g a (X)(Z))" and
 axg_5ca: "\<forall>X \<beta> a. ((\<forall>Z. \<beta>(Z) \<longrightarrow> ob_g a(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> ob_g a (X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
 axg_5c: "\<forall>X Y Z a. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  ob_g a (X)(Y)  \<and>  ob_g a(X)(Z))  \<longrightarrow>  ob_g a(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
 axg_5d: "\<forall>X Y Z a. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob_g a (X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w))) 
                   \<longrightarrow> ob_g a(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
 axg_5e: "\<forall>X Y Z a. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob_g a(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob_g a(Y)(Z)" and

 stit1: "\<forall>a F w. ((stit a F) w) \<longrightarrow> F w"
  
 abbreviation ddlneg::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
 abbreviation ddland::\<rho> (infixr"\<^bold>\<and>"51) where "A\<^bold>\<and>B \<equiv> \<lambda>w. A(w)\<and>B(w)"   
 abbreviation ddlor::\<rho> (infixr"\<^bold>\<or>"50) where "A\<^bold>\<or>B \<equiv> \<lambda>w. A(w)\<or>B(w)"   
 abbreviation ddlimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. A(w)\<longrightarrow>B(w)"  
 abbreviation ddlequiv::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "A\<^bold>\<leftrightarrow>B \<equiv> \<lambda>w. A(w)\<longleftrightarrow>B(w)"  
 abbreviation ddlbox::\<gamma> ("\<^bold>\<box>") where "\<^bold>\<box>A \<equiv> \<lambda>w.\<forall>v. A(v)" 
 abbreviation ddldia::\<gamma>  ("\<^bold>\<diamond>") where "\<^bold>\<diamond> A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>A)"

 (*Necessity/possibility for agents*)
 abbreviation ddlboxa_g::\<eta> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>a i A \<equiv> \<lambda>w. (\<forall>x. av_g i (w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp_g::\<eta> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>p i A \<equiv> \<lambda>w. (\<forall>x. pv_g i (w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa_g::\<eta> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>a i A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a i (\<^bold>\<not>A)"
 abbreviation ddldiap_g::\<eta> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>p i A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p i (\<^bold>\<not>A)"
 (*generalised operators with agents as a parameter*)
 abbreviation ddlo_g::\<chi> ("\<^bold>O _ \<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>") where "\<^bold>O i \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. ob_g i A B"  (*Agent i ought to A, given B *)
 abbreviation ddloa_g::\<eta>  ("\<^bold>O\<^sub>a _ ") where "\<^bold>O\<^sub>a i A \<equiv> \<lambda>w. ob_g i (av_g i (w))(A) \<and> (\<exists>x. av_g i (w)(x) \<and> \<not>A(x))" (*actual obligation*)
 abbreviation ddlop_g::\<eta>  ("\<^bold>O\<^sub>p _") where "\<^bold>O\<^sub>p i A \<equiv> \<lambda>w. ob_g i (pv_g i (w))(A) \<and> (\<exists>x. pv_g i (w)(x) \<and> \<not>A(x))"  (*primary obligation*)

 (*non-agentive necessity, possibility and obligation operators*)
 abbreviation ddlboxa::\<gamma> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>aA \<equiv> \<lambda>w. (\<forall>x. av(w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp::\<gamma> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>pA \<equiv> \<lambda>w. (\<forall>x. pv(w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa::\<gamma> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>aA \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a(\<^bold>\<not>A)"
 abbreviation ddldiap::\<gamma> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>pA \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p(\<^bold>\<not>A)" 
 abbreviation ddlo::\<rho> ("\<^bold>O\<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>"[52]53) where "\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. ob(A)(B)"  (*it ought to be \<psi>, given \<phi> *)
 abbreviation ddloa::\<gamma>  ("\<^bold>O\<^sub>a") where "\<^bold>O\<^sub>aA \<equiv> \<lambda>w. ob(av(w))(A) \<and> (\<exists>x. av(w)(x) \<and> \<not>A(x))" (*actual obligation*)
 abbreviation ddlop::\<gamma>  ("\<^bold>O\<^sub>p") where "\<^bold>O\<^sub>pA \<equiv> \<lambda>w. ob(pv(w))(A) \<and> (\<exists>x. pv(w)(x) \<and> \<not>A(x))"  (*primary obligation*)
 
 abbreviation ddltop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
 abbreviation ddlbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

(*Possibilist Quantification.*)
 abbreviation ddlforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
 abbreviation ddlforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
 abbreviation ddlexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
 abbreviation ddlexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

 abbreviation ddlvalid::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]105) where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w"   (*Global validity*)
 abbreviation ddlvalidcw::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) where "\<lfloor>A\<rfloor>\<^sub>l \<equiv> A cw" (*Local validity (in cw)*)

 (*New syntax *)
 abbreviation ddlobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><A> \<equiv>  \<^bold>O\<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>" 
 abbreviation ddlobl_g::\<eta> ("\<^bold>\<circle>_<_>") where "\<^bold>\<circle> i <A> \<equiv>  \<^bold>O i \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"

 (* Consistency *) 
 lemma True nitpick [satisfy,user_axioms,show_all,card i=1, card ag=3] (*no model for i>1*) oops

end


