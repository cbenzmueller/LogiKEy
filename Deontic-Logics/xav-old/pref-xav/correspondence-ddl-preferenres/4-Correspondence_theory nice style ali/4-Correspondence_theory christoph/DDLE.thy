theory DDLE  imports Main   
begin       
typedecl i \<comment> \<open>type for possible worlds\<close>  
type_synonym \<tau> = "(i\<Rightarrow>bool)" 
consts  aw::i (* actual world *) 
 
definition ddetop          :: "\<tau>" ("\<^bold>\<top>")     where "\<^bold>\<top>  \<equiv> \<lambda>w. True"
definition ddebot          :: "\<tau>" ("\<^bold>\<bottom>")      where "\<^bold>\<bottom>  \<equiv> \<lambda>w. False"
definition ddeneg          :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
definition ddeand          :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)" 
definition ddeor           :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"
definition ddeimp          :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"
definition ddeequivt       :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"

definition ddebox  :: "\<tau>\<Rightarrow>\<tau>" ("\<box>") where "\<box> \<equiv> \<lambda>\<phi> w.  \<forall>v. \<phi>(v)"
definition ddediomond  :: "\<tau>\<Rightarrow>\<tau>" ("\<diamond>") where "\<diamond> \<equiv> \<lambda>\<phi> w.  \<exists>v. \<phi>(v)"
consts r :: "i\<Rightarrow>\<tau>"  (infixr "r" 70)
 \<comment> \<open>the betterness relation r, used in definition of \<circle><_|_>  \<close>  
definition  ddeopt :: "\<tau>\<Rightarrow>\<tau>" ("opt<_>") 
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x)  \<longrightarrow>  v r x) )) )" 
abbreviation(input) msubset :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"
definition ddecond :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
    
definition  ddevalid :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
definition ddeactual :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) 
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"
     
lemma True nitpick [satisfy, user_axioms, show_all, expect=genuine] oops

 
  
end





