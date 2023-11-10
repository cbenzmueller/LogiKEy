theory Etest imports Main       (* Aqvist's System E: C. Benzmüller & X. Parent, 2019 *)
begin       
typedecl i (*Possible worlds.*) type_synonym \<sigma> = "(i\<Rightarrow>bool)" 
consts aw::i (*Actual world.*)  
abbreviation etrue  :: "\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

(*Possibilist--constant domain--quantification.*)
abbreviation eforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation eforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation eexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
abbreviation eexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<box>") where "\<box> \<equiv> \<lambda>\<phi> w.  \<forall>v. \<phi>(v)"  
consts R :: "i\<Rightarrow>\<sigma>" (infixr "R" 70) (*Betterness relation, cf. def. of \<circle><_|_>.*) 
abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" ("opt<_>") 
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x)  \<longrightarrow>  v R x) )) )" 
abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 

abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (*Global validity.*)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (*Local validity — in world aw.*)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

(*The standard properties*)
abbreviation reflexivity  where "reflexivity  \<equiv> (\<forall>x. x Rx)"
abbreviation transitivity 
  where "transitivity \<equiv> (\<forall>x y z. (x R y \<and> y R z) \<longrightarrow> x R z)"
abbreviation totalness 
  where "totalness \<equiv> (\<forall>x y. (x R y \<or> y R x))"

(*4 versions of Lewis's limit assumption*)

abbreviation olimitedness  
  where "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"
abbreviation osmoothness  where 
   "osmoothness \<equiv> (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> 
                      (opt<\<phi>>x \<or> (\<exists>y. (y r x \<and> \<not>(x r y) \<and> opt<\<phi>>y)))))"


lemma True nitpick [satisfy,user_axioms,expect=genuine] oops (*Consistency conf.*)

lemma assumes "transitivity"
      shows " \<forall>\<phi> \<psi> \<chi>. \<lfloor>((\<^bold>\<not>\<circle><\<^bold>\<not>\<phi>|\<phi>\<^bold>\<or>\<psi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<psi>|\<psi>\<^bold>\<or>\<chi>>)) \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>"  
  nitpick [show_all,format=5,timeout=10] 
  sledgehammer 

lemma Abs:"\<forall>\<phi> \<psi>. \<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>" 
  sledgehammer oops

lemma Sh: "\<forall>\<phi>\<^sub>1 \<phi>\<^sub>2 \<psi>. \<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>"  
  sledgehammer oops

lemma FD: "\<forall>\<phi> \<psi>. \<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<phi>) \<^bold>\<rightarrow> \<circle><\<psi>>\<rfloor>" 
    sledgehammer oops
    nitpick




lemma assumes Abs:"\<forall>\<phi> \<psi>. \<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>"
      assumes Nec:"\<forall>\<phi> \<psi>. \<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>>\<rfloor>" 
      assumes Ext:"\<forall>\<phi>\<^sub>1 \<phi>\<^sub>1 \<psi>. \<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circle><\<psi>|\<phi>\<^sub>2>)\<rfloor>"
      assumes Id:"\<forall>\<phi>. \<lfloor>\<circle><\<phi>|\<phi>>\<rfloor>" 
      assumes Sh:"\<forall>\<phi>\<^sub>1 \<phi>\<^sub>1 \<psi>. \<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" 
      assumes MP:"\<forall>\<phi> \<psi>. (\<lfloor>\<phi>\<rfloor>\<and>\<lfloor>\<phi>\<^bold>\<rightarrow>\<psi>\<rfloor>)\<Longrightarrow>\<lfloor>\<psi>\<rfloor>"
      assumes N:"\<forall>\<phi>. \<lfloor>\<phi>\<rfloor>\<Longrightarrow>\<lfloor>\<box>\<phi>\<rfloor>"
      assumes COK:"\<forall>\<phi>\<^sub>1 \<phi>\<^sub>1 \<psi>. \<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>"
      assumes "\<lfloor>((\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<psi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<chi>|\<psi>>\<rfloor>"
     shows " \<forall>\<phi> \<psi> \<chi>. \<lfloor>((\<^bold>\<not>\<circle><\<^bold>\<not>\<phi>|\<phi>\<^bold>\<or>\<psi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<psi>|\<psi>\<^bold>\<or>\<chi>>)) \<^bold>\<rightarrow> \<^bold>\<not>\<circle><\<^bold>\<not>\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>"  
  nitpick [show_all,timeout=1000] 
  sledgehammer oops



(*Correspondence theory.*)
lemma assumes "\<forall>x y z. x R y \<and> y R z \<longrightarrow> x R z" 
      shows "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>" 
  using assms by blast

lemma assumes "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>" 
      shows "\<forall>x y z. x R y \<and> y R z \<longrightarrow> x R z" 
  nitpick [show_all,format=2] oops (*Countermodel presented by Nitpick.*)
end

