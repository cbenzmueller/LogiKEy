theory e imports Main       (* Aqvist's System E: C. Benzmüller & X. Parent, 2019 *)
begin      

nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3]


(*nitpick_params [sat_solver = MiniSat_JNI]*)
typedecl i (*Possible worlds.*)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>" (*Type of betterness relation between worlds.*)
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"


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
definition ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>") where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

consts r :: "\<alpha>" (infixr "r" 70) (*Betterness relation, cf. def. of \<circle><_|_>.*)

axiomatization where 
  totalness: "(\<forall>x y. (x r y) \<or> (y r x))" and
  ferrer: "(\<forall>x y z u. (x r y) \<and> (z r u) \<longrightarrow> (x r u) \<or> (z r y))" and
  quasitr: "(\<forall>x y z u. (x r y) \<and> (y r z) \<longrightarrow> (x r u) \<or> (u r z))"

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x r v \<longrightarrow>  v r x)) )) )" 
abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle><_>")   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("P<_|_>") 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"





abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (*Global validity.*)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (*Local validity — in world aw.*)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

lemma True nitpick [satisfy,user_axioms,expect=genuine] oops (*Consistency conf.*)

(*axioms of E holding irrespective of the properties of r*)
lemma Abs:"\<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>"  sledgehammer oops
lemma Nec:"\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>>\<rfloor>"  sledgehammer oops
lemma Ext:"\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circle><\<psi>|\<phi>\<^sub>2>)\<rfloor>"  sledgehammer oops
lemma Id:"\<lfloor>\<circle><\<phi>|\<phi>>\<rfloor>"  sledgehammer oops
lemma Sh:"\<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>"  sledgehammer oops
lemma MP:"(\<lfloor>\<phi>\<rfloor>\<and>\<lfloor>\<phi>\<^bold>\<rightarrow>\<psi>\<rfloor>)\<Longrightarrow>\<lfloor>\<psi>\<rfloor>"  sledgehammer oops
lemma N:"\<lfloor>\<phi>\<rfloor>\<Longrightarrow>\<lfloor>\<box>\<phi>\<rfloor>"  sledgehammer oops
lemma COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" sledgehammer oops (*countermodel*)

(*disjunctive rationlity*)

lemma "\<lfloor>\<circle><\<psi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<psi>|\<phi>>\<^bold>\<or>\<circle><\<psi>|\<chi>>)\<rfloor>" nitpick oops

lemma "\<lfloor>( \<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<chi>>\<rfloor>" nitpick oops
 

lemma  "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>"  nitpick  oops


(*Rational Monotony.*)
lemma "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>"  nitpick [user_axioms,expect=genuine]oops

(*Rational Monotony.*)
lemma "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<psi>|\<phi>\<and>\<xi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>"  nitpick [user_axioms,expect=genuine]



end

