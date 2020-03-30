theory IHOML imports Main                      
begin  
  typedecl i (*Possible worlds*)  typedecl e (*Individuals*)      
  type_synonym \<delta> = "e\<Rightarrow>bool" (*Type of ordinary predicates*)
  type_synonym \<sigma> = "i\<Rightarrow>bool" (*Type of world-lifted propositions, truth-sets*)
  type_synonym \<tau> = "i\<Rightarrow>i\<Rightarrow>bool" (*Type of accessibility relations*)
  type_synonym \<gamma> = "e\<Rightarrow>\<sigma>" (*Type of lifted predicates*)
(**Logical operators lifted to truth-sets**)  
  abbreviation mbot::"\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
  abbreviation mtop::"\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
  abbreviation mnot::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  abbreviation negpred::"\<delta>\<Rightarrow>\<delta>" ("\<rightharpoondown>_"[52]53) where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)" 
  abbreviation mnegpred::"\<gamma>\<Rightarrow>\<gamma>" ("\<^bold>\<rightharpoondown>_"[52]53) where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)"
  abbreviation mand::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"   
  abbreviation mor::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation mimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"  
  abbreviation mequ::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
(**Polymorphic possibilist quantification**) 
  abbreviation mforall::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexists::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
  abbreviation mexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
(**Actualist quantification for individuals**)
  consts Exists::\<gamma> ("existsAt")  
  abbreviation mforallAct::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. (existsAt x w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mforallActB (binder"\<^bold>\<forall>\<^sup>E"[8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
  abbreviation mexistsAct::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. (existsAt x w) \<and> (\<Phi> x w)"
  abbreviation mexistsActB (binder"\<^bold>\<exists>\<^sup>E"[8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"
(**Modal operators**)
  consts aRel::\<tau> (infixr "r" 70)  (*Accessibility Relation r*)
  abbreviation mbox::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_"[52]53) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_"[52]53) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"
(**Meta-logical predicates**)
  abbreviation globalvalid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]) where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)"
(**Definition of rigidly intensionalised predicates**)
  (*\<lparr>\<phi>\<rparr> converts an extensional object \<phi> into `rigid' intensional one*)  
  abbreviation trivialConversion::"bool\<Rightarrow>\<sigma>" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> (\<lambda>w. \<phi>)"
  (*Q\<^bold>\<down>\<phi>: the extension of a (possibly) non-rigid predicate \<phi> is turned into a rigid intensional 
   one and Q is applied to the latter; \<down>\<phi> is read as "the rigidly intensionalised predicate \<phi>"*)
  abbreviation mextPredArg::"(\<gamma>\<Rightarrow>\<sigma>)\<Rightarrow>\<gamma>\<Rightarrow>\<sigma>" (infix"\<^bold>\<down>"60) where "\<phi>\<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. \<lparr>P x w\<rparr>) w"
  lemma "\<forall>\<phi> P. \<phi> P = \<phi>\<^bold>\<down>P" nitpick[user_axioms] oops (*Countermodel: notions are not the same*)
(**Some further definitions required for Fitting's variant**)
  (*\<phi>'s argument is a relativized term of extensional type derived from an intensional predicate*)
  abbreviation extPredArg::"(\<delta>\<Rightarrow>\<sigma>)=>\<gamma>=>\<sigma>" (infix"\<down>"60) where "\<phi>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"
  (*Another variant where \<phi> has two arguments (the first one being relativized)*)
  abbreviation extPredArg1::"(\<delta>\<Rightarrow>\<gamma>)=>\<gamma>=>\<gamma>" (infix"\<down>\<^sub>1"60) where "\<phi>\<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
(**Consistency**)
  lemma True nitpick[satisfy] oops  (*Model found by Nitpick*)
end