theory quasimax imports Main       (* Quasi-maximality: C. Benzmüller & X. Parent, 2020 *)

(* Quasi-maximality, Deb 1977, means maximal wrt transitive closure of the betterness relation restricted to the menu *)
(* Quasi-maximality: ideally the transitive closure should be paramatrized by a context.
It is restricted to the set of antecedent-worlds. The transitive closure should be recalculated each time
each time the set of worlds in which the antecedent is true changes  *)

begin
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


(* Some useful relations for constraining accessibility relations*)


definition transitive :: "\<alpha>\<Rightarrow>bool" where "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"

(*In HOL the transitive closure of a relation can be defined in a single line.*)
definition tc :: "\<alpha>\<Rightarrow>\<alpha>" where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"

definition ltc :: "\<alpha>\<Rightarrow>\<sigma>\<Rightarrow>\<alpha>" 
  where "ltc R \<phi> \<equiv>  \<lambda>x y.  \<phi> x \<and> \<phi> y \<and> (tc R x y)"

lemma transltc: "\<forall>R \<phi>. transitive (ltc R varphi)" 
  by (smt ltc_def tc_def transitive_def) 

consts BRel :: "\<alpha>" (infixr "R" 70) (*Betterness relation, cf. def. of \<circle><_|_>.*)
(*Original Max, wrt to R

abbreviation max  :: "\<sigma>\<Rightarrow>\<sigma>" ("max<_>")
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x)\<and> x R v  \<longrightarrow>  v  R x))) )" 
*)

abbreviation qmax  :: "\<sigma>\<Rightarrow>\<sigma>" ("qmax<_>")(*quasimax, i.e. max wrt to tc(R)*)
  where "qmax<\<phi>> \<equiv> (\<lambda>v. ((\<phi> v) \<and> (\<forall>x. ((\<phi> x) \<and> ((ltc BRel \<phi>) x  v)  \<longrightarrow>  ((ltc BRel \<phi>) v x)))) )" 

abbreviation subset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix "\<^bold>\<subseteq>" 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

abbreviation cond  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<circle><_|_>")
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. qmax<\<phi>> \<^bold>\<subseteq> \<psi>"


abbreviation evalid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  (*Global validity.*)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) (*Local validity — in world aw.*)  
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

lemma True nitpick [satisfy,user_axioms,expect=genuine] oops (*Consistency conf.*)


lemma CM: "\<lfloor>(\<circle><\<psi>|\<phi>>\<^bold>\<and>(\<circle><\<xi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>)\<rfloor>" nitpick  [show_all,format=2] oops

lemma RM: "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>" nitpick oops

lemma OR: "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> (\<circle><\<psi>|\<xi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>" sledgehammer oops

lemma S: "\<lfloor>\<circle><\<xi>|\<phi>\<^bold>\<and>\<psi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^bold>\<rightarrow>\<xi>|\<phi>>\<rfloor>" sledgehammer (* it should be invalid! *)



lemma assumes "\<forall>x y z. x R y \<and> y R z \<longrightarrow> x R z" 
      shows "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>" 
  using assms by blast

lemma assumes "\<lfloor>((\<circle><\<psi>|\<phi>>) \<^bold>\<and> \<^bold>\<not>(\<circle><\<^bold>\<not>\<xi>|\<phi>>)) \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>\<^bold>\<and>\<xi>>\<rfloor>" 
      shows "\<forall>x y z. x R y \<and> y R z \<longrightarrow> x R z" 
  nitpick [show_all,format=2] oops (*Countermodel presented by Nitpick.*)

end

