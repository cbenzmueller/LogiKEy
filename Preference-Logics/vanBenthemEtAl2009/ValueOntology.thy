theory ValueOntology      (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
  imports PreferenceLogicBasics 
begin (*** Lomfeld's value ontology is encoded ***)

(*two legal parties (there can be more in principle)*)
datatype c = p | d (*parties/contenders: plaintiff, defendant*)
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse> = p" 
  
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

datatype (*ethico-legal upper values (wrt. a given party)*) 
 't VAL = FREEDOM 't | UTILITY 't | SECURITY 't | EQUALITY 't
type_synonym v = "(c)VAL\<Rightarrow>bool" (*principles: sets of upper values*)
type_synonym cv = "c\<Rightarrow>v" (*principles are specified wrt. a given party*)

abbreviation vset1 ("\<lbrace>_\<rbrace>") where "\<lbrace>\<phi>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<phi>" 
abbreviation vset2 ("\<lbrace>_,_\<rbrace>")   where "\<lbrace>\<alpha>,\<beta>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<alpha> \<or> x=\<beta>" 

abbreviation utility::cv  ("UTILITY\<^sup>_")  where "UTILITY\<^sup>x  \<equiv> \<lbrace>UTILITY  x\<rbrace>" 
abbreviation security::cv ("SECURITY\<^sup>_") where "SECURITY\<^sup>x \<equiv> \<lbrace>SECURITY x\<rbrace>" 
abbreviation equality::cv ("EQUALITY\<^sup>_") where "EQUALITY\<^sup>x \<equiv> \<lbrace>EQUALITY x\<rbrace>" 
abbreviation freedom::cv  ("FREEDOM\<^sup>_")  where "FREEDOM\<^sup>x  \<equiv> \<lbrace>FREEDOM  x\<rbrace>" 
abbreviation stab::cv ("STAB\<^sup>_") where "STAB\<^sup>x \<equiv> \<lbrace>SECURITY x, UTILITY  x\<rbrace>" 
abbreviation effi::cv ("EFFI\<^sup>_") where "EFFI\<^sup>x \<equiv> \<lbrace>UTILITY  x, SECURITY x\<rbrace>" 
abbreviation gain::cv ("GAIN\<^sup>_") where "GAIN\<^sup>x \<equiv> \<lbrace>UTILITY  x, FREEDOM  x\<rbrace>" 
abbreviation will::cv ("WILL\<^sup>_") where "WILL\<^sup>x \<equiv> \<lbrace>FREEDOM  x, UTILITY  x\<rbrace>" 
abbreviation resp::cv ("RESP\<^sup>_") where "RESP\<^sup>x \<equiv> \<lbrace>FREEDOM  x, EQUALITY x\<rbrace>" 
abbreviation fair::cv ("FAIR\<^sup>_") where "FAIR\<^sup>x \<equiv> \<lbrace>EQUALITY x, FREEDOM  x\<rbrace>" 
abbreviation equi::cv ("EQUI\<^sup>_") where "EQUI\<^sup>x \<equiv> \<lbrace>EQUALITY x, SECURITY x\<rbrace>" 
abbreviation reli::cv ("RELI\<^sup>_") where "RELI\<^sup>x \<equiv> \<lbrace>SECURITY x, EQUALITY x\<rbrace>" 

(*derivation operators (cf. theory of "formal concept analysis") *)
consts Vrel::"i\<Rightarrow>(c)VAL\<Rightarrow>bool" ("\<I>") (*incidence relation worlds-values*)
abbreviation intension::"\<sigma>\<Rightarrow>v" ("_\<up>") where "W\<up> \<equiv> \<lambda>v. \<forall>x. W x \<longrightarrow> \<I> x v"
abbreviation extension::"v\<Rightarrow>\<sigma>" ("_\<down>") where "V\<down> \<equiv> \<lambda>w. \<forall>x. V x \<longrightarrow> \<I> w x"

(*shorthand notation for aggregating values*) 
abbreviation agg (infixr "\<^bold>\<oplus>"80) where "v\<^sub>1\<^bold>\<oplus>v\<^sub>2 \<equiv> v\<^sub>1 \<^bold>\<sqinter> v\<^sub>2"
abbreviation agg1 ("[_]") where "[v] \<equiv> v\<down>"
abbreviation agg2 ("[_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down>"
abbreviation agg3 ("[_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2\<^bold>\<oplus>v\<^sub>3)\<down>"
abbreviation agg4 ("[_\<oplus>_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3\<oplus>v\<^sub>4] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2\<^bold>\<oplus>v\<^sub>3\<^bold>\<oplus>v\<^sub>4)\<down>"

(*chosen variant for preference relation (cf. van Benthem et al. 2009*)
abbreviation relPref::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<psi> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>"  
abbreviation relPrefval::"v\<Rightarrow>v\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>\<^sub>v_") where "\<phi> \<^bold>\<prec>\<^sub>v \<psi> \<equiv> \<psi>\<down> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>\<down>"

abbreviation incnst ("INCONS\<^sup>_") where (*inconsistency for value support*)
 "INCONS\<^sup>x \<equiv> [SECURITY\<^sup>x] \<^bold>\<and> [EQUALITY\<^sup>x] \<^bold>\<and> [FREEDOM\<^sup>x] \<^bold>\<and> [UTILITY\<^sup>x]"

lemma "True" nitpick[satisfy] oops (*verify consistency of this theory*)
end

