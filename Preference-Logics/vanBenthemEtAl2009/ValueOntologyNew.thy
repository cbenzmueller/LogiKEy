theory ValueOntologyNew     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports PreferenceLogicBasics 
begin (*** Lomfeld's value ontology is encoded ***)

(*two legal parties (there can be more in principle)*)
datatype c = p | d (*parties/contenders: plaintiff, defendant*)
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p" 
  
consts For::"c\<Rightarrow>\<sigma>"    (*decision: find/rule for party*)
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"

datatype (*ethico-legal upper values (wrt. party)*) 
 't VAL = LIBERTY 't | UTILITY 't | SECURITY 't | EQUALITY 't
type_synonym v = "(c)VAL\<Rightarrow>bool" (*principles: sets of upper values*)

abbreviation vset1 ("\<lbrace>_\<rbrace>") where "\<lbrace>\<phi>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<phi>" 
abbreviation vset2 ("\<lbrace>_,_\<rbrace>")   where "\<lbrace>\<alpha>,\<beta>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<alpha> \<or> x=\<beta>" 

abbreviation util::"c\<Rightarrow>v" ("UTIL\<^sup>_") where "UTIL\<^sup>x \<equiv> \<lbrace>UTILITY  x\<rbrace>" 
abbreviation secu::"c\<Rightarrow>v" ("SECU\<^sup>_") where "SECU\<^sup>x \<equiv> \<lbrace>SECURITY x\<rbrace>" 
abbreviation equa::"c\<Rightarrow>v" ("EQUA\<^sup>_") where "EQUA\<^sup>x \<equiv> \<lbrace>EQUALITY x\<rbrace>" 
abbreviation libe::"c\<Rightarrow>v" ("LIBE\<^sup>_") where "LIBE\<^sup>x \<equiv> \<lbrace>LIBERTY  x\<rbrace>" 
abbreviation stab::"c\<Rightarrow>v" ("STAB\<^sup>_") where "STAB\<^sup>x \<equiv> \<lbrace>SECURITY x, UTILITY  x\<rbrace>" 
abbreviation effi::"c\<Rightarrow>v" ("EFFI\<^sup>_") where "EFFI\<^sup>x \<equiv> \<lbrace>UTILITY  x, SECURITY x\<rbrace>" 
abbreviation gain::"c\<Rightarrow>v" ("GAIN\<^sup>_") where "GAIN\<^sup>x \<equiv> \<lbrace>UTILITY  x, LIBERTY  x\<rbrace>" 
abbreviation will::"c\<Rightarrow>v" ("WILL\<^sup>_") where "WILL\<^sup>x \<equiv> \<lbrace>LIBERTY  x, UTILITY  x\<rbrace>" 
abbreviation resp::"c\<Rightarrow>v" ("RESP\<^sup>_") where "RESP\<^sup>x \<equiv> \<lbrace>LIBERTY  x, EQUALITY x\<rbrace>" 
abbreviation fair::"c\<Rightarrow>v" ("FAIR\<^sup>_") where "FAIR\<^sup>x \<equiv> \<lbrace>EQUALITY x, LIBERTY  x\<rbrace>" 
abbreviation equi::"c\<Rightarrow>v" ("EQUI\<^sup>_") where "EQUI\<^sup>x \<equiv> \<lbrace>EQUALITY x, SECURITY x\<rbrace>" 
abbreviation reli::"c\<Rightarrow>v" ("RELI\<^sup>_") where "RELI\<^sup>x \<equiv> \<lbrace>SECURITY x, EQUALITY x\<rbrace>" 

consts Vrel::"(c)VAL\<Rightarrow>i\<Rightarrow>bool" ("\<I>") (*incidence relation (between values and worlds) *)

(*derivation operators (forming a Galois connection, cf. tests) *)
abbreviation Vint::"\<sigma>\<Rightarrow>v" ("_\<up>") where "W\<up> \<equiv> \<lambda>v. \<forall>x. W x \<longrightarrow> \<I> v x"
abbreviation Vext::"v\<Rightarrow>\<sigma>" ("_\<down>") where "V\<down> \<equiv> \<lambda>w. \<forall>x. V x \<longrightarrow> \<I> x w"
abbreviation clExt::"\<sigma>\<Rightarrow>\<sigma>" ("_\<^sup>o") where "X\<^sup>o \<equiv> X\<up>\<down>"
abbreviation clInt::"v\<Rightarrow>v" ("_\<^sup>v") where "X\<^sup>v \<equiv> X\<down>\<up>"
abbreviation concept::"\<sigma>\<Rightarrow>v\<Rightarrow>bool" ("\<BB>") where "\<BB> A B \<equiv> (A\<up> = B) \<and> (B\<down> = A)"

abbreviation Vagg (infixr "\<^bold>\<oplus>"80) where "v\<^sub>1\<^bold>\<oplus>v\<^sub>2 \<equiv> v\<^sub>1 \<^bold>\<sqinter> v\<^sub>2"
lemma "v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down> \<^bold>\<sqsubseteq> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down>" by simp
lemma "(v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down> \<^bold>\<sqsubseteq> v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down>" nitpick oops
lemma "(v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down> \<equiv> (v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down>)\<up>\<down>" nitpick oops

(*useful(???) shorthand notation for aggregated values*) 
abbreviation Vagg1 ("[_]") where "[v] \<equiv> v\<down>"
abbreviation Vagg2 ("[_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2] \<equiv> (v\<^sub>1 \<^bold>\<oplus> v\<^sub>2)\<down>"
abbreviation Vagg3 ("[_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3] \<equiv> (v\<^sub>1 \<^bold>\<oplus> v\<^sub>2 \<^bold>\<oplus> v\<^sub>3)\<down>"
abbreviation Vagg4 ("[_\<oplus>_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3\<oplus>v\<^sub>4] \<equiv> (v\<^sub>1 \<^bold>\<oplus> v\<^sub>2 \<^bold>\<oplus> v\<^sub>3 \<^bold>\<oplus> v\<^sub>4)\<down>"

 (* abbreviation relPref::"v\<Rightarrow>v\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi>\<down> \<^bold>\<preceq>\<^sub>A\<^sub>E \<psi>\<down> "  *)
 abbreviation relPref::"v\<Rightarrow>v\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<psi>\<down> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>\<down>" 

abbreviation indiff ("INDIFF\<^sup>_") where "INDIFF\<^sup>x \<equiv> (\<^bold>\<not>SECU\<^sup>x\<down>) \<^bold>\<and> (\<^bold>\<not>EQUA\<^sup>x\<down>) \<^bold>\<and> (\<^bold>\<not>LIBE\<^sup>x\<down>) \<^bold>\<and> (\<^bold>\<not>UTIL\<^sup>x\<down>)"
abbreviation incnst1 ("INCONS\<^sup>_") where "INCONS\<^sup>x \<equiv> (SECU\<^sup>x \<^bold>\<squnion> EQUA\<^sup>x \<^bold>\<squnion> LIBE\<^sup>x \<^bold>\<squnion> UTIL\<^sup>x)\<down>"
abbreviation incnst2 ("INCONS2\<^sup>_") where "INCONS2\<^sup>x \<equiv> SECU\<^sup>x\<down> \<^bold>\<and> EQUA\<^sup>x\<down> \<^bold>\<and> LIBE\<^sup>x\<down> \<^bold>\<and> UTIL\<^sup>x\<down>"

lemma "\<lfloor>INCONS\<^sup>x \<^bold>\<rightarrow> INCONS2\<^sup>x\<rfloor>" by simp (*both are equivalent: choose the most performant*)
lemma "\<lfloor>INCONS2\<^sup>x \<^bold>\<rightarrow> INCONS\<^sup>x\<rfloor>" by blast

lemma "True" nitpick[satisfy] oops

end

