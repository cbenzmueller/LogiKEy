theory ValueOntology     (*** Benzmüller, Fuenmayor & Lomfeld, 2020 ***)  
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
type_synonym cv = "c\<Rightarrow>v"

abbreviation vset1 ("\<lbrace>_\<rbrace>") where "\<lbrace>\<phi>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<phi>" 
abbreviation vset2 ("\<lbrace>_,_\<rbrace>")   where "\<lbrace>\<alpha>,\<beta>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<alpha> \<or> x=\<beta>" 

abbreviation utility::cv ("UTILITY\<^sup>_")   where "UTILITY\<^sup>x  \<equiv> \<lbrace>UTILITY  x\<rbrace>" 
abbreviation security::cv ("SECURITY\<^sup>_") where "SECURITY\<^sup>x \<equiv> \<lbrace>SECURITY x\<rbrace>" 
abbreviation equality::cv ("EQUALITY\<^sup>_") where "EQUALITY\<^sup>x \<equiv> \<lbrace>EQUALITY x\<rbrace>" 
abbreviation liberety::cv ("LIBERTY\<^sup>_")  where "LIBERTY\<^sup>x  \<equiv> \<lbrace>LIBERTY  x\<rbrace>" 
abbreviation stab::cv ("STAB\<^sup>_") where "STAB\<^sup>x \<equiv> \<lbrace>SECURITY x, UTILITY  x\<rbrace>" 
abbreviation effi::cv ("EFFI\<^sup>_") where "EFFI\<^sup>x \<equiv> \<lbrace>UTILITY  x, SECURITY x\<rbrace>" 
abbreviation gain::cv ("GAIN\<^sup>_") where "GAIN\<^sup>x \<equiv> \<lbrace>UTILITY  x, LIBERTY  x\<rbrace>" 
abbreviation will::cv ("WILL\<^sup>_") where "WILL\<^sup>x \<equiv> \<lbrace>LIBERTY  x, UTILITY  x\<rbrace>" 
abbreviation resp::cv ("RESP\<^sup>_") where "RESP\<^sup>x \<equiv> \<lbrace>LIBERTY  x, EQUALITY x\<rbrace>" 
abbreviation fair::cv ("FAIR\<^sup>_") where "FAIR\<^sup>x \<equiv> \<lbrace>EQUALITY x, LIBERTY  x\<rbrace>" 
abbreviation equi::cv ("EQUI\<^sup>_") where "EQUI\<^sup>x \<equiv> \<lbrace>EQUALITY x, SECURITY x\<rbrace>" 
abbreviation reli::cv ("RELI\<^sup>_") where "RELI\<^sup>x \<equiv> \<lbrace>SECURITY x, EQUALITY x\<rbrace>" 

(*incidence relation (between values and worlds) *)
consts Vrel::"(c)VAL\<Rightarrow>i\<Rightarrow>bool" ("\<I>") 

(*derivation operators (forming a Galois connection, cf. tests) *)
abbreviation Vint::"\<sigma>\<Rightarrow>v" ("_\<up>") where "W\<up> \<equiv> \<lambda>v. \<forall>x. W x \<longrightarrow> \<I> v x"
abbreviation Vext::"v\<Rightarrow>\<sigma>" ("_\<down>") where "V\<down> \<equiv> \<lambda>w. \<forall>x. V x \<longrightarrow> \<I> x w"
abbreviation clExt::"\<sigma>\<Rightarrow>\<sigma>" ("_\<^sup>o") where "X\<^sup>o \<equiv> X\<up>\<down>"
abbreviation clInt::"v\<Rightarrow>v" ("_\<^sup>v") where "X\<^sup>v \<equiv> X\<down>\<up>"
abbreviation concept::"\<sigma>\<Rightarrow>v\<Rightarrow>bool" ("\<BB>") where "\<BB> A B \<equiv> A\<up>=B \<and> B\<down>=A"

abbreviation agg (infixr "\<^bold>\<oplus>"80) where "v\<^sub>1\<^bold>\<oplus>v\<^sub>2 \<equiv> v\<^sub>1 \<^bold>\<sqinter> v\<^sub>2"
lemma "v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down> \<^bold>\<sqsubseteq> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down>" by simp
lemma "(v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down> \<^bold>\<sqsubseteq> v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down>" nitpick oops
lemma "(v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down> \<equiv> (v\<^sub>1\<down> \<^bold>\<or> v\<^sub>2\<down>)\<up>\<down>" nitpick oops

(*shorthand notation for aggregated values*) 
abbreviation agg1 ("[_]") where "[v] \<equiv> v\<down>"
abbreviation agg2 ("[_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2)\<down>"
abbreviation agg3 ("[_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2\<^bold>\<oplus>v\<^sub>3)\<down>"
abbreviation agg4 ("[_\<oplus>_\<oplus>_\<oplus>_]") where "[v\<^sub>1\<oplus>v\<^sub>2\<oplus>v\<^sub>3\<oplus>v\<^sub>4] \<equiv> (v\<^sub>1\<^bold>\<oplus>v\<^sub>2\<^bold>\<oplus>v\<^sub>3\<^bold>\<oplus>v\<^sub>4)\<down>"

abbreviation relPref::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<psi> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>"  
abbreviation relPrefv::"v\<Rightarrow>v\<Rightarrow>\<sigma>" ("_\<^bold>\<prec>\<^sub>v_") where "\<phi> \<^bold>\<prec>\<^sub>v \<psi> \<equiv> \<psi>\<down> \<^bold>\<succ>\<^sub>E\<^sub>A \<phi>\<down>"

abbreviation indiff ("INDIFF\<^sup>_") where "INDIFF\<^sup>x \<equiv> 
  (\<^bold>\<not>SECURITY\<^sup>x\<down>)\<^bold>\<and>(\<^bold>\<not>EQUALITY\<^sup>x\<down>)\<^bold>\<and>(\<^bold>\<not>LIBERTY\<^sup>x\<down>)\<^bold>\<and>(\<^bold>\<not>UTILITY\<^sup>x\<down>)"
abbreviation incnst1 ("INCONS\<^sup>_") where 
 "INCONS\<^sup>x \<equiv> SECURITY\<^sup>x\<down> \<^bold>\<and> EQUALITY\<^sup>x\<down> \<^bold>\<and> LIBERTY\<^sup>x\<down> \<^bold>\<and> UTILITY\<^sup>x\<down>"
abbreviation incnst2 ("INCONS2\<^sup>_") where "INCONS2\<^sup>x \<equiv> 
  (SECURITY\<^sup>x \<^bold>\<squnion> EQUALITY\<^sup>x \<^bold>\<squnion> LIBERTY\<^sup>x \<^bold>\<squnion> UTILITY\<^sup>x)\<down>"

lemma "\<lfloor>INCONS\<^sup>x \<^bold>\<leftrightarrow> INCONS2\<^sup>x\<rfloor>" by blast (*equivalent*)

lemma "True" nitpick[satisfy] oops (*consistency*)
end

