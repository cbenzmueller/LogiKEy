theory ValueOntology imports PreferenceLogicBasics (** Benzm., Fuenmayor & Lomfeld, 2021 **)  
begin (*** Lomfeld's value ontology is encoded ***)
 (*new datatype for parties/contenders (there could be more in principle)*)
datatype c = p | d (*plaintiff & defendant*)
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse> = p" 
 (*new constant symbol: finding/ruling for party*)
consts For::"c\<Rightarrow>\<sigma>"    
axiomatization where ForAx: "\<lfloor>For x \<^bold>\<leftrightarrow> (\<^bold>\<not>For x\<inverse>)\<rfloor>"
 (*new parameterized datatype for abstract values (wrt. a given party)*) 
datatype 't VAL = FREEDOM 't | UTILITY 't | SECURITY 't | EQUALITY 't
type_synonym v = "(c)VAL\<Rightarrow>bool" (*principles: sets of (abstract) values*)
type_synonym cv = "c\<Rightarrow>v" (*principles are specified wrt. a given party*)
 (*notation for sets*)
abbreviation vset1 ("\<lbrace>_\<rbrace>") where "\<lbrace>\<phi>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<phi>" 
abbreviation vset2 ("\<lbrace>_,_\<rbrace>")   where "\<lbrace>\<alpha>,\<beta>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<alpha> \<or> x=\<beta>" 
 (*abstract values and value principles*)
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
(**Value Theory*)
consts Irel::"\<iota>\<Rightarrow>v" ("\<I>") (*incidence relation worlds-values*)
 (*derivation operators (cf. theory of "formal concept analysis") *)
abbreviation intent::"\<sigma>\<Rightarrow>v" ("_\<up>") where "W\<up> \<equiv> \<lambda>v. \<forall>x. W x \<longrightarrow> \<I> x v"
abbreviation extent::"v\<Rightarrow>\<sigma>" ("_\<down>") where "V\<down> \<equiv> \<lambda>w. \<forall>x. V x \<longrightarrow> \<I> w x"
abbreviation extent_brkt ("[_]") where "[V] \<equiv> V\<down>" (*alternative notation*)
 (*connective for aggregating value principles*) 
abbreviation aggr ("[_\<^bold>\<oplus>_]") where "[V\<^sub>1\<^bold>\<oplus>V\<^sub>2] \<equiv> (V\<^sub>1\<down>) \<^bold>\<or> (V\<^sub>2\<down>)"
 (*chosen variant for preference relation (cf. Halpern (1997)*)
abbreviation pref::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  ("_\<^bold>\<prec>_") where "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<^bold>\<prec>\<^sub>A\<^sub>E \<psi>"
 (*schema for value principle promotion*)
abbreviation "Promotes F D V \<equiv> \<lfloor>F \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<prec>(D \<^bold>\<leftrightarrow> \<^bold>\<diamond>\<^sup>\<prec>(V\<down>))\<rfloor>"
 (*proposition for testing for value conflict*)
abbreviation conflict ("Conflict\<^sup>_") where (*conflict for value support*)
 "Conflict\<^sup>x \<equiv> [SECURITY\<^sup>x] \<^bold>\<and> [EQUALITY\<^sup>x] \<^bold>\<and> [FREEDOM\<^sup>x] \<^bold>\<and> [UTILITY\<^sup>x]"
 (*verify consistency of this theory*)
lemma "True" nitpick[satisfy] oops 
end

