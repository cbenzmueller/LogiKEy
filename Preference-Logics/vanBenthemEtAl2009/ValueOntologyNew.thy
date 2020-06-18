theory ValueOntologyNew     (*Benzmüller, Fuenmayor & Lomfeld, 2020*)  
  imports PreferenceLogicCeterisParibus 
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
abbreviation vset3 ("\<lbrace>_,_,_\<rbrace>") where "\<lbrace>\<alpha>,\<beta>,\<gamma>\<rbrace> \<equiv> \<lambda>x::(c)VAL. x=\<alpha> \<or> x=\<beta> \<or> x=\<gamma>"

abbreviation util::"c\<Rightarrow>v" ("UTIL\<^sup>_") where "UTIL\<^sup>x \<equiv> \<lbrace>UTILITY x\<rbrace>" 
abbreviation equa::"c\<Rightarrow>v" ("EQUA\<^sup>_") where "EQUA\<^sup>x \<equiv> \<lbrace>EQUALITY x\<rbrace>" 
abbreviation stab::"c\<Rightarrow>v" ("STAB\<^sup>_") where "STAB\<^sup>x \<equiv> \<lbrace>UTILITY x, SECURITY x\<rbrace>" 
abbreviation will::"c\<Rightarrow>v" ("WILL\<^sup>_") where "WILL\<^sup>x \<equiv> \<lbrace>UTILITY x, LIBERTY x\<rbrace>" 
abbreviation resp::"c\<Rightarrow>v" ("RESP\<^sup>_") where "RESP\<^sup>x \<equiv> \<lbrace>EQUALITY x, LIBERTY x\<rbrace>" 
abbreviation reli::"c\<Rightarrow>v" ("RELI\<^sup>_") where "RELI\<^sup>x \<equiv> \<lbrace>EQUALITY x, SECURITY x\<rbrace>" 
(* TODO: add more...*)

consts Vrel::"(c)VAL\<Rightarrow>i\<Rightarrow>bool" ("\<I>") (*incidence relation (between values and worlds) *)

(*derivation operators (forming a Galois connection, cf. tests) *)
abbreviation Vint::"\<sigma>\<Rightarrow>v" ("_\<up>") where "W\<up> \<equiv> \<lambda>v. \<forall>x. W x \<longrightarrow> \<I> v x"
abbreviation Vext::"v\<Rightarrow>\<sigma>" ("_\<down>") where "V\<down> \<equiv> \<lambda>w. \<forall>x. V x \<longrightarrow> \<I> x w"
abbreviation clExt::"\<sigma>\<Rightarrow>\<sigma>" ("_\<^sup>o") where "X\<^sup>o \<equiv> X\<up>\<down>"
abbreviation clInt::"v\<Rightarrow>v" ("_\<^sup>v") where "X\<^sup>v \<equiv> X\<down>\<up>"
abbreviation concept::"\<sigma>\<Rightarrow>v\<Rightarrow>bool" ("\<BB>") where "\<BB> A B \<equiv> (A\<up> = B) \<and> (B\<down> = A)"

abbreviation union (infixr "\<^bold>\<squnion>" 70) where "A\<^bold>\<squnion>B \<equiv> \<lambda>x. A x \<or> B x"
abbreviation inters (infixr "\<^bold>\<sqinter>" 70) where "A\<^bold>\<sqinter>B \<equiv> \<lambda>x. A x \<and> B x"

(*useful shorthand notation for aggregated values*) 
abbreviation Vagg::"v\<Rightarrow>v\<Rightarrow>\<sigma>" (infixr "\<^bold>\<oplus>" 80) where "v\<^sub>1\<^bold>\<oplus>v\<^sub>2 \<equiv> (v\<^sub>1 \<^bold>\<sqinter> v\<^sub>2)\<down>"

abbreviation "INCONS c \<equiv> WILL\<^sup>c \<^bold>\<oplus> RELI\<^sup>c" (*since they include all 4 upper values (at present)*)
(* abbreviation "INDIFF c \<equiv> (\<lambda>x. False)" TODO: define - how?*)

(*exploring the consistency and models of the ontology*)
lemma "True" nitpick[satisfy,show_all,card i=1] oops
lemma "True" nitpick[satisfy,show_all,card i=10] oops

lemma "\<lfloor> RELI\<^sup>d\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" nitpick[satisfy,show_all] oops
lemma "\<lfloor>(\<^bold>\<not>INCONS p) \<^bold>\<and> RELI\<^sup>p\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" nitpick[satisfy,show_all] oops

(*TODO: should find models:*)
lemma "\<lfloor>(\<^bold>\<not>INCONS d) \<^bold>\<and> (\<^bold>\<not>INCONS p) \<^bold>\<and> RELI\<^sup>d\<down> \<^bold>\<and> WILL\<^sup>p\<down>\<rfloor>" nitpick[satisfy,show_all] oops

end

