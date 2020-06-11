theory ValueOntology                 (*Benzmüller,Fuenmayor & Lomfeld, 2020*)  
  imports PreferenceLogicBasics 
begin (** proof of concept: ethical value ontology and wild animal cases **)
abbreviation pref::\<nu>            ("_\<^bold>\<prec>_")   where  "\<phi> \<^bold>\<prec> \<psi> \<equiv> \<phi> \<prec>\<^sub>A\<^sub>E \<psi>"   
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("_\<subseteq>_")   where  "\<alpha>\<subseteq>\<beta> \<equiv> \<forall>w.(\<alpha> w)\<longrightarrow>(\<beta> w)" 
abbreviation boxg::\<mu> ("\<^bold>\<box>_") where "\<^bold>\<box>\<phi> \<equiv> \<^bold>\<box>\<^sup>\<preceq>\<phi>"

(*ethico-legal values*)
datatype UVAL = SECURITY | LIBERTY | EQUALITY | UTILITY
datatype VAL = WILL | RELI | RESP | EQUI | FAIR | EFFI | STAB | GAIN 

(*contenders have values*)
datatype c = p | d      (*parties/contenders: plaintiff, defendant*)  
fun other::"c\<Rightarrow>c" ("_\<inverse>") where "p\<inverse> = d" | "d\<inverse>= p"
consts UV::"c\<Rightarrow>UVAL\<Rightarrow>\<sigma>" ("_\<up>_") (*c\<up>UV: contenders c has upper value UV*)
consts  V::"c\<Rightarrow> VAL\<Rightarrow>\<sigma>" ("_\<down>_") (*c\<down>V: contenders c has value V*)

axiomatization where (*axiomatization of the ethico-legal value ontology*)
V1: "\<lfloor>(x\<up>SECURITY \<^bold>\<and> x\<up>EQUALITY) \<^bold>\<rightarrow> \<^bold>\<not>(x\<up>UTILITY \<^bold>\<and> x\<up>LIBERTY)\<rfloor>" and 
V2: "\<lfloor>(x\<down>RELI \<^bold>\<or> x\<down>EQUI \<^bold>\<or> x\<down>STAB \<^bold>\<or> x\<down>EFFI) \<^bold>\<leftrightarrow> x\<up>SECURITY\<rfloor>" and
V3: "\<lfloor>(x\<down>FAIR \<^bold>\<or> x\<down>RESP \<^bold>\<or> x\<down>EQUI \<^bold>\<or> x\<down>RELI) \<^bold>\<leftrightarrow> x\<up>EQUALITY\<rfloor>" and
V4: "\<lfloor>(x\<down>WILL \<^bold>\<or> x\<down>GAIN \<^bold>\<or> x\<down>RESP \<^bold>\<or> x\<down>FAIR) \<^bold>\<leftrightarrow> x\<up>LIBERTY\<rfloor>" and
V5: "\<lfloor>(x\<down>EFFI \<^bold>\<or> x\<down>STAB \<^bold>\<or> x\<down>GAIN \<^bold>\<or> x\<down>WILL) \<^bold>\<leftrightarrow> x\<up>UTILITY\<rfloor>" 

lemma L1: "\<lfloor>(x\<up>UTILITY  \<^bold>\<and> x\<up>LIBERTY)  \<^bold>\<rightarrow> \<^bold>\<not>(x\<up>SECURITY \<^bold>\<and> x\<up>EQUALITY)\<rfloor>" 
  using V1 by blast
lemma L2: "\<lfloor>(x\<up>LIBERTY  \<^bold>\<and> x\<up>EQUALITY) \<^bold>\<rightarrow> \<^bold>\<not>(x\<up>SECURITY \<^bold>\<and> x\<up>UTILITY)\<rfloor>"  
  using V1 by blast
lemma L3: "\<lfloor>(x\<up>EQUALITY \<^bold>\<and> x\<up>SECURITY) \<^bold>\<rightarrow> \<^bold>\<not>(x\<up>UTILITY  \<^bold>\<and> x\<up>LIBERTY)\<rfloor>"  
  using V1 by blast

(*exploring & assessing the ontology with reasoning tools*)
lemma "True" nitpick[satisfy,max_genuine=80,eval=UV V p d] oops (*show models*)
lemma "\<exists>x. \<lfloor>x\<down>GAIN \<^bold>\<and> x\<down>STAB \<^bold>\<and> x\<down>WILL\<rfloor>" nitpick[satisfy]  oops (*satisfiable*)
lemma "\<exists>x. \<lfloor>x\<down>RELI \<^bold>\<and> x\<down>WILL\<rfloor>" nitpick[satisfy]  oops (*not satisfiable*)
lemma "\<not>(\<exists>x. \<lfloor>x\<down>RELI \<^bold>\<and> x\<down>WILL\<rfloor>)" using L2 V2 V3 V4 V5 by blast 
end

