theory embedding
  imports Main
begin
(* Configuration defaults *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)

subsection \<open>(Shallow) Semantic Embedding of modal logic using a Kripke semantics\<close>

typedecl w                  (**type for possible worlds*)
type_synonym wo = "w\<Rightarrow>bool" (**type for formulas (i.e. characteristic functions of sets of worlds)*)

(*** (meta-logical) algebraic operations on truth-sets*)
abbreviation top::"wo" ("\<^bold>\<top>")    where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation bottom::"wo" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation equ::"'t\<Rightarrow>'t\<Rightarrow>wo" (infixr "\<^bold>\<approx>" 48) where "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<lambda>w. \<phi> = \<psi>"
abbreviation meet::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<inter>" 51) where "\<phi> \<^bold>\<inter> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"
abbreviation join::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<union>" 50) where "\<phi> \<^bold>\<union> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
abbreviation subs::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<Rightarrow>" 49) where "\<phi> \<^bold>\<Rightarrow> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"
abbreviation sequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<approx>\<^sup>c" 48) where "\<phi> \<^bold>\<approx>\<^sup>c \<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation compl::"wo\<Rightarrow>wo" ("_\<^sup>C" [54]55)      where    "\<phi>\<^sup>C  \<equiv> \<lambda>w. \<not>(\<phi> w)"

(*** boolean connectives*)
abbreviation cand::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<and>" 51)  where "\<phi> \<^bold>\<and> \<psi>  \<equiv> \<phi> \<^bold>\<inter> \<psi> "
abbreviation cor:: "wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<or>" 50)  where "\<phi> \<^bold>\<or> \<psi>  \<equiv> \<phi> \<^bold>\<union> \<psi>"
abbreviation cimp::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<rightarrow>" 49) where  "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<^bold>\<Rightarrow> \<psi>"
abbreviation cequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix  "\<^bold>\<leftrightarrow>" 48) where  "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<phi> \<^bold>\<approx> \<psi>"
abbreviation cneg::"wo\<Rightarrow>wo"      ("\<^bold>\<not>_" [54]55)   where   "\<^bold>\<not>\<phi>   \<equiv> \<phi>\<^sup>C"

(** accessibility relation and modal operators*)
consts aRel::"w\<Rightarrow>w\<Rightarrow>bool" (infix "r" 70)
abbreviation mbox :: "wo\<Rightarrow>wo" ("\<^bold>\<box>_"[54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v) \<longrightarrow> (\<phi> v)"
abbreviation mdia :: "wo\<Rightarrow>wo" ("\<^bold>\<diamond>_"[54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v) \<and> (\<phi> v)" (*i.e. \<sim>\<box>\<sim>\<phi> *)

subsection \<open>Meta-logical predicates for validity and consequence\<close>

abbreviation valid::"wo\<Rightarrow>bool"       ("[\<turnstile> _]") where  "[\<turnstile>  \<phi>]  \<equiv> \<forall>w. \<phi> w"  (*truth in all worlds*)
abbreviation satisfiable::"wo\<Rightarrow>bool" ("[\<turnstile>\<^sup>s\<^sup>a\<^sup>t_]") where "[\<turnstile>\<^sup>s\<^sup>a\<^sup>t \<phi>] \<equiv> \<exists>w. \<phi> w"  (*truth in some world*)
abbreviation invalid::"wo\<Rightarrow>bool"     ("[\<turnstile>\<^sup>i\<^sup>n\<^sup>v_]") where "[\<turnstile>\<^sup>i\<^sup>n\<^sup>v \<phi>] \<equiv> \<forall>w. \<not>\<phi> w" (*falsity in all worlds*)

abbreviation conseq_global::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<turnstile>\<^sub>g _]") where 
    "[\<phi> \<turnstile>\<^sub>g \<psi>] \<equiv> [\<turnstile> \<phi>] \<longrightarrow> [\<turnstile> \<psi>]"
abbreviation conseq_local::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<turnstile>\<^sub>l _]") where 
    "[\<phi> \<turnstile>\<^sub>l \<psi>] \<equiv> [\<turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]"
abbreviation equ_global::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<cong>\<^sub>g _]") where 
    "[\<phi> \<cong>\<^sub>g \<psi>] \<equiv> [\<turnstile> \<phi>] \<longleftrightarrow> [\<turnstile> \<psi>]"
abbreviation equ_local::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<cong>\<^sub>l _]") where 
    "[\<phi> \<cong>\<^sub>l \<psi>] \<equiv> [\<turnstile> \<phi> \<^bold>\<leftrightarrow> \<psi>]"
abbreviation conseq_global2::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_ \<turnstile>\<^sub>g _]") where 
    "[\<phi>, \<gamma> \<turnstile>\<^sub>g \<psi>] \<equiv> [\<turnstile> \<phi>] \<longrightarrow> ([\<turnstile> \<gamma>] \<longrightarrow> [\<turnstile> \<psi>])"
abbreviation conseq_local2::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_ \<turnstile>\<^sub>l _]") where 
    "[\<phi>, \<gamma> \<turnstile>\<^sub>l \<psi>] \<equiv> [\<turnstile> \<phi> \<^bold>\<rightarrow> (\<gamma> \<^bold>\<rightarrow> \<psi>)]"
abbreviation conseq_global3::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_,_ \<turnstile>\<^sub>g _]") where 
    "[\<phi>, \<gamma>, \<eta> \<turnstile>\<^sub>g \<psi>] \<equiv> [\<turnstile> \<phi>] \<longrightarrow> ([\<turnstile> \<gamma>] \<longrightarrow> [\<turnstile> \<eta>] \<longrightarrow> [\<turnstile> \<psi>])"
abbreviation conseq_local3::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_,_ \<turnstile>\<^sub>l _]") where 
    "[\<phi>, \<gamma>, \<eta> \<turnstile>\<^sub>l \<psi>] \<equiv> [\<turnstile> \<phi> \<^bold>\<rightarrow> \<gamma> \<^bold>\<rightarrow> \<eta> \<^bold>\<rightarrow> \<psi>]"

section \<open>Proving some meta-logical properties\<close>

lemma mod: "[\<^bold>\<box>a \<cong>\<^sub>l \<^bold>\<not>\<^bold>\<diamond>\<^bold>\<not>a]" by simp
theorem K: "[\<^bold>\<box>(p \<^bold>\<rightarrow> q) \<turnstile>\<^sub>l \<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>q]" by simp
theorem Nec: "[a \<turnstile>\<^sub>g \<^bold>\<box>a]" by simp
theorem local_implies_global_conseq: "[a \<turnstile>\<^sub>l b] \<Longrightarrow> [a \<turnstile>\<^sub>g b]" by simp
theorem global_doesnt_imply_local_conseq: "[a \<turnstile>\<^sub>g b] \<Longrightarrow> [a \<turnstile>\<^sub>l b]" nitpick oops

(*Some useful notions regarding accessibility relations*)
  abbreviation "Symmetric  A \<equiv> \<forall> x.  \<forall> y. (A x y) \<longrightarrow> (A y x)"
  abbreviation "Reflexive  A \<equiv> \<forall> x. A x x"
  abbreviation "Transitive  A \<equiv> \<forall> x. \<forall> y. \<forall> z. (A x y) \<and> (A y z) \<longrightarrow> (A x z)"
  abbreviation "AxB \<equiv> Symmetric aRel"
  abbreviation "Ax4 \<equiv> Transitive aRel"
  abbreviation "AxS4 \<equiv> Reflexive aRel \<and> Transitive aRel"
  abbreviation "AxS5 \<equiv> Reflexive aRel \<and> Symmetric aRel \<and> Transitive aRel"

(*Possibilist quantification for objects of arbitrary type.*)  
  abbreviation mforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
  abbreviation mexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

end