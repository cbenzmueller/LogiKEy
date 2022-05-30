theory DeepShallow imports Main begin  (*** Christoph Benzmüller, Nov 2021 ***)


 section\<open>Deep embedding\<close>

  text\<open>The signature \<open>\<Sigma>\<close>.\<close>   

typedecl \<Sigma>

  text\<open>The wff over \<open>\<Sigma>\<close>.\<close>  

datatype wff\<Sigma>  = atom \<Sigma> ("_\<^sup>a") | false ("\<^bold>f") | true ("\<^bold>t") | neg wff\<Sigma> ("\<^bold>\<not>") 
  | or wff\<Sigma> wff\<Sigma> (infix "\<^bold>\<or>" 92) | box wff\<Sigma> ("\<^bold>\<box> _" 93) 
print_theorems

typedecl World 

type_synonym AccessibilityRelation = "(World\<Rightarrow>World\<Rightarrow>bool)"

consts r::AccessibilityRelation (infix "\<^bold>r" 94)

type_synonym InterpretationFunction = "\<Sigma>\<Rightarrow>(World\<Rightarrow>bool)"

  text\<open>Next we provide a recursive definition of truth of a PL formula \<open>\<phi>\<close> in an 
     interpretation/model structure \<open>I\<close>, which we denote as \<open>I,w \<TTurnstile> \<phi>\<close>.\<close>

fun TruthInModel::"InterpretationFunction\<Rightarrow>World\<Rightarrow>wff\<Sigma>\<Rightarrow>bool" ("_,_ \<TTurnstile> _" 30) 
  where
    "(I,w \<TTurnstile> a\<^sup>a)  = I(a)(w)"
  | "(I,w \<TTurnstile> \<^bold>t)  = True"
  | "(I,w \<TTurnstile> \<^bold>f)  = False"
  | "(I,w \<TTurnstile> \<^bold>\<not>\<phi>) = (\<not>(I,w \<TTurnstile> \<phi>))"
  | "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<psi>)  = ((I,w \<TTurnstile> \<phi>) \<or> (I,w \<TTurnstile> \<psi>))"
  | "(I,w \<TTurnstile> \<^bold>\<box>\<phi>)  = (\<forall>v. w \<^bold>r v \<longrightarrow> (I,v \<TTurnstile> \<phi>)) "

   text\<open>Further logical connectives can be defined as usual.\<close>

(* definition true ("\<^bold>t") where "\<^bold>t \<equiv> \<^bold>\<not>\<^bold>f" *)
definition conj (infix "\<^bold>\<and>" 95) where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"
definition impl (infix "\<^bold>\<rightarrow>" 91) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<^bold>\<not>\<phi> \<^bold>\<or> \<psi>"
definition equi (infix "\<^bold>\<leftrightarrow>" 92) where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"
definition dia  ("\<^bold>\<diamond> _" 93) where "\<^bold>\<diamond>\<phi> \<equiv> \<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>\<phi>)"


  text\<open>We define a bag term\<open>Defs\<close> add the above definitions to it; we can then later unfold all
       these definitions exhaustively by just typing "unfolding Defs"\<close>

named_theorems Defs
declare (* true_def[Defs] *) conj_def[Defs] impl_def[Defs] equi_def[Defs] dia_def[Defs]


  text\<open>We may now perform various tests. Here are simple examples:\<close>

lemma PLtest1: "\<forall>I w \<phi>. (I,w \<TTurnstile> \<phi> \<^bold>\<or> \<^bold>\<not>\<phi>)" by simp  \<comment>\<open>proof\<close>
lemma PLtest2: "\<not>(\<exists>I w \<phi>. (I,w \<TTurnstile> \<phi> \<^bold>\<and> \<^bold>\<not>\<phi>))" using conj_def by auto  \<comment>\<open>proof\<close>

   subsection\<open>The base logic is a Boolean Algebra.\<close>

lemma Commutative1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<psi>) = (I,w \<TTurnstile> \<psi> \<^bold>\<or> \<phi>) " unfolding Defs apply simp by auto
lemma Commutative2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> \<psi>) = (I,w \<TTurnstile> \<psi> \<^bold>\<and> \<phi>) "unfolding Defs apply simp by auto
lemma Assoziative1[simp]: "(I,w \<TTurnstile> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<or> \<gamma>) = (I,w \<TTurnstile> \<phi> \<^bold>\<or> (\<psi> \<^bold>\<or> \<gamma>))" unfolding Defs by simp
lemma Idempotent1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<phi>) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp
lemma Idempotent2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> \<phi>) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp
lemma Distributive1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> (\<psi> \<^bold>\<or> \<gamma>)) = (I,w \<TTurnstile> (\<phi> \<^bold>\<and> \<psi>) \<^bold>\<or> (\<phi> \<^bold>\<and> \<gamma>))" unfolding Defs apply simp by auto
lemma Distributive2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> (\<psi> \<^bold>\<and> \<gamma>)) = (I,w \<TTurnstile> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<and> (\<phi> \<^bold>\<or> \<gamma>))" unfolding Defs apply simp by auto
lemma Neutral1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> \<^bold>t) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp
lemma Neutral2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<^bold>f) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp                   
lemma Extremal1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> \<^bold>f) = (I,w \<TTurnstile> \<^bold>f)" unfolding Defs by simp
lemma Extremal2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<^bold>t) = (I,w \<TTurnstile> \<^bold>t)" unfolding Defs by simp
lemma DoubleNeg[simp]: "(I,w \<TTurnstile> \<^bold>\<not>(\<^bold>\<not>\<phi>)) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp
lemma DeMorgan1[simp]: "(I,w \<TTurnstile> \<^bold>\<not>(\<phi> \<^bold>\<and> \<psi>)) = (I,w \<TTurnstile> \<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)" unfolding Defs by simp               
lemma DeMorgan2[simp]: "(I,w \<TTurnstile> \<^bold>\<not>(\<phi> \<^bold>\<or> \<psi>)) = (I,w \<TTurnstile> \<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>)" unfolding Defs by simp    
lemma Complement1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> \<^bold>\<not>\<phi>) = (I,w \<TTurnstile> \<^bold>f)" unfolding Defs by simp
lemma Complement2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> \<^bold>\<not>\<phi>) = (I,w \<TTurnstile> \<^bold>t)" unfolding Defs by simp
lemma Dual1[simp]: "(I,w \<TTurnstile> \<^bold>\<not>\<^bold>f \<^bold>\<leftrightarrow> \<^bold>t)" unfolding Defs by simp                
lemma Absorb1[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<or> (\<phi> \<^bold>\<and> \<psi>)) = (I,w \<TTurnstile> \<phi>)" unfolding Defs apply simp by auto
lemma Absorb2[simp]: "(I,w \<TTurnstile> \<phi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>)) = (I,w \<TTurnstile> \<phi>)" unfolding Defs by simp

definition orderBA  (infix "\<^bold>\<le>" 95) where "\<phi> \<^bold>\<le> \<psi> \<equiv>  \<phi> \<^bold>\<and> \<psi> = \<phi>"
definition "Atom \<phi> \<equiv> (\<phi> \<noteq> \<^bold>f) \<and> \<not>(\<exists>\<psi>. (\<psi> \<noteq> \<^bold>f) \<and> (\<phi> \<^bold>\<and> \<psi> = \<psi>))" 
declare orderBA_def[Defs] Atom_def[Defs] impl_def[Defs] equi_def[Defs]

lemma True nitpick[satisfy,user_axioms,show_all] oops
lemma False oops text\<open>timeout\<close>

  subsection\<open>Shallow Embedding\<close>
     
type_synonym \<sigma> = "World\<Rightarrow>bool" \<comment>\<open>World-lifted propositions\<close>

type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" \<comment>\<open>Unary modal connectives\<close>
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" \<comment>\<open>Binary modal connectives\<close>


   text\<open>Mapping of Signature\<close>


consts map\<Sigma>::"\<Sigma>\<Rightarrow>\<sigma>"
  
 
   text\<open>Mapping Function\<close>

fun map::"wff\<Sigma>\<Rightarrow>InterpretationFunction\<Rightarrow>\<sigma>" ("\<langle>_\<rangle>\<^sup>_" 112) 
  where 
    "\<langle>(a\<^sup>a)\<rangle>\<^sup>I = I(a)"
  |  "\<langle>\<^bold>t\<rangle>\<^sup>I = (\<lambda>w::World. True)"
  |  "\<langle>\<^bold>f\<rangle>\<^sup>I = (\<lambda>w::World. False)"
  | "\<langle>\<^bold>\<not>\<phi>\<rangle>\<^sup>I = (\<lambda>w::World. \<not>((\<langle>\<phi>\<rangle>\<^sup>I) w))"
  | "\<langle>\<phi> \<^bold>\<or> \<psi>\<rangle>\<^sup>I = (\<lambda>w::World. ((\<langle>\<phi>\<rangle>\<^sup>I) w) \<or> ((\<langle>\<psi>\<rangle>\<^sup>I) w))"
  | "\<langle>\<^bold>\<box>\<phi>\<rangle>\<^sup>I = (\<lambda>w::World. \<forall>v::World. (w\<^bold>rv) \<longrightarrow> ((\<langle>\<phi>\<rangle>\<^sup>I) v))"


text\<open>Meta-logical predicate for global validity:\<close>
definition valid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"
declare valid_def[Defs]


lemma S1: "(I,w \<TTurnstile> (a\<^sup>a)) \<longleftrightarrow> (\<langle>(a\<^sup>a)\<rangle>\<^sup>I)w" by auto
lemma S2: "(I,w \<TTurnstile> (\<^bold>t)) \<longleftrightarrow> (\<langle>(\<^bold>t)\<rangle>\<^sup>I)w" by auto
lemma S3: "(I,w \<TTurnstile> (\<^bold>f)) \<longleftrightarrow> (\<langle>(\<^bold>f)\<rangle>\<^sup>I)w" by auto
lemma S4: 
  assumes "(I,w \<TTurnstile> (\<phi>)) \<longleftrightarrow> (\<langle>(\<phi>)\<rangle>\<^sup>I)w" "(I,w \<TTurnstile> (\<psi>)) \<longleftrightarrow> (\<langle>(\<psi>)\<rangle>\<^sup>I)w"
  shows "(I,w \<TTurnstile> (\<phi> \<^bold>\<or> \<psi>)) \<longleftrightarrow> ((\<langle>(\<phi>)\<rangle>\<^sup>I)w \<or> (\<langle>(\<psi>)\<rangle>\<^sup>I)w)"
  using assms by auto
lemma S5: 
  assumes "(I,w \<TTurnstile> (\<phi>)) \<longleftrightarrow> (\<langle>(\<phi>)\<rangle>\<^sup>I)w" 
  shows "(I,w \<TTurnstile> \<^bold>\<not>\<phi>) \<longleftrightarrow> \<not>(\<langle>(\<phi>)\<rangle>\<^sup>I)w "
  using assms by auto
lemma S6: 
  assumes "\<forall>I w. (I,w \<TTurnstile> (\<phi>)) \<longleftrightarrow> (\<langle>(\<phi>)\<rangle>\<^sup>I)w" 
  shows "(I,w \<TTurnstile> \<^bold>\<box>\<phi>) \<longleftrightarrow> (\<langle>(\<^bold>\<box>\<phi>)\<rangle>\<^sup>I)w "
  using assms by simp


lemma All: "(I,w \<TTurnstile> (\<phi>)) \<longleftrightarrow> (\<langle>(\<phi>)\<rangle>\<^sup>I)w" 
  apply induction apply auto 
  using S1 S2 S3 S4 S5 S6 sledgehammer 


lemma Help: "\<forall>x. \<not> (I,w \<TTurnstile> x) \<longrightarrow> \<not> (\<langle>x\<rangle>\<^sup>I) w" sledgehammer
   apply induction apply auto nitpick

lemma Soundness: assumes "(I,w \<TTurnstile> \<phi>)" shows "(\<langle>\<phi>\<rangle>\<^sup>I)w" 
  sledgehammer
  using assms unfolding Defs 
  apply induction
  apply auto
  sledgehammer
  


  text\<open>Logical connectives (operating on truth-sets):\<close>
abbreviation c1::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu> (infix"\<^bold>\<and>"50) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu> (infix"\<^bold>\<or>"49) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu> (infix"\<^bold>\<rightarrow>"48) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu> (infix"\<^bold>\<leftrightarrow>"47) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation c8::\<mu> ("\<^bold>\<box>_"[54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<^bold>rv)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu> ("\<^bold>\<diamond>_"[54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<^bold>rv)\<and>(\<phi> v)"


text\<open>Meta-logical predicate for global validity:\<close>
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"


lemma "\<forall>F::wff\<Sigma>. True"






  text\<open>Barcan and converse Barcan formula:\<close>
lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops \<comment>\<open>Ctm\<close>
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops \<comment>\<open>Ctm\<close>
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)\<rfloor>" by simp 
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp



datatype \<phi> = Cff \<phi>b ("_\<^sup>f") |  Var var ("_\<^sup>v") | Cons \<phi> | And \<phi> \<phi> (infix "&" 55) | Neg \<phi> ("~") 
print_theorems     

  text\<open>As for the base logic we provide a recursive function \<open>I,\<alpha> \<TTurnstile> \<phi>\<close> defining truth of 
   an abstract level formula \<open>f\<close> of type \<open>\<phi>\<close> for model structure \<open>I\<close> under assignment 
   \<open>\<alpha>\<close>. Note how the clause for consistency uses existential quantification over 
   model structures an variable assignments.\<close> 

  text\<open>Note on the use of function versus fun: fun comes from the function package and is a 
   simplified version of function that tries to prove exhaustiveness, non-overlappedness of patterns, 
   and termination automatically. This works for most functions that arise in practice; when it does not, 
   one has to use function and prove these things by hand.\<close>


fun TruthInModelUpper1::"\<phi>bModel\<Rightarrow>(var\<Rightarrow>\<phi>b)\<Rightarrow>\<phi>\<Rightarrow>bool" ("_,_ \<Turnstile>\<^sup>1 _" 30) 
  where
    "( I,\<alpha> \<Turnstile>\<^sup>1 \<phi> & \<psi> ) = ( (I,\<alpha> \<Turnstile>\<^sup>1 \<phi>) \<and> (I,\<alpha> \<Turnstile>\<^sup>1 \<psi>))"
  | "( I,\<alpha> \<Turnstile>\<^sup>1 ~\<phi>) = (~ (I,\<alpha> \<Turnstile>\<^sup>1 \<phi>))" 
  | "( I,\<alpha> \<Turnstile>\<^sup>1 (\<phi>b)\<^sup>f ) = (I,w \<TTurnstile> \<phi>b)"
  | "( I,\<alpha> \<Turnstile>\<^sup>1 Cons(\<phi>)) = (\<exists>J. J,\<alpha> \<Turnstile>\<^sup>1 \<phi>)"
  | "( I,\<alpha> \<Turnstile>\<^sup>1 (x)\<^sup>v )  = (I,w \<TTurnstile> \<alpha>(x))"


consts TruthInModelUpper2::"\<phi>bModel\<Rightarrow>(var\<Rightarrow>\<phi>)\<Rightarrow>\<phi>\<Rightarrow>bool" ("_,_ \<Turnstile>\<^sup>2 _" 30) 

axiomatization where 
  A1[simp]: "( I,\<alpha> \<Turnstile>\<^sup>2 \<phi> & \<psi> ) = ( (I,\<alpha> \<Turnstile>\<^sup>2 \<phi>) \<and> (I,\<alpha> \<Turnstile>\<^sup>2 \<psi>))" and
  A2[simp]: "( I,\<alpha> \<Turnstile>\<^sup>2 ~\<phi>) = (~ (I,\<alpha> \<Turnstile>\<^sup>2 \<phi>))" and
  A3[simp]: "( I,\<alpha> \<Turnstile>\<^sup>2 (\<phi>b)\<^sup>f ) = (I,w \<TTurnstile> \<phi>b)" and
  A4[simp]: "( I,\<alpha> \<Turnstile>\<^sup>2 Cons(\<phi>)) = (\<exists>J. J,\<alpha> \<Turnstile>\<^sup>2 \<phi>)" and
  A5[simp]: "( I,\<alpha> \<Turnstile>\<^sup>2 (x)\<^sup>v )  = (I,\<alpha> \<Turnstile>\<^sup>2 \<alpha>(x))"

lemma  "wfP (\<lambda>(x::\<phi>) y. size x < size y)" 
  by (metis (no_types, lifting) infinite_descent_measure wfPUNIVI) 




lemma True nitpick[satisfy,user_axioms] oops
lemma False sledgehammer oops 

   text\<open>We need to provide a notion of variable assignment update/modification.\<close>

definition modifyValuation::"(var\<Rightarrow>\<phi>)\<Rightarrow>var\<Rightarrow>\<phi>\<Rightarrow>(var\<Rightarrow>\<phi>)" ("_\<lparr>_\<mapsto>_\<rparr>" 10)
  where "(V\<lparr>x\<mapsto>b\<rparr>)(y) \<equiv> (if x = y then b else V(y))"
declare modifyValuation_def[Defs]

lemma Help1: "x = y \<longrightarrow> (\<alpha>\<lparr>x\<mapsto>b\<rparr>)(y) = b" unfolding Defs by simp
lemma Help2: "x \<noteq> y \<longrightarrow> (\<alpha>\<lparr>x\<mapsto>b\<rparr>)(y) = \<alpha>(y)" unfolding Defs by simp


fun subst::"(var\<Rightarrow>\<phi>)\<Rightarrow>\<phi>\<Rightarrow>\<phi>" ("S\<^sup>__") 
  where 
    "S\<^sup>\<alpha>(\<phi> & \<psi>) = (S\<^sup>\<alpha> \<phi>) & (S\<^sup>\<alpha> \<psi>)"
  | "S\<^sup>\<alpha>(~\<phi>) = ~(S\<^sup>\<alpha> \<phi>)"
  | "S\<^sup>\<alpha>(\<phi>b)\<^sup>f = (\<phi>b)\<^sup>f"
  | "S\<^sup>\<alpha>(Cons(\<phi>)) = Cons(S\<^sup>\<alpha> \<phi>)"
  | "S\<^sup>\<alpha>(x)\<^sup>v = \<alpha>(x)"


function TruthInModelUpper2::"\<phi>bModel\<Rightarrow>(var\<Rightarrow>\<phi>)\<Rightarrow>\<phi>\<Rightarrow>bool" ("_,_ \<Turnstile>_" 30) 
  where
    "( I,\<alpha> \<Turnstile> \<phi> & \<psi> ) = ( (I,\<alpha> \<Turnstile> \<phi>) \<and> (I,\<alpha> \<Turnstile> \<psi>))"
  | "( I,\<alpha> \<Turnstile> ~\<phi>) = (~ (I,\<alpha> \<Turnstile> \<phi>))" 
  | "( I,\<alpha> \<Turnstile> (\<phi>b)\<^sup>f ) = (I,w \<TTurnstile> \<phi>b)"
  | "( I,\<alpha> \<Turnstile> Cons(\<phi>)) = (\<exists>J. J,\<alpha> \<Turnstile> \<phi>)"
  | "( I,\<alpha> \<Turnstile> (x)\<^sup>v )  = (I,\<alpha> \<Turnstile> S\<^sup>\<alpha>((x)\<^sup>v))"
  by pat_completeness auto
   

function TruthInModelUpper3::"\<phi>bModel\<Rightarrow>((var\<Rightarrow>\<phi>)\<Rightarrow>\<phi>\<Rightarrow>\<phi>)\<Rightarrow>(var\<Rightarrow>\<phi>)\<Rightarrow>\<phi>\<Rightarrow>bool" ("_,_\<^sup>_ \<Turnstile>_" 30) 
  where
    "( I,Subst\<^sup>\<alpha> \<Turnstile> \<phi> & \<psi> ) = ( (I,Subst\<^sup>\<alpha> \<Turnstile> \<phi>) \<and> (I,Subst\<^sup>\<alpha> \<Turnstile> \<psi>))"
  | "( I,Subst\<^sup>\<alpha> \<Turnstile> ~\<phi>) = (~ (I,Subst\<^sup>\<alpha> \<Turnstile> \<phi>))" 
  | "( I,Subst\<^sup>\<alpha> \<Turnstile> (\<phi>b)\<^sup>f ) = (I,w \<TTurnstile> \<phi>b)"
  | "( I,Subst\<^sup>\<alpha> \<Turnstile> Cons(\<phi>)) = (\<exists>J. J,Subst\<^sup>\<alpha> \<Turnstile> \<phi>)"
  | "( I,Subst\<^sup>\<alpha> \<Turnstile> (x)\<^sup>v )  = (I,Subst\<^sup>\<alpha> \<Turnstile> \<alpha>(x))"
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(_,_,x). size x)\<close>)  

  text\<open>Next we introduce the inductively defined datatype \<open>\<phi>\<close> of formulas at abstract layer.
     At this layer a logical connective for consistency is added. Note also that we use a different 
     syntax for the logical connectives at upper layer to better distinguish them from those of 
     the imported logic.\footnote{Enrico wrote in his first document draft: "At most one variable occurrence per formula". This can eventually 
     not be realised that easily, but might not be needed.)}\<close> 


  text\<open>Further logical connectives can be defined as usual.\<close>

definition conj' (infix "|" 55) where "(\<phi>::\<phi>) | \<psi> \<equiv> ~(~\<phi> & ~\<psi>)"
definition impl' (infix "\<Rightarrow>" 52) where "(\<phi>::\<phi>) \<Rightarrow> \<psi> \<equiv> ~\<phi> | \<psi>"
definition equi' (infix "\<Leftrightarrow>" 53) where "(\<phi>::\<phi>) \<Leftrightarrow> \<psi> \<equiv> (\<phi> \<Rightarrow> \<psi>) & (\<psi> \<Rightarrow> \<phi>)"

declare conj'_def[Defs] impl'_def[Defs] equi'_def[Defs]

   text\<open>We can now define two notions of satisfiablity.\<close> 

definition "SAT \<phi> \<equiv> (\<exists>I \<alpha>. (I,\<alpha> \<TTurnstile> \<phi>))"
(* definition "MSAT (\<phi>1::\<phi>) (\<phi>2::\<phi>\<Rightarrow>\<phi>) \<equiv> SAT (\<phi>2 \<phi>1)" *)

definition "MSAT \<phi>1 \<phi>2 x \<equiv> (\<exists>I \<alpha>. I,\<alpha>\<lparr>x\<mapsto>\<phi>1\<rparr> \<TTurnstile> \<phi>2)"


declare SAT_def[Defs] MSAT_def[Defs] 

   text\<open>We can also add a standard notion of logical entailment.\<close> 

definition entails (infix "\<^bold>\<TTurnstile>" 52) where "\<phi> \<^bold>\<TTurnstile> \<psi> \<equiv> (\<forall>I \<alpha>. (I,\<alpha> \<TTurnstile> \<phi>) \<longrightarrow> (I,\<alpha> \<TTurnstile> \<psi>))"

   text\<open>The introduced theory is consistent in HOL; nitpick reports a trivial model.\<close>

nitpick_params[user_axioms,expect=genuine,show_all,format=2]

lemma True nitpick[satisfy] oops

  section\<open>First Tests and Examples.\<close>

  text\<open>We can now put our modeling at test and check for various examples.\<close>

lemma L1: "\<forall>\<phi>. SAT \<^bold>t\<^sup>f" unfolding Defs by simp 
  by (simp add: A3) \<comment>\<open>proof\<close>


lemma "\<exists>\<phi>. SAT \<phi>" unfolding Defs using A2 by blast

(*
  text\<open>\<open>Nitpicking goal:
  \<exists>\<phi> I \<alpha>. I,\<alpha> \<TTurnstile>\<phi>. 
Nitpick found a model:
  Skolem constants:
    I = (\<lambda>x. _)(\<Sigma>\<^sub>1 := True),
    \<alpha> = (\<lambda>x. _)(v\<^sub>1 := \<Sigma>\<^sub>1\<^sup>a),
    \<phi> = v\<^sub>1\<^sup>v.\<close>\<close>
*)

lemma "\<exists>\<phi> \<psi> x. MSAT \<phi> \<psi> x" unfolding Defs  nitpick[satisfy] \<comment>\<open>model\<close>
  by (meson A2)


lemma "\<exists>\<phi> \<psi> x. \<not>MSAT \<phi> \<psi> x" unfolding Defs nitpick[satisfy,timeout=200] \<comment>\<open>model\<close>
  using A1 A2 by blast
(*
  text\<open>\<open>Nitpicking goal:
  \<exists>\<phi> \<psi> x. \<not>\<exists>I \<alpha>. I,\<lambda>y. if x = y then \<phi> else \<alpha> y \<TTurnstile>\<psi>.
Nitpick found a potentially spurious model:
  Skolem constants:
    \<phi> = \<^bold>f
    \<psi> = v\<^sub>1\<^sup>v
    x = v\<^sub>1.\<close>\<close> 
*)

lemma "\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> (x1)\<^sup>v | ~(x1)\<^sup>v )" unfolding Defs using A1 A2 by fastforce
lemma "\<not>(\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> (x1)\<^sup>v | ~((symB\<^sup>a)\<^sup>f)) )" unfolding Defs apply simp 
  apply (rule exI [where x = "(\<lambda>y. True)"]) apply simp 
  by (metis A2 A3 Help1)


lemma "\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> ((symB\<^sup>a)\<^sup>f) | ~((symB\<^sup>a)\<^sup>f) )" unfolding Defs by simp  \<comment>\<open>proof\<close>
lemma "\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> ((symB\<^sup>a) \<^bold>\<or> \<^bold>\<not>(symB\<^sup>a)\<^sup>f) )" unfolding Defs by simp  \<comment>\<open>proof\<close>

lemma "\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> (((symB\<^sup>a)\<^sup>f) | ~((symB\<^sup>a)\<^sup>f)) \<Leftrightarrow> ((symB\<^sup>a) \<^bold>\<or> \<^bold>\<not>(symB\<^sup>a))\<^sup>f)" unfolding Defs by simp  \<comment>\<open>proof\<close>

lemma "\<forall>I \<alpha> \<phi> \<psi>. ( I,\<alpha> \<TTurnstile> (((\<phi>)\<^sup>f) | ~((\<psi>)\<^sup>f)) \<Leftrightarrow> (((\<phi>) \<^bold>\<or> \<^bold>\<not>(\<psi>))\<^sup>f) )" unfolding Defs apply simp by meson  \<comment>\<open>proof\<close>


  text\<open>Some further tests as suggested by Enrico (they have been further adapted).\<close>


axiomatization where 
   ax1: "\<forall>I \<alpha>. ( I,\<alpha> \<TTurnstile> P \<Leftrightarrow> (((Cons (P & x)) \<Rightarrow> A) & ((~(Cons (P & x))) \<Rightarrow> A)))"

lemma True nitpick[satisfy,user_axioms]

(*
abbreviation "F1 Q y A \<equiv> ((Q)\<^sup>f \<Leftrightarrow> (((Cons ((Q)\<^sup>f & (y)\<^sup>v)) \<Rightarrow> ~(A)\<^sup>f) | ((~(Cons ((Q)\<^sup>f & (y)\<^sup>v))) \<Rightarrow> (A)\<^sup>f)))"
abbreviation "F2pred P A \<equiv> \<lambda>x. ((P)\<^sup>f \<Leftrightarrow> (((Cons ((P)\<^sup>f & x)) \<Rightarrow> (A)\<^sup>f) | ((~(Cons ((P)\<^sup>f & x))) \<Rightarrow> ~(A)\<^sup>f)))"
*)

lemma "(\<exists>Q y P A. 
   MSAT  ((Q\<^sup>f) \<Leftrightarrow> (((Cons ((Q\<^sup>f) & (y\<^sup>v))) \<Rightarrow> (~(A\<^sup>f))) | ((~(Cons ((Q\<^sup>f) & (y\<^sup>v)))) \<Rightarrow> (A\<^sup>f)))) 
         (\<lambda>x. ((P\<^sup>f) \<Leftrightarrow> (((Cons ((P\<^sup>f) & x)) \<Rightarrow> (A\<^sup>f)) | ((~(Cons ((P\<^sup>f) & x))) \<Rightarrow> (~(A\<^sup>f)))))))" 
  unfolding Defs apply simp 
  text\<open> This is what we get at this point:
\<open>proof (prove)
goal (1 subgoal):
 1. \<exists>Q P A I.
       (I,w \<TTurnstile> P \<longrightarrow> (\<forall>J. J \<TTurnstile> P \<longrightarrow> \<not> (J \<TTurnstile> Q)) \<or> (I,w \<TTurnstile> A) \<or> (\<exists>J. (J \<TTurnstile> P) \<and> (J \<TTurnstile> Q)) \<or> \<not> (I,w \<TTurnstile> A)) \<and>
       ((\<exists>J. (J \<TTurnstile> P) \<and> (J \<TTurnstile> Q)) \<and> \<not> (I,w \<TTurnstile> A) \<and> (\<forall>J. J \<TTurnstile> P \<longrightarrow> \<not> (J \<TTurnstile> Q)) \<and> (I,w \<TTurnstile> A) \<or> I,w \<TTurnstile> P)
   \<close>\<close>
  nitpick[satisfy]  \<comment>\<open>model\<close>
text\<open> This is what nitpick tells us:
\<open>Nitpicking goal:
  \<exists>Q P A I.
     (I,w \<TTurnstile> P \<longrightarrow> (\<forall>J. J \<TTurnstile> P \<longrightarrow> \<not> (J \<TTurnstile> Q)) \<or> (I,w \<TTurnstile> A) \<or> (\<exists>J. (J \<TTurnstile> P) \<and> (J \<TTurnstile> Q)) \<or> \<not> (I,w \<TTurnstile> A)) \<and>
     ((\<exists>J. (J \<TTurnstile> P) \<and> (J \<TTurnstile> Q)) \<and> \<not> (I,w \<TTurnstile> A) \<and> (\<forall>J. J \<TTurnstile> P \<longrightarrow> \<not> (J \<TTurnstile> Q)) \<and> (I,w \<TTurnstile> A) \<or> I,w \<TTurnstile> P) 
Nitpick found a model:
  Skolem constants:
    A = \<Sigma>\<^sub>1\<^sup>a
    I = (\<lambda>x. _)(\<Sigma>\<^sub>1 := True)
    J = (\<lambda>x. _)(\<Sigma>\<^sub>1 := False)
    J = (\<lambda>x. _)(\<Sigma>\<^sub>1 := False)
    P = \<Sigma>\<^sub>1\<^sup>a
    Q = \<Sigma>\<^sub>1\<^sup>a\<close>\<close>
 by (metis TruthInModel.simps(3))  \<comment>\<open>proof\<close>

lemma "(\<exists>Q y P A B. 
  MSAT  ((Q\<^sup>f) \<Leftrightarrow> (((Cons ((Q\<^sup>f) & (y\<^sup>v))) \<Rightarrow> (~(A\<^sup>f))) | ((~(Cons ((Q\<^sup>f) & (y\<^sup>v)))) \<Rightarrow> (A\<^sup>f)))) 
        (\<lambda>x. ((P\<^sup>f) \<Leftrightarrow> (((Cons ((P\<^sup>f) & x)) \<Rightarrow> (B\<^sup>f)) | ((~(Cons ((P\<^sup>f) & x))) \<Rightarrow> (~(B\<^sup>f)))))))" 
  unfolding Defs apply simp 
  nitpick[satisfy]  \<comment>\<open>model\<close>
  by (metis TruthInModel.simps(3))  \<comment>\<open>proof\<close>

lemma "\<not>(\<forall>Q y P A. 
  MSAT  ((Q\<^sup>f) \<Leftrightarrow> (((Cons ((Q\<^sup>f) & (y\<^sup>v))) \<Rightarrow> (~(A\<^sup>f))) | ((~(Cons ((Q\<^sup>f) & (y\<^sup>v)))) \<Rightarrow> (A\<^sup>f)))) 
        (\<lambda>x. ((P\<^sup>f) \<Leftrightarrow> (((Cons ((P\<^sup>f) & x)) \<Rightarrow> (A\<^sup>f)) | ((~(Cons ((P\<^sup>f) & x))) \<Rightarrow> (~(A\<^sup>f)))))))" 
  unfolding Defs apply simp 
  using TruthInModel.simps(2) by blast

lemma "\<not>(\<forall>Q y P A B. 
  MSAT  ((Q\<^sup>f) \<Leftrightarrow> (((Cons ((Q\<^sup>f) & (y\<^sup>v))) \<Rightarrow> (~(A\<^sup>f))) | ((~(Cons ((Q\<^sup>f) & (y\<^sup>v)))) \<Rightarrow> (A\<^sup>f)))) 
        (\<lambda>x. ((P\<^sup>f) \<Leftrightarrow> (((Cons ((P\<^sup>f) & x)) \<Rightarrow> (B\<^sup>f)) | ((~(Cons ((P\<^sup>f) & x))) \<Rightarrow> (~(B\<^sup>f)))))))" 
  unfolding Defs apply simp
  using TruthInModel.simps(2) by blast

end


(*
lemma "MSAT (Q\<^sup>f \<Leftrightarrow> (((Cons (Q\<^sup>f & y\<^sup>v)) \<Rightarrow> ~A\<^sup>f) | ((~(Cons (Q\<^sup>f & y\<^sup>v))) \<Rightarrow> A\<^sup>f)))
            (P\<^sup>f \<Leftrightarrow> (((Cons (P\<^sup>f & y\<^sup>v)) \<Rightarrow> ~A\<^sup>f) | ((~(Cons (P\<^sup>f & y\<^sup>v))) \<Rightarrow> A\<^sup>f))) 
            x" 
*)

(*
lemma "MSAT (Q \<leftrightarrow> ((Cons(Q \<^bold>\<and> y) \<^bold>\<rightarrow> \<^bold>\<not>A) \<^bold>\<or> (\<^bold>\<not>Cons (Q \<^bold>\<and> y) \<^bold>\<rightarrow> A)))
            (P \<^bold>\<leftrightarrow> ((Cons(P \<^bold>\<and> x) \<^bold>\<rightarrow> A) \<^bold>\<or> (\<^bold>\<not>Cons (P \<^bold>\<and> x) \<^bold>\<rightarrow> \<^bold>\<not>A))
            x"
*)
