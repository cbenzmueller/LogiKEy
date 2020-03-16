(*<*) 
theory HybridLogic
imports Main 

begin
(*>*)

  text \<open>
  For the embedding of NHOML into HOL we can use mostly the same
  embedding as HOML to HOL. We introduce i for individuals, \<tau> for
  the worlds, that are points in time, and a new type \<eta> for nominals.

  We define an ordering relation <t for the worlds, that works
  as the accessibility relation and a relation for the nominals
  that associates nominals with points in time. As can be read in Blackburn
  the valuation maps a nominal to a singleton set taken from the powerset of the worlds.
\<close>
  typedecl i    \<comment> \<open>the type for indiviuals\<close>   
  typedecl \<tau>    \<comment> \<open>the type for worlds\<close>
  typedecl \<eta>    \<comment> \<open>the type of nomimals\<close>
  
  consts order :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool" (infixl "t<" 70) \<comment> \<open>accessibility relation on worlds\<close>
  consts worldAt :: "\<eta> \<Rightarrow> \<tau> \<Rightarrow> bool" (infixl "@@" 70) \<comment> \<open>nominal - world - relation\<close>


  text \<open>
  We axiomatize the relation for the mapping of nominals to worlds
  as functions. Opposing to Blackburn we declare the mapping
  as surjective. Without surjectivity the lemmas L1x - L6x cannot
  be proven.
\<close>

  axiomatization where
    rightUnique: "\<forall>i. \<forall>t. \<forall>t'. i @@ t \<and> i @@ t' \<longrightarrow> t = t'" and
    leftTotal: "\<forall>i. \<exists>t. i @@ t" and
    surjective: "\<forall>t. \<exists>i. i @@ t"  

  text \<open>
  Adopted from QML embedding by Benzmueller and Paleo
\<close>

  type_synonym \<sigma> = "(\<tau> \<Rightarrow> bool)"

  abbreviation tTop :: "\<sigma>" ("tT") where "tT \<equiv> (\<lambda>t. True)"
  abbreviation tnot :: "\<sigma> \<Rightarrow> \<sigma>" ("t\<not>") where "t\<not> \<phi> \<equiv> (\<lambda>t. \<not> \<phi> t)"    
  abbreviation tand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "t\<and>" 51) where "\<phi> t\<and> \<psi> \<equiv> (\<lambda>t. \<phi> t \<and> \<psi> t)"   
  abbreviation tor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "t\<or>" 50) where "\<phi> t\<or> \<psi> \<equiv> (\<lambda>t. \<phi> t \<or> \<psi> t)"   
  abbreviation timplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "t\<rightarrow>" 49) where "\<phi> t\<rightarrow> \<psi> \<equiv> (\<lambda>t. \<phi> t \<longrightarrow> \<psi> t)"  
  abbreviation tequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "t\<equiv>" 48) where "\<phi> t\<equiv> \<psi> \<equiv> (\<lambda>t. \<phi> t \<longleftrightarrow> \<psi> t)"  
  abbreviation tP :: "\<sigma> \<Rightarrow> \<sigma>" ("P") where "P \<phi> \<equiv> (\<lambda>t. \<exists>t'.  t' t< t  \<and> \<phi> t')"
  abbreviation tF :: "\<sigma> \<Rightarrow> \<sigma>" ("F") where "F \<phi> \<equiv> (\<lambda>t. \<exists>t'.  t  t< t' \<and> \<phi> t')"
  abbreviation tH :: "\<sigma> \<Rightarrow> \<sigma>" ("H") where "H \<phi> \<equiv> (\<lambda>t. \<forall>t'.  t' t< t  \<longrightarrow> \<phi> t')"
  abbreviation tG :: "\<sigma> \<Rightarrow> \<sigma>" ("G") where "G \<phi> \<equiv> (\<lambda>t. \<forall>t'.  t  t< t' \<longrightarrow> \<phi> t')"

  text \<open>
    The L operator as stated by Blackburn
\<close>
  abbreviation tL :: "\<sigma> \<Rightarrow> \<sigma>" ("L") where "L \<phi> \<equiv> (\<lambda>t. \<forall>t'.  \<phi> t')"
  

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>t. p t"

  text \<open>
    Similar to [_], we define a conversion from nominals to
    propositions by <_>. 
\<close>
  abbreviation nom :: "\<eta> \<Rightarrow> \<sigma>" ("<_>") where "<i> \<equiv> \<lambda>t. i @@ t "

  lemma True nitpick [satisfy, user_axioms=true, expect = genuine] oops
  
  (* Lemma L1x: Irreflexivity *)
  lemma L1a:
    assumes "\<forall>i.[<i> t\<rightarrow> t\<not> (F <i>)]"
    shows "\<forall>x.\<not>(x t< x)"
  by (metis assms surjective)

  lemma L1b:
    assumes "\<forall>x.\<not>(x t< x)"
    shows "\<forall>i.[<i> t\<rightarrow> t\<not> (F <i>)]"
  by (metis assms rightUnique)

  (* Lemma L2x: Asymmetry *)
  lemma L2a:
   assumes "\<forall>i.[<i> t\<rightarrow> t\<not> (F (F <i>))]"
   shows "\<forall>x.\<forall>y. x t< y \<longrightarrow> \<not>(y t< x)"
  by (metis assms surjective)

  lemma L2b:
   assumes "\<forall>x.\<forall>y. x t< y \<longrightarrow> \<not>(y t< x)"   
   shows "\<forall>i.[<i> t\<rightarrow> t\<not> (F (F <i>))]"
  by (metis assms rightUnique)

  (* Lemma L3x: Antisymmetry *)
  lemma L3a:
   assumes "\<forall>i.[<i> t\<rightarrow> G (F <i> t\<rightarrow> <i>)]"
   shows "\<forall>x.\<forall>y. (x t< y \<and> y t< x) \<longrightarrow> x = y"
  by (metis assms rightUnique surjective)

  lemma L3b:
   assumes "\<forall>x.\<forall>y. (x t< y \<and> y t< x) \<longrightarrow> x = y" 
   shows "\<forall>i.[<i> t\<rightarrow> G (F <i> t\<rightarrow> <i>)]"
  by (metis assms rightUnique)

  (* Lemma L4x: Trichotomy (total relation) *)
  lemma L4a:
   assumes "\<forall>i.[(P <i>) t\<or> <i> t\<or> (F <i>)]"
   shows "\<forall>x.\<forall>y. ((x t< y) \<or> (x = y) \<or> (y t< x))"
  by (metis assms rightUnique surjective)

  lemma L4b:
   assumes "\<forall>x.\<forall>y. ((x t< y) \<or> (x = y) \<or> (y t< x))" 
   shows "\<forall>i.[(P <i>) t\<or> <i> t\<or> (F <i>)]"
  by (metis assms leftTotal)

  (* Lemma L5x: right directed *)
  lemma L5a:
   assumes "\<forall>i.[F (P <i>)]"
   shows "\<forall>x.\<forall>y.\<exists>z. x t< z \<and> y t< z"
  by (metis assms rightUnique surjective)

  lemma L5b:
   assumes "\<forall>x.\<forall>y.\<exists>z. x t< z \<and> y t< z" 
   shows "\<forall>i.[F (P <i>)]"
  by (metis assms leftTotal)

  (* Lemma L6x: right discrete *)
  lemma L6a:
   assumes "\<forall>i.[<i> t\<rightarrow> ((F tT) t\<rightarrow> F (H (H (t\<not> <i>))))]"
   shows "\<forall>x.\<forall>y. x t< y \<longrightarrow> (\<exists>z. x t< z \<and> \<not>(\<exists>w. x t< w \<and> w t< z))"
  by (metis assms surjective)

  lemma L6b:
   assumes "\<forall>x.\<forall>y. x t< y \<longrightarrow> (\<exists>z. x t< z \<and> \<not>(\<exists>w. x t< w \<and> w t< z))"
   shows "\<forall>i.[<i> t\<rightarrow> ((F tT) t\<rightarrow> F (H (H (t\<not> <i>))))]"
  by (metis assms rightUnique)
end
