(*<*)
theory MDLEmbedding imports Main
begin
(*>*)

section \<open>MDL Reasoning -- A Semantical Approach\<close>

text \<open>Direct automation of proof calculi such as natural deduction (ND)
      or Hilbert-style systems is usually unfeasible in practice.
      The calculi do not provide reasonable proof guidance for
      theorem proving systems and, thus, perform poorly.
      Popular calculi well-suited for automation are resolution,
      superposition, tableaux-based systems, connection calculi
      and many more. However, implementing such calculi is hard
      work and proving them correct can also be a large task.\<close>

text \<open>Another approach is to utilize the expressivity of Isabelle's
     underlying higher-order logic (HOL) to encode MDL's semantics
     into HOL and then use already existing automation methods
     for HOL for reasoning within MDL.\<close>

text \<open>The embedding explicitly encodes the Kripke-style semantics
      of MDL (Modal logic D) as follows:\<close>

typedecl i                   \<comment> \<open>type for possible worlds\<close>
type_synonym \<sigma> = "(i\<Rightarrow>bool)" \<comment> \<open>propositions are lifted to predicates on worlds\<close>

locale MDL =  
  fixes
    r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70) \<comment> \<open>the accessibility relation\<close>
  assumes
    seriality: "\<forall>w. \<exists>v. w r v" \<comment> \<open>the usual assumption for MDL\<close>
begin
text \<open>In the following, the definitions of all logical connectives
      are given with respect to their semantics.\<close>

 abbreviation mnot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53) 
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
 abbreviation mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) 
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) 
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
 abbreviation mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<equiv>"48) 
  where "\<phi>\<^bold>\<equiv>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
 abbreviation mobligatory :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circle>") 
  where "\<^bold>\<circle> \<phi> \<equiv> \<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi>(v)"
 abbreviation mforbidden :: "\<sigma>\<Rightarrow>\<sigma>" ("F") 
  where "F \<phi> \<equiv> \<^bold>\<circle> (\<^bold>\<not> \<phi>)"
 abbreviation mpermitted :: "\<sigma>\<Rightarrow>\<sigma>" ("P") 
  where "P \<phi> \<equiv> \<^bold>\<not> (\<^bold>\<circle> (\<^bold>\<not> \<phi>))"

 text \<open>The meta-logical notion valid is used to ground formulas
      of MDL to truth-values within HOL (i.e. Isabelle). It's
      definition is straight-forward: A MDL formula is (globally)
      valid iff it holds in every possible world.\<close>
 abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) 
   where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

 text \<open>We can also define local validity as validity in a
      certain given world w:\<close>
 abbreviation validInCW :: "\<sigma> \<Rightarrow> i \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>_"[7]8) 
  where "\<lfloor>p\<rfloor>\<^sub>w \<equiv> p w"
end

text \<open>Now we already have everything we need for reasoning within
      MDL. Using the definitions/abbreviations above, formulas
      that are inputted are being internally unfolded to HOL formulas
      and we can use every proof strategy of Isabelle to tackle them.\<close>

subsection \<open>Some properties of MDL\<close>

text \<open>We can easily verify the basic properties of MDL:\<close>

lemma (in MDL) D:
  "\<lfloor>\<^bold>\<not> ((\<^bold>\<circle>\<phi>) \<^bold>\<and> (\<^bold>\<circle>(\<^bold>\<not>\<phi>)))\<rfloor>" using seriality by smt 
lemma (in MDL) K: "\<lfloor>((\<^bold>\<circle>\<phi>) \<^bold>\<and> (\<^bold>\<circle>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<circle>\<psi>))\<rfloor>" by simp   
lemma (in MDL) NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<circle>\<phi>\<rfloor>" by simp \<comment> \<open>@{text "\<Longrightarrow>"} is meta-level implication\<close>
lemma (in MDL) RM: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<circle>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<circle>\<psi>)\<rfloor>" by simp

text \<open>We can also reason about MDL in this setting, e.g.
      for verifying that the axiom D corresponds to 
      serial frames:\<close>
lemma (in MDL) D_equivalent_to_seriality:
  "\<lfloor>\<^bold>\<not> ((\<^bold>\<circle>\<phi>) \<^bold>\<and> (\<^bold>\<circle>(\<^bold>\<not>\<phi>)))\<rfloor> \<equiv> (\<forall>w. \<exists>v. w r v)" by smt

text \<open>We can check for consistency of our theory at any time:\<close>
lemma (in MDL) True nitpick [satisfy,user_axioms,expect=genuine] oops  
  \<comment> \<open>Consistency is confirmed by Nitpick\<close>

text \<open>And we can get explicit (counter-) models generated for
      formulas that do not hold in general.\<close>
lemma (in MDL) MC: "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<^bold>\<circle>\<phi>)\<rfloor>"  \<comment> \<open>Modal Collapse\<close> 
  nitpick [user_axioms,expect=genuine] oops  
  \<comment> \<open>Counter model by Nitpick, that is, Modal Collapse for O does not hold\<close>

paragraph \<open>Examples from the exercises\<close>

text \<open>We define short hands for the both relation properties:\<close>
abbreviation transitive 
  where "transitive R \<equiv> \<forall>w v u. ((R w v) \<and> (R v u)) \<longrightarrow> R w u"
abbreviation euclidean
  where "euclidean R \<equiv> \<forall> s t u. ((R s t) \<and> (R s u)) \<longrightarrow> R t u"

subparagraph \<open>Exercise 1\<close>

text \<open>Does it hold that the formula @{text \<open>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle>(\<^bold>\<circle> \<phi>)\<close>}
     is valid if @{term "r"} is not transitive?\<close>

lemma (in MDL)
  assumes "\<not> (transitive (r))"
  shows "\<lfloor>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle>(\<^bold>\<circle> \<phi>)\<rfloor>"
  nitpick[expect=genuine, atoms = s t, card i = 2]
  oops

text \<open>No, there is a counter-model provided by nitpick. It
      The counter model can directly be reconstructed from
      nitpick's answer. \<close>

subparagraph \<open>Exercise 2\<close>

text \<open>Prove that @{text "\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle> \<psi>"} whenever @{text "\<phi> \<^bold>\<rightarrow> \<psi>"}.\<close>

lemma (in MDL) ROM: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle> \<psi>\<rfloor>" by simp

subparagraph \<open>Exercise 3\<close>

text \<open>Does it hold that the formula @{text \<open>\<^bold>\<not>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle>(\<^bold>\<not>\<^bold>\<circle> \<phi>)\<close>}
     is valid if @{term "r"} is euclidean?\<close>

lemma (in MDL) "3a":
  assumes "euclidean (r)"
  shows "\<lfloor>\<^bold>\<not>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle>(\<^bold>\<not>\<^bold>\<circle> \<phi>)\<rfloor>"
  nitpick[expect=none]
  sledgehammer
  using assms by blast

text \<open>Yes, nitpick does not find a counter-model and
      sledgehammer suggests a proof in under 5ms.\<close>

lemma (in MDL) "3b":
  assumes "\<not> euclidean (r)"
  shows "\<lfloor>\<^bold>\<not>\<^bold>\<circle> \<phi> \<^bold>\<rightarrow> \<^bold>\<circle>(\<^bold>\<not>\<^bold>\<circle> \<phi>)\<rfloor>"
  nitpick[expect=genuine,atoms = s t]
  oops

text \<open>On the contrary, if @{text "r"} is not euclidean,
      then the conjecture does not hold any more. Nitpick
     gives a minimal counter-model with two worlds s and t.\<close>


subsection \<open>Chisholm's Paradox in MDL\<close>

text \<open>Let's use the automation of MDL to assess Chisholm's paradox
      with automated reasoning mechanisms:\<close>

paragraph \<open>The set-up.\<close>
text \<open>We define a locale that gives raise to the vocabulary
      (and possibly additional assumptions) of an experiment
      scenario.\<close>

locale Chisholm = MDL +
  fixes \<comment> \<open>We fix local assumptions to our experiment.\<close>
    go :: \<sigma> and \<comment> \<open>both from Chisholm's paradox\<close>
    tell :: \<sigma> and
    kill :: \<sigma> and
    w :: i \<comment> \<open>current world\<close>
begin

text \<open>Define the axioms of the paradox as shorthands D1, D2, D3 and D4,
and, for D2 and D3, both the wide and narrow interpretation.\<close>

text \<open>It is obligatory to go and help.\<close>
abbreviation D1 where "D1 \<equiv> \<lfloor>\<^bold>\<circle> go\<rfloor>\<^sub>w" \<comment> \<open>everything local\<close>

text \<open>If you go, you must tell your neighbor.\<close>
abbreviation D2_wide ("D2\<^sup>w") where "D2\<^sup>w \<equiv> \<lfloor>\<^bold>\<circle> (go \<^bold>\<rightarrow> tell)\<rfloor>\<^sub>w"
abbreviation D2_narrow ("D2\<^sup>n") where "D2\<^sup>n \<equiv> \<lfloor>go \<^bold>\<rightarrow> \<^bold>\<circle>tell\<rfloor>\<^sub>w"

text \<open>If you do not go, do not tell your neighbor.\<close>
abbreviation D3_wide ("D3\<^sup>w") where "D3\<^sup>w \<equiv> \<lfloor>\<^bold>\<circle>( \<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>\<not>tell )\<rfloor>\<^sub>w"
abbreviation D3_narrow ("D3\<^sup>n") where "D3\<^sup>n \<equiv> \<lfloor>(\<^bold>\<not>go) \<^bold>\<rightarrow> (\<^bold>\<circle> (\<^bold>\<not>tell))\<rfloor>\<^sub>w"

text \<open>You do not go.\<close>
abbreviation D4 where "D4 \<equiv> \<lfloor>\<^bold>\<not> go\<rfloor>\<^sub>w"

text \<open>As can be seen above, we have defined two variants
      of D2 and D3, referred to as narrow- and wide-scope interpretations.
      We select the concrete D2/D3 by ...\<close>

abbreviation D2 where "D2 \<equiv> D2\<^sup>w" (* we can change it here to wide/narrow *)
abbreviation D3 where "D3 \<equiv> D3\<^sup>n" (* this way, we dont need to change the lemmas below *)

text \<open>We can access the definitions directly or just change to above two
lines if we want to change the interpretations for our experiments.\<close>


text \<open>You should kill the boss. Just as an example statement
      that we really do not want to be true.\<close>
abbreviation D5 where "D5 \<equiv> \<lfloor>\<^bold>\<circle> kill\<rfloor>\<^sub>w"
end

paragraph \<open>The experiments.\<close>
text \<open>Now we can start assessing the concrete examples:\<close>

subparagraph \<open>Inconsistency.\<close>
text \<open>We can prove falsity from the assumptions D1, D2, D3 and D4.\<close>
theorem (in Chisholm)
  assumes D1 and D2 and D3 and D4
  shows False
using seriality assms by fastforce

text \<open>This implies that the assumptions are inconsistent and we can prove
anything, e.g. that we should kill our Boss:\<close>

theorem (in Chisholm)
  assumes D1 and D2 and D3 and D4
  shows D5
  sledgehammer
  using assms seriality by blast

text \<open>Sledgehammer finds a proof for this in less than 5ms.\<close>

subparagraph \<open>Logical independence\<close>
text \<open>We can also assess logical independence. Depending
on the choice of narrow/wide scope interpretations, either
the theory will be inconsistent or logically dependent.\<close>

lemma (in Chisholm)
  assumes D2 and D3 and D4
  shows D1 nitpick[user_axioms, expect=genuine, show_all] oops

lemma (in Chisholm)
  assumes D1 and D3 and D4
  shows D2 nitpick[user_axioms, expect=genuine, show_all] oops

lemma (in Chisholm)
  assumes D1 and D2 and D4
  shows D3 nitpick[user_axioms, expect=genuine, show_all] oops

lemma (in Chisholm)
  assumes D1 and D2 and D3
  shows D4 nitpick[user_axioms, expect=genuine, show_all] oops

text \<open>Currently, the theory is logically independent (but inconsistent),
      as certified by nitpick (giving counter-models to the
      conjecture of logical dependence). These results of
      course change if D2 and D3 are chosen with other scope.\<close>


section \<open>Forrester's Paradox\<close>

text \<open>Just as above, we define a local scope for the experiments
      with Forrester's paradox:\<close>

locale Forrester = MDL +
  fixes 
    red :: \<sigma> and 
    scarlet :: \<sigma> and \<comment> \<open>both from Forrester's paradox\<close>
    w :: i \<comment> \<open>current world\<close>
  assumes
    scarlet_implies_red: "\<lfloor>scarlet \<^bold>\<rightarrow> red\<rfloor>"
begin

text \<open>You ought not dress red.\<close>
abbreviation F1
  where "F1 \<equiv> \<lfloor>\<^bold>\<circle>(\<^bold>\<not>red)\<rfloor>\<^sub>w"

text \<open>If you dress red, you ought dress scarlet\<close>
abbreviation F2_narrow ("F2\<^sup>n")
  where "F2\<^sup>n \<equiv> \<lfloor>(red \<^bold>\<rightarrow> \<^bold>\<circle>scarlet)\<rfloor>\<^sub>w"
abbreviation F2_wide ("F2\<^sup>w")
  where "F2\<^sup>w \<equiv> \<lfloor>\<^bold>\<circle>(red \<^bold>\<rightarrow> scarlet)\<rfloor>\<^sub>w"

text \<open>You dress red.\<close>
abbreviation F3
  where "F3 \<equiv> \<lfloor>red\<rfloor>\<^sub>w"

(* select the interpretation *)
abbreviation F2 
  where "F2 \<equiv> F2\<^sup>n"
end

lemma (in Forrester)
  assumes F1 and F2 and F3
  shows "False" 
  nitpick
  using assms scarlet_implies_red seriality by blast
text \<open>Again, the theory is inconsistent.\<close>

text \<open>Logical independence can again be assessed for different
      scope interpretations:\<close>

lemma  (in Forrester)
  assumes F1 and F2
  shows F3
  nitpick oops

lemma (in Forrester)
  assumes F1 and F3
  shows F2
  nitpick oops

lemma (in Forrester)
  assumes F2 and F3
  shows F1
  nitpick oops

  text_raw \<open>\pagebreak\<close>

section \<open>About using Cups.\<close>

locale Cup = MDL +
  fixes \<comment> \<open>We fix local assumptions to our experiment.\<close>
    useCup :: \<sigma> and \<comment> \<open>Using the cup\<close>
    putInDishwasher :: \<sigma> and \<comment> \<open>Putting the cup in the dishwasher\<close>
    w :: i \<comment> \<open>current world\<close>

  assumes "\<lfloor> putInDishwasher \<^bold>\<rightarrow> useCup \<rfloor>" \<comment> \<open>Implicit: If I put a cup in the dishwasher;
                                             I'm practically using it.\<close>
begin

  text \<open>You ought not use non-stock cups.\<close>
  abbreviation F1 where "F1 \<equiv> \<lfloor>\<^bold>\<circle>(\<^bold>\<not>useCup)\<rfloor>"

  text \<open>If you use non-stock cups, you ought to put them into the dishwasher\<close>
  abbreviation F2 ("F2")  where "F2 \<equiv> \<lfloor>(useCup \<^bold>\<rightarrow> \<^bold>\<circle>putInDishwasher)\<rfloor>" 
  
  text \<open>I use a non-stock cup.\<close>
  abbreviation F3 where "F3 \<equiv> \<lfloor>useCup\<rfloor>\<^sub>w"
  
  lemma
    assumes F1 and F2 and F3 
    shows "False"
    using Cup.axioms(2) Cup_axioms Cup_axioms_def D assms(1) assms(2) assms(3) by fastforce 

  text \<open>As a consequence, we see that we get in a crazy situation (Falsity is true!)
if using non-stock cups.\<close>
end

  text_raw \<open>\pagebreak\<close>

(*<*)
end
(*>*)