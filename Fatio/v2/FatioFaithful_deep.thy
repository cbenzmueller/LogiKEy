section\<open>Deep embedding: content logic, Fatio language, BD logic\<close>

theory FatioFaithful_deep
  imports FatioFaithful_preliminaries
begin

subsection\<open>Content logic (deeply embedded, propositional)\<close>

text\<open>\<^emph>\<open>Scope note.\<close> The content logic is embedded deeply with a semantics of its own
(see below), and shallowly in the shallow theory; the two are related by
\<open>Faithful0a\<close>/\<open>Faithful0b\<close> in the faithfulness theory. Its meaning is moreover tied
to the BD logic by the injection \<open>{_}\<^sup>d\<close>, which is truth-preserving
(\<open>MapC_faithful\<close>). The deep/shallow/faithfulness triangle of this entry therefore
covers \<^emph>\<open>both\<close> object logics. What the content layer deliberately does not carry is
a notion of argumentative support: the entailment atoms of the BD logic are
interpreted freely, and the optional bridge in the variants theory shows what
constraining them by content-logic entailment would cost.\<close>

datatype Formula = AtmC \<S> ("_\<^sup>c" [1000] 999) | NegC Formula ("\<not>\<^sup>c_" [96] 96)
                 | ImpC Formula Formula (infixr "\<supset>\<^sup>c" 93)
definition AndC (infixr "\<and>\<^sup>c" 95) where "\<phi> \<and>\<^sup>c \<psi> \<equiv> \<not>\<^sup>c(\<phi> \<supset>\<^sup>c \<not>\<^sup>c\<psi>)"
definition OrC  (infixr "\<or>\<^sup>c" 92) where "\<phi> \<or>\<^sup>c \<psi> \<equiv> \<not>\<^sup>c\<phi> \<supset>\<^sup>c \<psi>"
definition TopC ("\<top>\<^sup>c") where "\<top>\<^sup>c \<equiv> (SOME x. True)\<^sup>c \<supset>\<^sup>c (SOME x. True)\<^sup>c"
definition BotC ("\<bottom>\<^sup>c") where "\<bottom>\<^sup>c \<equiv> \<not>\<^sup>c\<top>\<^sup>c"

\<comment>\<open>Kripke-style (here: valuation-based) semantics of the content logic\<close>
primrec RelTC :: "\<V>\<Rightarrow>\<w>\<Rightarrow>Formula\<Rightarrow>bool" ("_,_ \<Turnstile>\<^sup>c _") where
    "V,w \<Turnstile>\<^sup>c x\<^sup>c = V x w"
  | "V,w \<Turnstile>\<^sup>c \<not>\<^sup>c\<phi> = (\<not> V,w \<Turnstile>\<^sup>c \<phi>)"
  | "V,w \<Turnstile>\<^sup>c \<phi> \<supset>\<^sup>c \<psi> = (V,w \<Turnstile>\<^sup>c \<phi> \<longrightarrow> V,w \<Turnstile>\<^sup>c \<psi>)"

definition ValC ("\<Turnstile>\<^sup>c _") where "\<Turnstile>\<^sup>c \<phi> \<equiv> \<forall>V w. V,w \<Turnstile>\<^sup>c \<phi>"

subsection\<open>The Fatio language\<close>

datatype Sign = Pls ("\<oplus>") | Mns ("\<ominus>")
datatype FatioL =
    Assert    Speaker Formula          ("assert[_,_]")
  | Question  Speaker Speaker Formula  ("question[_,_,_]")
  | Challenge Speaker Speaker Formula  ("challenge[_,_,_]")
  | Justify   Speaker Formula Sign Formula ("justify[_,_\<turnstile>\<^sup>__]")
  | Retract   Speaker Formula Sign     ("retract[_,_,_]")

subsection\<open>BD logic (deeply embedded)\<close>

text\<open>The object language of the axiomatic semantics of Fatio
\<^cite>\<open>"McBurneyParsons2005"\<close>, as formalised in \<^cite>\<open>"PasettoBenzmueller2024"\<close>: agent beliefs \<open>\<B>\<^sup>d\<close> and
desires \<open>\<D>\<^sup>d\<close> over the content logic, with three further kinds of atoms: \<open>Done\<^sup>d\<close>
for uttered locutions, \<open>EntD\<close> for argumentative entailment, and \<open>ExJD i \<phi>\<close> whose
single semantic clause carries the existential of the pre-conditions of question
and challenge, \<open>(\<exists>\<Delta>) Done[justify(i,\<Delta>\<turnstile>\<^sup>s\<^sup>g\<phi>)]\<close>, inside the object language. Following
the sign-parametric justify locution of the LogiKEy sources \<^cite>\<open>"LogiKEy2020"\<close>, \<open>ExJD\<close> carries the
sign of the requested justification.\<close>

datatype BDF =
    AtmD \<S>            ("_\<^sup>a" [1000] 999)
  | DoneD FatioL       ("Done\<^sup>d")
  | EntD Formula Sign Formula
  | ExJD Speaker Sign Formula
  | NegD BDF           ("\<not>\<^sup>d_" [96] 96)
  | ImpD BDF BDF       (infixr "\<supset>\<^sup>d" 93)
  | BelD Speaker BDF   ("\<B>\<^sup>d")
  | DesD Speaker BDF   ("\<D>\<^sup>d")


\<comment>\<open>Homomorphic injection of content formulas into the BD language\<close>
primrec MapC :: "Formula\<Rightarrow>BDF" ("{_}\<^sup>d") where
  "{\<phi>\<^sup>c}\<^sup>d = \<phi>\<^sup>a" | "{\<not>\<^sup>c\<phi>}\<^sup>d = \<not>\<^sup>d{\<phi>}\<^sup>d" | "{\<phi> \<supset>\<^sup>c \<psi>}\<^sup>d = {\<phi>}\<^sup>d \<supset>\<^sup>d {\<psi>}\<^sup>d"

subsection\<open>Kripke semantics over models \<open>\<langle>W,B,D,V,U,E\<rangle>\<close>\<close>

type_synonym \<U> = "FatioL\<Rightarrow>\<w>\<Rightarrow>bool"              \<comment>\<open>Done-valuations\<close>
type_synonym \<E> = "Formula\<Rightarrow>Sign\<Rightarrow>Formula\<Rightarrow>\<w>\<Rightarrow>bool" \<comment>\<open>entailment-valuations\<close>

primrec RelTD :: "\<W>\<Rightarrow>\<R>\<Rightarrow>\<R>\<Rightarrow>\<V>\<Rightarrow>\<U>\<Rightarrow>\<E>\<Rightarrow>\<w>\<Rightarrow>BDF\<Rightarrow>bool" ("\<langle>_,_,_,_,_,_\<rangle>,_ \<Turnstile>\<^sup>d _") where
    "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d x\<^sup>a = V x w"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d Done\<^sup>d l = U l w"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d EntD \<Phi> sg \<phi> = E \<Phi> sg \<phi> w"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d ExJD i sg \<phi> = (\<exists>\<Delta>. U (Justify i \<Delta> sg \<phi>) w)"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<not>\<^sup>d\<phi> = (\<not> \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<psi> = (\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longrightarrow> \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<psi>)"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<B>\<^sup>d i \<phi> = (\<forall>v:W. B i w v \<longrightarrow> \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>d \<phi>)"
  | "\<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<D>\<^sup>d i \<phi> = (\<forall>v:W. D i w v \<longrightarrow> \<langle>W,B,D,V,U,E\<rangle>,v \<Turnstile>\<^sup>d \<phi>)"

definition ValD ("\<Turnstile>\<^sup>d _") where "\<Turnstile>\<^sup>d \<phi> \<equiv> \<forall>W B D V U E. \<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi>"

\<comment>\<open>Global consequence from a set of deep premises, over all models\<close>
definition ConsD :: "(BDF\<Rightarrow>bool)\<Rightarrow>BDF\<Rightarrow>bool" (infix "\<Turnstile>" 25) where
  "\<Gamma> \<Turnstile> \<phi> \<equiv> \<forall>W B D V U E. (\<forall>\<gamma>. \<Gamma> \<gamma> \<longrightarrow> (\<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<gamma>))
                            \<longrightarrow> (\<forall>w:W. \<langle>W,B,D,V,U,E\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"

named_theorems DefD
declare ValC_def[DefD] AndC_def[DefD,simp] OrC_def[DefD,simp] TopC_def[DefD,simp] BotC_def[DefD,simp]
  ValD_def[DefD] ConsD_def[DefD] ValC_def[DefD]

end
