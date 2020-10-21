theory ClimateEngineering
imports Argumentation embedding
begin
(* Configuration defaults *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)


section\<open>Introduction\<close>

(**Climate Engineering (CE), aka. Geo-engineering is the intentional large-scale intervention
in the Earth’s climate system in order to counter climate change.
Proposed CE technologies (e.g. solar radiation management, carbon dioxide removal, etc.)
are highly controversial, spurring global debates about whether
and under what conditions they should be considered.
Criticisms to CE range from diverting attention (and resources) from much needed mitigation policies
to potentially catastrophic side-effects; thus the cure may become worse than the disease.
The analysed arguments around the CE debate presented in this preliminary work originate from
the book of Betz and Cacean [cite], which is a slightly modified and updated translation of a study
commissioned by the German Federal Ministry of Education and Research (BMBF) on
"Ethical Aspects of Climate Engineering", which was finalised in spring 2011.
At the time, the work of Betz and Cacean indeed aimed at providing a quite complete overview of
the arguments around CE. However, the CE controversy has been advancing rapidly,
and it is thus expected that some of their results have become meanwhile outdated.
The illustrative analysis carried out in the present work focuses only on a small subset of
the CE argumentative landscape, namely on those arguments concerned with the "ethics of risk"
(cf. [cite] p. 38ff.) which point out (potentially dangerous) uncertainties in future deployment of CE.*)

(**
Our aim with this work is to further illustrate an approach previously presented at the CLAR-2018
conference [cite] which concerns the application of (higher-order) interactive theorem proving
to the logical analysis of arguments and their networks.
This approach had previously been introduced by analysing different kinds of ontological arguments
(i.e. arguments for the existence of a Godlike being).
On this ocassion we wanted to formalize and evaluate an extract from a quite contemporary
(and controversial) area of argumentative discourse. We argue that the utilization
of automated reasoning technology for very expressive (e.g. higher-order) logics in argumentation
can also be satisfactorily automated and is inded very useful to help in the reconstruction
of structured argument graphs (e.g. in the spirit of Besnard and Hunter's [cite] work) and also to
help discover implicit and idle premises in arguments.
The case study presented in the following sections has been carried out in the Isabelle/HOL
proof assistant [cite] for classical higher-order logic (HOL), aka. Church’s type theory [cite].
HOL is a logic of functions formulated on top of the simply typed lambda-calculus,
which also provides a foundation for functional programming.
*)

section\<open>Framework\<close>
(**In previous work on the logical analysis of argumentative discourse, we have presented an
interpretative approach named computational hermeneutics, amenable to partial mechanization
using three kinds of automated reasoning technology: (i) theorem provers, which tell us whether a
(formalized) claim logically follows from a set of assumptions; (ii) model finders,
which give us (counter-)examples for formulas in the context of a background set of premises;
and (iii) so-called "hammers", which automatically invoke (i) and (ii) as to find minimal
sets of relevant assumptions sufficient to derive a claim. We exemplified this approach using
implementations of (i-iii) for higher-order logic provided by the Isabelle/HOL proof assistant.*) 

(**In the computational hermeneutics process we work iteratively on an argument by choosing (tentatively)
a logic for formalization and then working back and forth on the formalization of its premises
and conclusion, while getting real-time feedback about the suitability of our choices.
In particular, following the interpretive "principle of charity" [cite], we aim at formalizations 
which render the argument as logically valid, while having a consistent and minimal set of assumptions.
These actions are to be repeated until arriving at a state of reflective equilibrium:
a state where our arguments and claims have the highest degree of coherence and acceptability
according to syntactic and, particularly, inferential criteria of adequacy (see [cite] p. XXff.).*)

(**Drawing upon the literature on structured argumentation graphs, in particular on
Besnard and Hunter's work [cite], we conceive an argument as a pair consisting of
(i) a set of formulas (its premises), from which (ii) another formula (the conclusion)
logically follows (according to a previously chosen logic for formalization).
Besnard and Hunter further introduce and interrelate different kinds of attack relations
(defeaters, undercuts, and rebuttals; cf. [cite]), which can be all subsumed, as we do, by
considering the attack relation between arguments A and B as the inconsistency of the set of formulas
consisting of the (formalized) conclusion of A, together with the premises of B. Put more formally:
*)

(**A (deductive) argument is an ordered pair (phi, alpha), where (phi --i alpha). Phi is the support,
or premises/assumptions of the argument, and alpha is the claim, or conclusion, of the argument.
Other constraints we set on arguments are: consistency: phi has to be logically consistent
(according to the chosen logic); and minimality: there is no psi < phi such that psi -- alpha.
For an argument A = (phi, alpha) the function Premises(A) returns phi and Conclusion(A) returns alpha.
Note that while every pair (phi, alpha) can be seen as a candidate argument during the process of
formal reconstruction, only those pairs which satisfy the given constraints are considered as
arguments proper.
*)

(**An argument A attacks (aka. is a defeater of) B iff the set Conclusion(A) U Premises(B)
is inconsistent. Notice that this definition subsumes the more traditional one for classical logic,
Conclusion(A) -- -x for some x e Premises(B), while allowing for paraconsistent formalization logics
where explosion (inconsistency) does not necessarily follow from pairs of contradictory formulas.
*)

(**
We also want to highlight the similarity in spirit between ours and Besnard and Hunter's [cite]
"descriptive approach" to reconstructing argument graphs (from natural-language sources);
where we have some (Dung-style [cite]) abstract argument graph as the input,
together with some informal description of each argument. Thus the task becomes to choose the appropriate
logical formulas for the premises and conclusion of each argument compatible with the choice of the
logic of formalization. As will become clear when analysing our case study in the next section,
there is a need for finding approapriate "implicit" premises which render the individual arguments
logically valid and additionally honor their intended dialectical role in the input abstract graph
(i.e. attacking or supporting other arguments). This interpretive aspect, in particular,
is emphasized in our computational hermeneutics approach (cf. [cite] p. XX ff.),
as well as the possibility of modifying the input abstract argument graph as new
insights, resulting from the formalization process, appear.*)

(**Quite interestingly too, in their exposition (see e.g. [cite] p. XX) Besnard and Hunter
duly highlight the fact that "richer" logic formalisms (i.e. more expressive than "rule-based" ones
like e.g. logic programming) are more appropriate for reconstructing "real-world arguments".
Such representational and interpretive issues are tackled in our approach by the use of non-classical
(and higher-order) logics for formalization. For this we utilize the shallow semantical embeddings
(SSE) approach to combining logics. SSE exploits HOL as a meta-logic in order to embed the syntax
and semantics of some target logics, thereby turning theorem proving systems for higher-order
logics into universal reasoning engines [cite]. 
*)

section\<open>Case Study\<close>

subsection\<open>Individual (Component) Arguments\<close>
(**As pinpointed in Betz and Cacean work [cite], incalculable side-effects and imponderables
constitute one of the main reasons against CE technology deployment. Arguments from the
ethics of risk primarily support the thesis: "CE deployment is morally wrong" (named T9 in [cite])
and make for an argument cluster with a non-trivial dialectical structure which we aim at
reconstructing in this section. We focus on five arguments from the ethics of risk,
which justify that deploying CE technologies (today as in the future) would be morally wrong
(A45, A46, A47, A48, A49, using the original notation in Betz and Cacean work [cite]).
In particular, two of these arguments, namely A47 and A49, are further supported and attacked.*)

subsubsection\<open>Main Thesis (T9)\<close>
(**The main thesis of this cluster of arguments is:
(T9) "The deployment of CE technologies is morally wrong".
This thesis can become formalized as follows.\footnote{Notice here that
we start by introducing a new, unconstrained propositional constant ("CEisWrong")
without initially specifying its meaning by means of definitions.
In general, term meanings (understood as their inferential roles) will gradually become determined
as we later add other, companion arguments to the current analysis.}
*)

consts CEisWrong::"w\<Rightarrow>bool" (*we still don't know what "CEisWrong" means"*)
definition T9::bool where   "T9 \<equiv> [\<Turnstile> CEisWrong]"

subsubsection\<open>Termination Problem (A45)\<close>
(**CE measures do not possess viable exit options. If deployment is terminated abruptly,
rapid and catastrophic climate change ensues (cf. Betz and Cacean's work [cite] for sources for these
--and other-- proposed theses/arguments in the CE debate ).*)

consts (*here we introduce constants*)
  A45_P1::bool A45_P2::bool A45_C::bool (**propositions (type bool)*)
  CEisTerminated::"w\<Rightarrow>bool"             (**propositions (type bool)*)
  CEisCatastrophic::"w\<Rightarrow>bool"
definition a45p1::bool where "a45p1 \<equiv> [\<Turnstile>\<^bold>\<diamond>CEisTerminated]"
definition a45p2::bool where "a45p2 \<equiv> [\<Turnstile> CEisTerminated \<^bold>\<rightarrow> CEisCatastrophic]"
definition a45c::bool where   "a45c \<equiv> [\<Turnstile> \<^bold>\<diamond>CEisCatastrophic]"

(** Instantiation of the abstract argument nodes: they are mapped to their formal counterparts. *) 
abbreviation  "Instantiate_A45 \<equiv> (A45_P1=a45p1) \<and> (A45_P2=a45p2) \<and> (A45_C=a45c) "

lemma assumes a45p1 and a45p2 and a45c shows True nitpick [satisfy] oops
theorem A45:
  assumes A45_P1 and A45_P2 and Instantiate_A45
  shows  "A45_C" using a45c_def a45p1_def a45p2_def assms(1) assms(2) assms(3) by auto


subsubsection\<open>No Long-term Risk Control (A45)\<close>
(**Our social systems and institutions are possibly not capable of controlling risk technologies
on long time scales and of ensuring that they are handled with proper technical care
(cf. Betz and Cacean [cite]).
*)

consts A46_P1::bool A46_P2::bool A46_P3::bool A46_C::bool
consts RiskControlAbility::"w\<Rightarrow>bool"
definition a46p1::bool where "a46p1 \<equiv> [\<Turnstile>\<^bold>\<diamond>\<^bold>\<sim>RiskControlAbility]"
definition a46p2::bool where "a46p2 \<equiv> [\<Turnstile> \<^bold>\<sim>RiskControlAbility \<^bold>\<rightarrow> \<^bold>\<diamond>CEisCatastrophic]"
definition a46c::bool where   "a46c \<equiv> [\<Turnstile> \<^bold>\<diamond>CEisCatastrophic]"

abbreviation  "Instantiate_A46 \<equiv> (A46_P1=a46p1) \<and> (A46_P2=a46p2) \<and> (A46_C=a46c) "

lemma assumes a46p1 a46p2 a46c shows True nitpick [satisfy] oops
lemma assumes A46_P1 A46_P2 Instantiate_A46 shows A46_C
  nitpick oops (** note that modal axiom 4 is needed here*)
lemma A46_C: assumes A46_P1 A46_P2 Instantiate_A46 K4 shows A46_C
  using a46c_def a46p1_def a46p2_def assms(1) assms(2) assms(3) assms(4) by blast


subsubsection\<open>CE Interventions are Irreversible (A47)\<close>
(**This thesis states that CE represents an irreversible intervention, i.e. once the first
interventions on world's climate have been in motion, there is no way to 'undo' them. 
For the following arguments we work with a predicate logic (incl. quantification).
We thus introduce a type ("e") for actions (interventions).*)

typedecl e (*new type*)
consts A47_C::bool
       IrreversibleAction::"e\<Rightarrow>w\<Rightarrow>bool"
       CEAction::"e\<Rightarrow>w\<Rightarrow>bool"
definition a47c::bool where "a47c \<equiv> [\<Turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> IrreversibleAction(I)]"
abbreviation  "Instantiate_A47 \<equiv> (A47_C=a47c)"

subsubsection\<open>No Ability to Retain Options after Irreversible Interventions (A48)\<close>
(**Irreversible interventions narrow the options of future generations in an unacceptable way,
i.e. it is wrong to carry out (any kind of) irreversible interventions on the climate.*)

consts A48_C::bool
       WrongAction::"e\<Rightarrow>w\<Rightarrow>bool"
definition a48c::bool where "a48c \<equiv> [\<Turnstile> \<^bold>\<forall>I. IrreversibleAction(I) \<^bold>\<rightarrow> WrongAction(I)]"
abbreviation  "Instantiate_A48 \<equiv> (A48_C=a48c) "

subsubsection\<open>Unpredictable Side-Effects are Wrong (A49)\<close>
(**As long as the side-effects of CE technologies cannot be reliably predicted,
their deployment is morally wrong.*)

consts A49_P1::bool A49_P2::bool A49_C::bool
       UnpredictableSideEffects::"e\<Rightarrow>w\<Rightarrow>bool"
definition a49p1::bool where "a49p1 \<equiv> [\<Turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> UnpredictableSideEffects(I)]"
definition a49p2::bool where "a49p2 \<equiv> [\<Turnstile>\<^bold>\<forall>I. UnpredictableSideEffects(I) \<^bold>\<rightarrow> WrongAction(I)]"
definition a49c::bool where "a49c \<equiv> [\<Turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)]"

abbreviation  "Instantiate_A49 \<equiv> (A49_P1=a49p1) \<and> (A49_P2=a49p2) \<and> (A49_C=a49c)"

lemma assumes A49_P1 A49_P2 Instantiate_A49 shows A49_C
  using a49c_def a49p1_def a49p2_def assms(1) assms(2) assms(3) by auto

subsubsection\<open>Mitigation is also Irreversible (A50)\<close>
(**Mitigation of climate change (i.e. the 'nice' alternative to CE), too, is, at least to some
extent, an irreversible intervention with unseen side-effects.*)

(**We add a constant corresponding to the action/intervention corresponding to mitigation.*)
consts Mitigation::e

consts A50_C::bool
definition a50c::bool where "a50c \<equiv> [\<Turnstile> IrreversibleAction(Mitigation) \<^bold>\<and> UnpredictableSideEffects(Mitigation)]"
abbreviation  "Instantiate_A50 \<equiv> (A50_C=a50c) "

subsubsection\<open>All Interventions have Unpredictable Side-Effects (A51)\<close>
(**This thesis says that we do never completely foresee the consequences of our actions and aims
at somehow trivializing the concerns regarding unforeseen side-effects of CE interventions.*)

consts A51_C::bool
definition a51c::bool where "a51c \<equiv> [\<Turnstile> \<^bold>\<forall>I. UnpredictableSideEffects(I)]"
abbreviation  "Instantiate_A51 \<equiv> (A51_C=a51c)"

subsection\<open>Reconstructing the Argument Network\<close>

subsubsection\<open>A45 supports T9\<close>
(** Does A45 indeed support the main thesis (T9)? *)
lemma assumes Instantiate_A45 shows "supports A45_C T9" 
  nitpick oops (**not as it stands: countermodel found*)

(**As seen below, a further implicit premise is needed (playing the role of a kind of "meaning postulate" [cite])*)
lemma assumes "[\<Turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  and Instantiate_A45
  shows "supports A45_C T9" 
  by (simp add: T9_def a45c_def assms(1) assms(2))

subsubsection\<open>A46 supports T9\<close>
(** Does A46 indeed support the main thesis (T9)? *)
lemma assumes Instantiate_A46 shows "supports A46_C T9"
  nitpick oops (**not as it stands: countermodel found*)

(**Indeed, the same implicit premise as before (for A45) is needed here. *)
lemma assumes "[\<Turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  and Instantiate_A46
  shows "supports A46_C T9" 
  by (simp add: T9_def a46c_def assms(1) assms(2))

subsubsection\<open>A47 and A48 (together) support T9\<close>
(** Do A47 and A48 indeed support the main thesis (T9)? *)
lemma assumes Instantiate_A47 and Instantiate_A48 shows "supports A47_C T9"
  nitpick oops (**not as they stand: countermodel found*)

(**Here, again, an implicit premise is needed. *)
lemma assumes "[\<Turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)] \<Longrightarrow> [\<Turnstile> CEisWrong] " (**implicit*)
  and Instantiate_A47 and Instantiate_A48 
  shows "supports1 A47_C A48_C T9" 
  by (simp add: T9_def a47c_def a48c_def assms(1) assms(2) assms(3))

subsubsection\<open>A49 supports T9\<close>
(**Does A49 indeed support the main thesis (T9)? *)
lemma assumes Instantiate_A49 shows "supports A49_C T9"
  nitpick oops (**not as it stands: countermodel found*)

(**An implicit premise is also needed below.*)
lemma assumes "[\<Turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)] \<Longrightarrow> [\<Turnstile> CEisWrong]" (**implicit*) 
  and Instantiate_A49
shows "supports A49_C T9" by (simp add: T9_def a49c_def assms(1) assms(2))

subsubsection\<open>A50 attacks A47 and A49\<close>
(** Does A50 attack arguments A47 and A49? *)

lemma assumes Instantiate_A50 shows "attacks A50_C A47_C"
  nitpick oops (**not as it stands: countermodel found*)
lemma assumes Instantiate_A50 shows "attacks A50_C A49_C"
  nitpick oops (**not as it stands: countermodel found*)

(**In the following, we reconstruct the arguments corresponding to the attack relations,
noting that here too are two additional, implicit premises needed. *)
lemma assumes "[\<Turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<Turnstile> \<^bold>\<exists>I. \<^bold>\<sim>WrongAction(I)]" (**second implicit premise*)
  and Instantiate_A50 and Instantiate_A47 and Instantiate_A48
  shows "attacks1 A48_C A50_C A47_C"
  using a47c_def a48c_def a50c_def assms(1) assms(2) assms(3) assms(4) assms(5) by fastforce

lemma assumes "[\<Turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<Turnstile> \<^bold>\<exists>I. \<^bold>\<sim>WrongAction(I)]" (**second implicit premise*)
  and Instantiate_A50 and Instantiate_A49
  shows "attacks1 A50_C A49_P1 A49_P2"
  using a49p1_def a49p2_def a50c_def assms(1) assms(2) assms(3) assms(4) by fastforce

subsubsection\<open>A51 attacks A49\<close>
(** Does A51 attack argument A49? *)
lemma assumes Instantiate_A51 shows "attacks1 A51_C A49_P1 A49_P2"
  nitpick oops (**not as it stands: countermodel found*)

lemma assumes"[\<Turnstile> \<^bold>\<exists>I. \<^bold>\<sim>WrongAction(I)]" (**implicit premise *)
  and Instantiate_A51 and Instantiate_A49
  shows "attacks A51_C A49_P2"
  by (simp add: a49p2_def a51c_def assms(1) assms(2) assms(3))

(*TODO:
- Expand analysis to the A52 sub-network
- Show how to parameterize Support/Attack relations with axioms of the object logic
*)


end