(*<*)
theory ClimateEngineering
imports embedding
begin
(* Configuration defaults *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)
(*>*)

section\<open>Introduction\<close>

(**Climate Engineering (CE), aka. Geo-engineering, is the intentional large-scale intervention
in the Earth's climate system in order to counter climate change.
Proposed CE technologies (e.g., solar radiation management, carbon dioxide removal, etc.)
are highly controversial, spurring global debates about whether
and under what conditions they should be considered.
Criticisms to CE range from diverting attention (and resources) from much needed mitigation policies
to potentially catastrophic side-effects; thus the cure may become worse than the disease.
The analysed arguments around the CE debate presented in this preliminary work originate from
the book by Betz and Cacean \cite{CE}, which is a slightly modified and updated translation of a study
commissioned by the German Federal Ministry of Education and Research (BMBF) on
``Ethical Aspects of Climate Engineering", which was finalised in spring 2011.
At the time, the work of Betz and Cacean aimed at providing a quite complete overview of
the arguments around CE. However, the CE controversy has been advancing rapidly,
and it is thus expected that some of their results have become meanwhile outdated.
The illustrative analysis carried out in the present work focuses only on a small subset of
the CE argumentative landscape, namely on those arguments concerned with the ``ethics of risk"
(cf. \cite{CE} p. 38ff.) which point out (potentially dangerous) uncertainties in future deployment of CE.*)

(**Our objective in this paper is to further illustrate and explore an approach previously presented at the CLAR-2018
conference \cite{CH} which concerns the application of (higher-order) interactive theorem proving
to the logical analysis of individual arguments and argument networks.
This approach had previously been introduced by analysing different kinds of ontological arguments
(i.e., arguments for the existence of a Godlike being, common in philosophy and theology).
Here we are formalising and evaluating an extract from a quite contemporary
(and controversial) area of argumentative discourse. We argue that the utilisation
of automated reasoning technology for very expressive (e.g., higher-order) logics in argumentation
can also be satisfactorily automated and is indeed very useful to help in the reconstruction
of structured argument graphs (e.g., in the spirit of Besnard and Hunter's work \cite{BH,BH-2008}) and also to
help discover implicit and idle premises in arguments.
The case study presented in the last section has been carried out in the
\emph{Isabelle/HOL}\footnote{Sources for this case study have been made available online (see \cite{Sources}).}
proof assistant \cite{Isabelle} for classical higher-order logic (HOL), aka. Church's type theory.
HOL is a logic of functions formulated on top of the simply typed lambda-calculus,
which also provides a foundation for functional programming \cite{SEP-TT}.*)

section\<open>Framework\<close>
(**In previous work on the logical analysis of argumentative discourse, we have presented an
interpretive approach named computational hermeneutics, amenable to partial mechanisation
using three kinds of automated reasoning technology: (i) theorem provers, which tell us whether a
(formalized) claim logically follows from a set of assumptions; (ii) model finders,
which give us (counter-)examples for formulas in the context of a background set of premises;
and (iii) so-called ``hammers", which automatically invoke (i) and (ii) as to find minimal
sets of relevant assumptions sufficient to derive a claim. We exemplified this approach using
implementations of (i-iii) for higher-order logic provided by the \emph{Isabelle/HOL} proof assistant.
In this approach, named computational hermeneutics, we work iteratively on an argument by choosing (tentatively)
a logic for formalization and then working back and forth on the formalization of its premises
and conclusion, while getting real-time feedback about the suitability of our choices (including the 
chosen logic) from a proof assistant.
In particular, following the interpretive ``principle of charity" \cite{Davidson}, we aim at formalisations 
which render the argument as logically valid, while having a consistent and minimal set of assumptions.
These actions are to be repeated until arriving at a state of \emph{reflective equilibrium}:
a state where our arguments and claims have the highest degree of coherence and acceptability
according to syntactic and, particularly, inferential criteria of adequacy (see \cite{CH,CH2}).*)

(**Drawing upon the literature on structured argumentation graphs, in particular on
Besnard and Hunter's work \cite{BH}, we conceive an argument as a pair consisting of
(i) a set of formulas (premises), from which (ii) another formula (conclusion)
logically follows according to a previously chosen logic for formalization.
Besnard and Hunter further introduce and interrelate different kinds of \emph{attack} relations between
arguments (defeaters, undercuts, and rebuttals; cf. \cite{BH}) which can be all subsumed, as we do, by
considering an attack between \emph{A} and \emph{B} as the inconsistency of the set of formulas
formed by the conclusion of \emph{A} together with the premises of \emph{B}.
Drawing on the work of Cayrol and Lagasquie-Schiex \cite{BAF},
we also consider \emph{support} relations between arguments. More formally:
\small
\begin{definition}
A (deductive) argument is an ordered pair @{text "\<langle>\<phi>, \<alpha>\<rangle>"}, where @{text "\<phi> \<turnstile>\<^sub>L \<alpha>"} for some given
logic \emph{L}. @{text "\<phi>"} is the support, or premises/assumptions of the argument,
and @{text "\<alpha>"} is the claim, or conclusion, of the argument.
Other constraints we set on arguments are consistency: @{text "\<phi>"} has to be logically consistent
(according to the chosen logic \emph{L}); and minimality: there is no @{text "\<psi> \<subset> \<phi>"} such that @{text "\<psi> \<turnstile>\<^sub>L \<alpha>"}.
For an argument @{text "A = \<langle>\<phi>, \<alpha>\<rangle>"} the function \emph{Premises(A)} returns @{text "\<phi>"} and
\emph{Conclusion(A)} returns @{text "\<alpha>"}.
Note that while every pair @{text "\<langle>\<phi>, \<alpha>\<rangle>"} can be seen as a candidate argument during the process of
formal reconstruction, only those pairs which satisfy the given constraints are considered as
arguments proper.
\end{definition}
\begin{definition}
An argument \emph{A} attacks (aka.~is a defeater of) \emph{B} iff the set @{text "Conclusion(A) \<union> Premises(B)"}
is inconsistent. Notice that this definition subsumes the more traditional one for classical logic,
@{text "Conclusion(A) \<turnstile> \<not>X"} for some @{text "X \<in> Premises(B)"}, while allowing for paraconsistent
formalization logics
where explosion (inconsistency) does not necessarily follow from pairs of contradictory formulas.
\end{definition}
\begin{definition}
An argument \emph{A} supports \emph{B} iff @{text "Conclusion(A) \<turnstile> X"}
for some @{text "X \<in> Premises(B)"}. This definition can be seamlessly extended to two (or more) arguments:
@{text "A\<^sub>1"} and @{text "A\<^sub>2"} support @{text "B"} iff @{text "Conclusion(A\<^sub>1) \<union> Conclusion(A\<^sub>2) \<turnstile> X"}
for some @{text "X \<in> Premises(B)"}.
\end{definition}
\normalsize
We also want to highlight the similarity in spirit between ours and Besnard and Hunter's \cite{BH}
``descriptive approach" to reconstructing argument graphs (from natural-language sources);
where we have some (Dung-style \cite{Dung}) abstract argument graph as the input,
together with some informal text description of each argument. Thus, the task becomes to choose the appropriate
logical formulas for the premises and conclusion of each argument compatible with the choice of the
logic of formalization. As will become clear when analysing our case study in the next section,
there is a need for finding appropriate ``implicit" premises which render the individual arguments
logically valid and additionally honor their intended dialectical role in the input abstract graph
(i.e., attacking or supporting other arguments). This interpretive aspect, in particular,
has been emphasized in our computational hermeneutics approach \cite{CH,CH2},
as well as the possibility of modifying the input abstract argument graph as new
insights, resulting from the formalization process, appear.
In their exposition of structured argumentation (see, e.g., \cite{BH}) Besnard and Hunter
duly highlight the fact that ``richer" logic formalisms (i.e., more expressive than ``rule-based" ones
like, e.g., logic programming) are more appropriate for reconstructing ``real-world arguments".
Such representational and interpretive issues are tackled in our approach by the use of different 
(combinations of) non-classical and higher-order logics for formalisation.
For this we utilise the shallow semantical embeddings
(SSE) approach to combining logics \cite{J23}. SSE exploits HOL as a meta-logic in order to embed the syntax
and semantics of diverse object logics (modal, temporal, deontic, paraconsistent, etc.),
thereby turning theorem proving systems for higher-order
logics into universal reasoning engines \cite{J41}. \emph{Isabelle/HOL} sources for this paper
have been made available online (see \cite{Sources}). We encourage the interested reader to try out (and improve on)
this work.*)

section\<open>Case Study\<close>

subsection\<open>Individual (Component) Arguments\<close>
(**As has been observed by Betz and Cacean \cite{CE}, incalculable side-effects and imponderables
constitute one of the main reasons against CE technology deployment. Thus, arguments from the
\emph{ethics of risk} primarily support the thesis: ``CE deployment is morally wrong" (also named T9 in \cite{CE})
and make for an argument cluster with a non-trivial dialectical structure which we aim at
reconstructing in this section. We focus on six arguments from the ethics of risk,
which entail that the deployment of CE technologies (today as in the future) is not desirable
because of being morally wrong (argument A22). Supporting arguments of A22 are: A45, A46, A47, A48, A49
(using the original notation in Betz and Cacean work \cite{CE}).
In particular, two of these arguments, namely A47 and A49, are further attacked by A50 and A51.
\begin{figure}[tp] \normalsize \centering
	\fbox{
		\begin{tikzcd}[row sep=1em,column sep=1em]
			{}  \& A50 \arrow{d}{@} \arrow{dr}{@} \& {} \& A51 \arrow{dl}{@} \& {} \\[1em]
			A48 \arrow{dr} \& A47 \arrow{d} \& A49 \arrow{dd} \& A45 \arrow{ddl} \& A46 \arrow{ddll} \\[1em]
			{} \& * \arrow{dr} \& {} \& {} \& {} \\[1em]
			{} \& {}\& A22 \& {} \& {}
		\end{tikzcd}
	}
	\caption{Abstract argumentation network for the ethics of risk cluster in the CE debate
  (arrows labeled with @ indicate \emph{attacks}); the * indicates a joint \emph{support}.}
	\label{figArgNetwork}
\end{figure}*)

subsubsection\<open>Ethics of Risk Argument (A22)\<close>
(**The argument has as premise T9: ``CE deployment is morally wrong" and as conclusion:
``CE deployment is not desirable". Notice that both are formalised as (modally) valid propositions,
i.e. true in all possible worlds or situations. We are thus presupossing a possible-worlds semantics
for our logic of formalisation while restricting ourselves, for the time being,
to a propositional logic (to keep it simple).
Also notice that we introduce two new, uninterpreted propositional constants
(``CEisWrong" and ``CEisNotDesirable") and interrelate them by means of an implicit premise (A22-P2),
but without further constraining their meaning at this stage of the modeling process.
In general, term meanings (understood as their inferential roles) will gradually become determined
as we add other companion arguments to the analysis.*)

consts CEisWrong::"w\<Rightarrow>bool"  (**notice type for world-contingent propositions*)
       CEisNotDesirable::"w\<Rightarrow>bool"
definition A22_P1::bool where "A22_P1 \<equiv> [\<turnstile> CEisWrong]" (*(T9) CE is wrong in all situations*)
definition A22_P2::bool where "A22_P2 \<equiv> [\<turnstile> CEisWrong \<^bold>\<rightarrow> CEisNotDesirable]" (*implicit!*)
definition A22_C::bool where "A22_C \<equiv> [\<turnstile> CEisNotDesirable]" (*...also in all situations*)

(**We use the model finder \emph{Nitpick} \cite{Nitpick} to find a model satisfying the premises and
the conclusion of the formalised argument (recall definitions in section 2).*)
lemma assumes A22_P1 and A22_P2 and A22_C shows True 
  nitpick [satisfy] oops (**consistency is shown: nitpick presents a simple model*)

(**This first argument (A22) serves as a quite straightforward illustration of the role of implicit,
unstated premises in enabling the reconstruction of a candidate argument as a (valid) argument proper.
We utilise the tableaux-based prover \emph{blast} to verify that the conclusion follows
from the premises (which form indeed a minimal set, since each of them is used by the prover).*)
theorem A22_valid: assumes A22_P1 and A22_P2 shows A22_C
  using A22_C_def A22_P2_def A22_P1_def assms(1) assms(2) by blast

subsubsection\<open>Termination Problem (A45)\<close>
(**CE measures do not possess viable exit options. If deployment is terminated abruptly,
catastrophic climate change ensues.\footnote{cf. Betz and Cacean's work \cite{CE} for sources for these
--and other-- proposed theses and arguments in the CE debate.}
*)
consts CEisTerminated::"w\<Rightarrow>bool"   (**world-contingent propositional constants*)
       CEisCatastrophic::"w\<Rightarrow>bool"
definition A45_P1::bool where "A45_P1 \<equiv> [\<turnstile> \<^bold>\<diamond>CEisTerminated]"
definition A45_P2::bool where "A45_P2 \<equiv> [\<turnstile> CEisTerminated \<^bold>\<rightarrow> CEisCatastrophic]"
definition A45_C::bool  where  "A45_C \<equiv> [\<turnstile> \<^bold>\<diamond>CEisCatastrophic]"

(**Notice that we have introduced in the above formalisation the @{text "\<diamond>"}
modal operator to signify that a proposition is possibly true (e.g. at a future point in time).*)
theorem A45_valid: assumes A45_P1 and A45_P2 shows "A45_C"
  using A45_C_def A45_P1_def A45_P2_def assms(1) assms(2) by blast

subsubsection\<open>No Long-term Risk Control (A46)\<close>
(**Our social systems and institutions are possibly not capable of controlling risk technologies
on long time scales and of ensuring that they are handled with proper technical care \cite{CE}.
Notice that we can make best sense of this objection as (implicitly?) presupossing a risk of 
CE-caused catastrophes.*)

consts RiskControlAbility::"w\<Rightarrow>bool"
definition A46_P1::bool where "A46_P1 \<equiv> [\<turnstile> \<^bold>\<diamond>\<^bold>\<not>RiskControlAbility]"
definition A46_P2::bool where "A46_P2 \<equiv> [\<turnstile> \<^bold>\<not>RiskControlAbility \<^bold>\<rightarrow> \<^bold>\<diamond>CEisCatastrophic]"
definition A46_C::bool where   "A46_C \<equiv> [\<turnstile> \<^bold>\<diamond>CEisCatastrophic]"

(**We can use our automated tools as before to find out further implicit premises that indeed correspond to
modifications to the logic of formalization. The argument A46 needs a modal logic ``K4" to succeed.
The implicit premise thus becomes:  @{text "Ax4: [\<turnstile> \<forall>\<phi>. \<box>\<phi> \<rightarrow> \<box>\<box>\<phi>]"} (corresponding to transitivity of the
accessibility relation).*)
lemma assumes A46_P1 and A46_P2 shows A46_C
  nitpick oops (**counterexample found, since modal axiom 4 is needed here*)
theorem A46_valid: assumes A46_P1 and A46_P2 and Ax4 shows A46_C
  using A46_C_def A46_P1_def A46_P2_def assms(1) assms(2) assms(3) by blast

subsubsection\<open>CE Interventions are Irreversible (A47)\<close>
(**As presented in \cite{CE}, this argument consists of a simple sentence (its conclusion), which
states that CE represents an irreversible intervention, i.e., that once the first
interventions on world's climate have been set in motion, there is no way to ``undo" them. 
For the following arguments we work with a predicate logic (incl. quantification), and
thus introduce a type (``e") for actions (interventions).*)

typedecl e (**introduces a new type for actions*)
consts CEAction::"e\<Rightarrow>w\<Rightarrow>bool" (**notice type for (world-dependent) predicates*)
       Irreversible::"e\<Rightarrow>w\<Rightarrow>bool" 
definition A47_C::bool where "A47_C \<equiv> [\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> Irreversible(I)]"

subsubsection\<open>No Ability to Retain Options after Irreversible Interventions (A48)\<close>
(**Irreversible interventions (of any kind) narrow the options of future generations in an unacceptable way,
i.e., it is wrong to carry them out \cite{CE}.*)

consts WrongAction::"e\<Rightarrow>w\<Rightarrow>bool"
definition A48_C::bool where "A48_C \<equiv> [\<turnstile> \<^bold>\<forall>I. Irreversible(I) \<^bold>\<rightarrow> WrongAction(I)]"

subsubsection\<open>Unpredictable Side-Effects are Wrong (A49)\<close>
(**As long as side-effects of CE technologies cannot be reliably predicted,
their deployment is morally wrong \cite{CE}.*)

consts USideEffects::"e\<Rightarrow>w\<Rightarrow>bool"
definition A49_P1::bool where "A49_P1 \<equiv> [\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> USideEffects(I)]"
definition A49_P2::bool where "A49_P2 \<equiv> [\<turnstile>\<^bold>\<forall>I. USideEffects(I) \<^bold>\<rightarrow> WrongAction(I)]"
definition A49_C ::bool where "A49_C  \<equiv> [\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)]"

theorem A49_valid: assumes A49_P1 and A49_P2 shows A49_C (*blast verifies validity*)
  using A49_C_def A49_P1_def A49_P2_def assms(1) assms(2) by blast

subsubsection\<open>Mitigation is also Irreversible (A50)\<close>
(**Mitigation of climate change (i.e., the ``prevention" alternative to CE), too, is, at least to some
extent, an irreversible intervention with unforeseen side-effects \cite{CE}.*)

consts Mitigation::e (**constant of same type as actions/interventions*)
definition A50_C::bool where 
  "A50_C \<equiv> [\<turnstile> Irreversible(Mitigation) \<^bold>\<and> USideEffects(Mitigation)]"

subsubsection\<open>All Interventions have Unpredictable Side-Effects (A51)\<close>
(**This defense of CE states that we do never completely foresee the consequences of our actions anyways,
and thus aims at somehow trivializing the concerns regarding unforeseen side-effects of CE.*)

definition A51_C where "A51_C \<equiv> [\<turnstile> \<^bold>\<forall>I. USideEffects(I)]"

subsection\<open>Reconstructing the Argument Graph\<close>
(**The claim that an argument (or a set of arguments) attacks resp. supports another argument is, in our
approach, conceived as an argument in itself, which also needs to be reconstructed as logically valid
by (possibly) adding implicit premises.
Below we introduce our generalized \emph{attack} resp. \emph{support} relations between arguments
along the lines of structured and bipolar argumentation (cf. \cite{BH} \cite{BAF} resp.).*)

abbreviation attacks1 where  "attacks1 \<phi> \<psi>  \<equiv> (\<phi> \<and> \<psi>) \<longrightarrow> False" (**one attacker*)
abbreviation supports1 where "supports1 \<phi> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>" (**only one supporter*)
abbreviation attacks2 where  "attacks2 \<gamma> \<phi> \<psi>  \<equiv> (\<gamma> \<and> \<phi> \<and> \<psi>) \<longrightarrow> False" (*two attackers *)
abbreviation supports2 where "supports2 \<gamma> \<phi> \<psi> \<equiv> (\<gamma> \<and> \<phi>) \<longrightarrow> \<psi>" (**two supporters*)

subsubsection\<open>Does A45 support A22?\<close>
(**In this example (as in others) we have utilised three kinds of automated tools integrated
into \emph{Isabelle/HOL}: the model finder \emph{Nitpick} \cite{Nitpick}, which finds a
counterexample to the claim that e.g. A45 supports A22 (without further implicit premises);
the tableaux-based prover \emph{blast},\footnote{This is a prover among several others integrated
into \emph{Isabelle/HOL} \cite{Isabelle}.}
which can indeed verify that by adding a given implicit
premise the \emph{support} relation obtains; and the ``hammer" tool \emph{Sledgehammer} \cite{Sledgehammer}
which automagically finds minimal sets of assumptions needed to prove the theorem.*)
lemma "supports1 A45_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  shows "supports1 A45_C A22_P1" using A22_P1_def A45_C_def assms(1) by blast

subsubsection\<open>Does A46 support A22?\<close>
(**The same implicit premise as before is needed.*)
lemma "supports1 A46_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  shows "supports1 A46_C A22_P1" using A22_P1_def A46_C_def assms(1) by blast

subsubsection\<open>Do A47 and A48 (together) support A22?\<close>
(**Implicit premise again needed.*)
lemma "supports2 A47_C A48_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)]\<longrightarrow>[\<turnstile> CEisWrong]" (*implicit*)
  shows "supports2 A47_C A48_C A22_P1"
  using A22_P1_def A47_C_def A48_C_def assms(1) by blast (**assms(1) implicit*)

subsubsection\<open>Does A49 support A22?\<close>
(**An implicit premise is also needed.*)
lemma "supports1 A49_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)] \<longrightarrow> [\<turnstile> CEisWrong]"
  shows "supports1 A49_C A22_P1" using A22_P1_def A49_C_def assms(1) by blast

subsubsection\<open>Does A50 attack both A47 and A49?\<close>
(**We reconstruct the arguments corresponding to the \emph{attack} relations,
noting that here, too, are two additional implicit premises needed.*)

lemma "attacks1 A50_C A47_C" nitpick oops (** countermodel found*)
lemma "attacks1 A50_C A49_C" nitpick oops (** countermodel found*)

theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**second implicit premise*)
  shows "attacks2 A48_C A50_C A47_C"
  using A47_C_def A48_C_def A50_C_def assms(1) assms(2) by fastforce
theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**second implicit premise*)
  shows "attacks2 A50_C A49_P1 A49_P2"
  using A49_P1_def A49_P2_def A50_C_def assms(1) assms(2) by fastforce

subsubsection\<open>Does A51 attack A49?\<close>
(**The same implicit premise as before is needed.*)
lemma "attacks2 A51_C A49_P1 A49_P2" nitpick oops (** countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**implicit premise *)
  shows "attacks1 A51_C A49_P2" using A49_P2_def A51_C_def assms(1) by blast

section\<open>Further Work and Conclusions\<close>
(**We are currently working on extending the current analysis to other argument clusters in the CE discourse
(as presented by Betz and Cacean \cite{CE} and drawing on more recent sources too).
An analysis at the abstract level, e.g.~by using Dung's dialectic semantics, is also in sight 
(possibly extended with \emph{support} relations, cf. bipolar abstract argumentation \cite{BAF}).
The expressivity of higher-order logic (HOL) indeed
allows us to encode Dung's definitions for complete, grounded, preferred and stable semantics
in \emph{Isabelle/HOL} and to use automated tools for HOL to carry out computations. This can be
very useful for prototyping tasks and as well for reasoning with arguments at the abstract and
structural level in an integrated fashion. However, further work is needed to obtain a satisfactorily
usable and performant implementation.
We are further working on utilising shallow semantic embeddings (SSE) of non-classical
logics (modal, deontic, paraconsistent, etc.) into HOL in order to foster a logico-pluralist approach to the
reconstruction of structured argument graphs (e.g. by employing \emph{attack} resp.
\emph{support} relations parameterised with different base logics).*)

(*<*)
end
(*>*)