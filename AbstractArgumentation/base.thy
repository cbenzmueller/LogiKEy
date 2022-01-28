(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains domain-specific basic definitions on arguments, extensions, labellings, etc. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
             logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory base
  imports Main misc
begin

(* A named collection of definitions related to AFs; it can later be referred to by its name 'Defs'. *)
named_theorems Defs

(* An abstract argumentation framework AF is characterized by its 
   set of arguments \<A> of type 'a Set (the arguments being of arbitrary type 'a)
   and the attack relation (usually referred to as 'att' or ... ) of type 'a Rel.
   The is usually bundled within a pair (\<A>, att) in literature. For simplicity
   (and technical reasons) we pass to each concept \<A> and att individually,
   instead of the pair AF = (\<A>, att). Any 2-ary function can be regarded
   a nested unary function in terms of Currying. *)

(***********************************************************)
(***********************************************************)
(* Notions primarily related to extension based semantics. *)
(***********************************************************)
(***********************************************************)

(* Given a set of arguments S, we define its set of attacked (+) and attacking (-) arguments ([BCG 2011] p. 3). *)
definition plusset :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>+") 
  where \<open>[att|S]\<^sup>+ \<equiv> \<lambda>b. \<exists>a. S a \<and> att a b\<close>
definition minusset:: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>-") 
  where \<open>[att|S]\<^sup>- \<equiv> \<lambda>b. \<exists>a. S a \<and> att b a\<close>

(* Below we define relativized variants, which require an universe set of arguments \<A> as additional parameter: *)
definition plusset_rel :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_|_]\<^sup>+") 
  where \<open>[\<A>|att|S]\<^sup>+ \<equiv> \<lambda>b. (\<exists>a. \<A> a \<and> S a \<and> att a b)\<close>
definition minusset_rel:: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_|_]\<^sup>-") 
  where \<open>[\<A>|att|S]\<^sup>- \<equiv> \<lambda>b. (\<exists>a. \<A> a \<and> S a \<and> att b a)\<close>

(* A set S of arguments defends an argument 'a' iff each argument 'b' attacking 'a' is itself attacked by
   at least one argument in S ([Dung 1995] Def. 6(1) and  [BCG 2011] Def. 11). *)
definition defends :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a \<Rightarrow> bool\<close> 
  where \<open>defends \<equiv> \<lambda>att S a. \<forall>b. att b a \<longrightarrow> (\<exists>z. S z \<and> att z b)\<close>

definition defends_rel :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a \<Rightarrow> bool\<close> ("defends\<^sup>_")
  where \<open>defends\<^sup>\<A> \<equiv> \<lambda>att S a. \<forall>b. \<A> b \<longrightarrow> att b a \<longrightarrow> (\<exists>z. \<A> z \<and> S z \<and> att z b)\<close>

lemma defends_defEq: \<open>defends att S a = [att|\<lbrace>a\<rbrace>]\<^sup>- \<subseteq> [att|S]\<^sup>+\<close>
  by (simp add: defends_def minusset_def plusset_def)

lemma defends_rel_defEq: \<open>\<A> a \<Longrightarrow> (defends\<^sup>\<A> att S a) = [\<A>|att|\<lbrace>a\<rbrace>]\<^sup>- \<subseteq>\<^sup>\<A> [\<A>|att|S]\<^sup>+\<close>
  by (simp add: defends_rel_def minusset_rel_def plusset_rel_def)

(* The characteristic function, denoted by \<F>, of an argumentation framework AF = (\<A>, att) is
   defined as \<F>(S) = {A | A is defended by S} ([BCG 2011] Def. 11). In fact, this corresponds to 'defends'.*)
abbreviation charFun  :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("\<F>") 
  where \<open>\<F> \<equiv> defends\<close>
abbreviation charFun_rel :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("\<F>\<^sup>_") 
  where \<open>\<F>\<^sup>\<A> \<equiv> defends\<^sup>\<A>\<close>

(* \<F> is monotone (i.e. order preserving wrt. set inclusion). *)
lemma \<F>_mono': "MONO (\<F>\<^sup>\<A> att)" unfolding MONO_def by (smt (verit, ccfv_SIG) defends_rel_def)
lemma \<F>_mono: "MONO\<^sup>\<A> (\<F>\<^sup>\<A> att)" unfolding MONO_rel_def defends_rel_def by blast

(* We can in fact verify that \<F> has both a least and a greatest fixed point. *)
lemma \<F>_leastFP_ex': \<open>\<exists>S. least (fixpoint (\<F>\<^sup>\<A> att)) S id\<close> using \<F>_mono' wKTl' by auto
lemma \<F>_leastFP_ex:  \<open>\<exists>S. least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id\<close> by (simp add: \<F>_mono wKTl_relw)
lemma \<F>_greatestFP_ex': \<open>\<exists>S. greatest (fixpoint (\<F>\<^sup>\<A> att)) S id\<close> using \<F>_mono' wKTg' by auto
lemma \<F>_greatestFP_ex:  \<open>\<exists>S. greatest\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id\<close> by (simp add: \<F>_mono wKTg_relw)

(* Recalling that least/greatest elements are unique we can indeed define:
   "the least/greatest fixed point of \<F>".*)
definition \<open>tlfp att \<equiv> THE S. least (fixpoint (\<F> att)) S id\<close>
definition \<open>tgfp att \<equiv> THE S. greatest (fixpoint (\<F> att)) S id\<close>

(* least/greatest fixed point of \<F> wrt. universe \<A>*)
definition lfpR ("lfp\<^sup>_") where \<open>lfp\<^sup>\<A> \<equiv> \<lambda>att S. least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id\<close>
definition gfpR ("gfp\<^sup>_") where \<open>gfp\<^sup>\<A> \<equiv> \<lambda>att S. greatest\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id\<close>

(***********************************************************)
(***********************************************************)
(* Notions primarily related to Labelling based semantics. *)
(***********************************************************)
(***********************************************************)

(* Generalising sets as "labellings", i.e. functions into some finite codomain (of "labels") *)
datatype Label = In | Out | Undec (*introduces a 3-element set of labels*)
type_synonym 'a Labelling = \<open>'a \<Rightarrow> Label\<close> (*labellings as functions into "labels" *)

(* (cf. [BCG 2011] p. 4) *)
definition inset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("in") where \<open>in(Lab) \<equiv> \<lambda>x. Lab(x) = In\<close>
definition outset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("out") where \<open>out(Lab) \<equiv> \<lambda>x. Lab(x) = Out\<close>
definition undecset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("undec") where \<open>undec(Lab) \<equiv> \<lambda>x. Lab(x) = Undec\<close>

definition equivalentLab :: \<open>'a Labelling \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> (infix "\<cong>" 52) 
  where "L1 \<cong> L2 \<equiv> (in(L1) \<approx> in(L2)) \<and> (out(L1) \<approx> out(L2))"

lemma InUndecEquivLab: "(in(L1) \<approx> in(L2)) \<and> (undec(L1) \<approx> undec(L2)) \<longrightarrow> L1 \<cong> L2"
  by (smt (verit, ccfv_SIG) Label.exhaust equivalentLab_def inset_def outset_def undecset_def)
lemma OutUndecEquivLab: "(out(L1) \<approx> out(L2)) \<and> (undec(L1) \<approx> undec(L2)) \<longrightarrow> L1 \<cong> L2"
  by (smt (verit, ccfv_SIG) Label.exhaust equivalentLab_def inset_def outset_def undecset_def)

lemma equivLabId: "L1 \<cong> L2 \<longleftrightarrow> L1 = L2" using Label.exhaust ext by (metis (full_types) equivalentLab_def inset_def outset_def)

(* Analogously we provide a relativized definition too (wrt. an universe set of arguments \<A>)*)
definition equivalentLab_rel :: \<open>'a Labelling \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> ("_\<cong>\<^sup>__") 
  where "L1 \<cong>\<^sup>\<A> L2 \<equiv> (in(L1) \<approx>\<^sup>\<A> in(L2)) \<and> (out(L1) \<approx>\<^sup>\<A> out(L2))"

lemma InUndecEquivLab_rel: "(in(L1) \<approx>\<^sup>\<A> in(L2)) \<and> (undec(L1) \<approx>\<^sup>\<A> undec(L2)) \<longrightarrow> L1 \<cong>\<^sup>\<A> L2"
  by (smt (verit, ccfv_SIG) Label.exhaust equivalentLab_rel_def inset_def outset_def undecset_def)
lemma OutUndecEquivLab_rel: "(out(L1) \<approx>\<^sup>\<A> out(L2)) \<and> (undec(L1) \<approx>\<^sup>\<A> undec(L2)) \<longrightarrow> L1 \<cong>\<^sup>\<A> L2"
  by (smt (verit, ccfv_SIG) Label.exhaust equivalentLab_rel_def inset_def outset_def undecset_def)

lemma equivLabId_rel: "L1 \<cong>\<^sup>\<A> L2 \<longleftrightarrow> L1 = L2" oops (* does not hold as expected *)
lemma IdLabImplEquiv_rel: "L1 = L2 \<Longrightarrow> L1 \<cong>\<^sup>\<A> L2" (* of course this one-sided direction holds *)
  by (simp add: equivalentLab_rel_def)


(***********************************************************)
(***********************************************************)
(*        Argument justification (cf. [BCG 2011] \<section>4).      *)
(***********************************************************)
(***********************************************************)

type_synonym 'a LabSemantics = \<open>'a Rel \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>

(* semantics has to be non-empty *)
definition skepticallyJustified :: \<open>'a LabSemantics \<Rightarrow> 'a Rel \<Rightarrow> 'a \<Rightarrow> bool\<close> ("sJ")
  where \<open>sJ S att \<equiv> \<lambda>arg. \<forall>Lab. ((\<exists>x. (Lab x) = In) \<and> (S att Lab)) \<longrightarrow> Lab(arg) = In\<close>
(* non-emptiness implicit *)
definition credulouslyJustified :: \<open>'a LabSemantics \<Rightarrow> 'a Rel \<Rightarrow> 'a \<Rightarrow> bool\<close> ("cJ")
  where \<open>cJ S att \<equiv> \<lambda>arg. \<exists>Lab. (S att Lab) \<and> Lab(arg) = In\<close>

lemma \<open>\<exists> S att a. \<not>(sJ S att a \<longrightarrow> cJ S att a)\<close>
  unfolding skepticallyJustified_def credulouslyJustified_def
  by auto
lemma \<open>cJ S att a \<Longrightarrow> sJ S att a\<close> nitpick oops (* expected *)


(***********************************************************)
(***********************************************************)
(*     Technical auxiliary definitions for experiments     *)
(***********************************************************)
(***********************************************************)

(* The predicate below is actually equivalent to: S = (Prop att). 
This is useful for obtaining at once *all* sets of extensions/labellings by using Nitpick *)
abbreviation \<open>findFor  att Prop S \<equiv> \<forall>x.  S x  \<longleftrightarrow> Prop att x\<close>
(* For technical reasons, we will often employ the equivalent formulation below.
(when using sets instead of predicates, we get nitpick to output only the contained elements) *)
abbreviation \<open>findFor' att Prop S \<equiv> \<forall>x. x \<in> S \<longleftrightarrow> Prop att x\<close>

(* Technical: Include into Defs collection *)
declare plusset_def[Defs] minusset_def[Defs] 
        plusset_rel_def[Defs] minusset_rel_def[Defs]
        defends_def[Defs] defends_rel_def[Defs]
        inset_def[Defs] outset_def[Defs] undecset_def[Defs]

end
