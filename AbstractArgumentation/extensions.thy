(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains extension-based semantics for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory extensions
  imports base 
begin

(***********************************************************)
(* Conflict-free extensions.                               *)
(***********************************************************)

(* A set S of arguments is said to be conflict-free if there are no arguments A and B in S 
  such that A attacks B ([Dung 1995] Def. 5 and [BCG 2011] Def. 12). *)
definition conflictfreeExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("conflictfreeExt\<^sup>_")
  where \<open>conflictfreeExt\<^sup>\<A> \<equiv> \<lambda>att S. \<forall>a b. (\<A> a \<and> \<A> b) \<longrightarrow> (S a \<and> S b) \<longrightarrow> \<not>(att a b)\<close>

(***********************************************************)
(* Admissible extensions.                                  *)
(***********************************************************)

(* A set of arguments S is admissible if it is conflict-free and each argument in S is
  defended by S ([Dung 1995] Def. 6(2) and [BCG 2011] Def. 13). *)
definition admissibleExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("admissibleExt\<^sup>_")
  where \<open>admissibleExt\<^sup>\<A> \<equiv> \<lambda>att S. conflictfreeExt\<^sup>\<A> att S \<and> (\<forall>a. \<A> a \<longrightarrow> S a \<longrightarrow> defends\<^sup>\<A> att S a)\<close>

(***********************************************************)
(* Complete extensions.                                    *)
(***********************************************************)

(* An admissible set S of arguments is called a complete extension if each argument,
  which is defended by S, belongs to S ([Dung 1995] Def. 23). *)
definition completeExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("completeExt\<^sup>_")
  where \<open>completeExt\<^sup>\<A> \<equiv> \<lambda>att S. admissibleExt\<^sup>\<A> att S \<and> (\<forall>a. \<A> a \<longrightarrow> defends\<^sup>\<A> att S a \<longrightarrow> S a)\<close>

(* Alternatively, complete extensions can be defined as conflict-free fixed points of \<F> (see [Dung 1995] Lemma 24)*)
definition completeExt2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("completeExt2\<^sup>_")
  where \<open>completeExt2\<^sup>\<A> \<equiv> \<lambda>att S. conflictfreeExt\<^sup>\<A> att S \<and> fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) S\<close>

(***********************************************************)
(* Grounded extensions.                                    *)
(***********************************************************)

(* The grounded extension of an argumentation framework AF is a minimal complete extension ([BCG 2011] Def. 21). *)
definition groundedExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("groundedExt\<^sup>_")
  where \<open>groundedExt\<^sup>\<A> \<equiv> \<lambda>att S. minimal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id\<close>

(* Alternatively, grounded extensions can be defined as least complete extensions*)
definition groundedExt2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("groundedExt2\<^sup>_")
  where \<open>groundedExt2\<^sup>\<A> \<equiv> \<lambda>att S. least\<^sup>\<A> (completeExt\<^sup>\<A> att) S id\<close>

(* Alternatively, according to Dung, the grounded extension of an argumentation framework AF is
   the least fixed point of \<F> ([Dung 1995] Def. 20). *)
definition groundedExt3 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("groundedExt3\<^sup>_")
  where \<open>groundedExt3\<^sup>\<A> \<equiv> \<lambda>att S. least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id\<close>

(***********************************************************)
(* Preferred extensions.                                   *)
(***********************************************************)

(* A preferred extension of an argumentation framework AF is a maximal (with respect to set inclusion)
  complete extension of AF. *)
definition preferredExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("preferredExt\<^sup>_")
  where \<open>preferredExt\<^sup>\<A> \<equiv> \<lambda>att S. maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id\<close>

(* Alternatively, preferred extensions can be defined as maximal admissible sets ([Dung 1995] Def. 7)*)
definition preferredExt2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("preferredExt2\<^sup>_")
  where \<open>preferredExt2\<^sup>\<A> \<equiv> \<lambda>att S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id\<close>

(***********************************************************)
(* Ideal extensions.                                       *)
(***********************************************************)

(* An ideal set is an admissible set that is subset of every preferred extension*)
definition idealSet :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("idealSet\<^sup>_")
  where \<open>idealSet\<^sup>\<A> \<equiv> \<lambda>att S. admissibleExt\<^sup>\<A> att S \<and> (\<forall>E. preferredExt\<^sup>\<A> att E \<longrightarrow> S \<subseteq>\<^sup>\<A> E)\<close>

(* An ideal extension of an argumentation framework AF is the (unique) 
  maximal (i.e greatest) ideal set. ([BCG 2011] Def. 30 and paragraph below). *)
definition idealExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("idealExt\<^sup>_")
  where \<open>idealExt\<^sup>\<A> \<equiv> \<lambda>att S. greatest\<^sup>\<A> (idealSet\<^sup>\<A> att) S id\<close>
definition idealExt2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("idealExt2\<^sup>_")
  where \<open>idealExt2\<^sup>\<A> \<equiv> \<lambda>att S. maximal\<^sup>\<A> (idealSet\<^sup>\<A> att) S id\<close>

(***********************************************************)
(* Stable extensions.                                      *)
(***********************************************************)

(* We define the range of a set of arguments S as the union of S with the set 
  of its attacked arguments. *)
definition range :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("range\<^sup>_")
  where \<open>range\<^sup>\<A> att \<equiv> \<lambda>S. S \<union> [\<A>|att|S]\<^sup>+\<close>

(* A stable extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ = Args ([BCG 2011] Def. 25). *)
definition stableExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("stableExt\<^sup>_")
  where \<open>stableExt\<^sup>\<A> \<equiv> \<lambda>att S. (conflictfreeExt\<^sup>\<A> att S) \<and> \<A> \<subseteq> range\<^sup>\<A> att S\<close>

definition stableExt2 :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("stableExt2\<^sup>_")
  where \<open>stableExt2\<^sup>\<A> \<equiv> \<lambda>att S. S \<approx>\<^sup>\<A> (\<lambda>a. \<not>[\<A>|att|S]\<^sup>+ a)\<close>

(***********************************************************)
(* Semi-stable extensions.                                 *)
(***********************************************************)

(* A semi-stable extension of an argumentation framework AF is a complete extension E
   such that E \<union> E\<^sup>+ is maximal among all complete extensions. ([BCG 2011] Def. 27). *)
definition semistableExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("semistableExt\<^sup>_")
  where \<open>semistableExt\<^sup>\<A> \<equiv> \<lambda>att S. maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S (range\<^sup>\<A> att)\<close>

(***********************************************************)
(* Stage extensions.                                       *)
(***********************************************************)

(* A stage extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ is maximal among all conflict-free extensions. ([BCG 2011] Def. 32). *)
definition stageExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> ("stageExt\<^sup>_")
  where \<open>stageExt\<^sup>\<A> \<equiv> \<lambda>att S. maximal\<^sup>\<A> (conflictfreeExt\<^sup>\<A> att) S (range\<^sup>\<A> att)\<close>

(* Technical: Include extensions into Defs collection *)
declare conflictfreeExt_def[Defs] admissibleExt_def[Defs] 
        completeExt_def[Defs] completeExt2_def[Defs] 
        groundedExt_def[Defs] groundedExt2_def[Defs] groundedExt3_def[Defs]
        preferredExt_def[Defs] preferredExt2_def[Defs]
        stableExt_def[Defs] stableExt2_def[Defs]
        semistableExt_def[Defs]
        idealSet_def[Defs] idealExt_def[Defs] idealExt2_def[Defs]
        stageExt_def[Defs]
end
