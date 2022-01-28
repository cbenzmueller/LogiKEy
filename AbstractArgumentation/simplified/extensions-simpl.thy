(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains extension-based semantics for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "extensions-simpl"
  imports "../base"
begin

(***********************************************************)
(* Conflict-free extensions.                               *)
(***********************************************************)

(* A set S of arguments is said to be conflict-free if there are no arguments A and B in S 
  such that A attacks B ([Dung 1995] Def. 5 and [BCG 2011] Def. 12). *)
definition conflictfreeExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>conflictfreeExt \<equiv> \<lambda>AF S. \<forall>a b. (S a \<and> S b) \<longrightarrow> \<not>(AF a b)\<close>

(***********************************************************)
(* Admissible extensions.                                  *)
(***********************************************************)

(* A set of arguments S is admissible if it is conflict-free and each argument in S is
  defended by S ([Dung 1995] Def. 6(2) and [BCG 2011] Def. 13). *)
definition admissibleExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>admissibleExt \<equiv> \<lambda>AF S. conflictfreeExt AF S \<and> (\<forall>a. S a \<longrightarrow> defends AF S a)\<close>

(***********************************************************)
(* Complete extensions.                                    *)
(***********************************************************)

(* An admissible set S of arguments is called a complete extension if each argument,
  which is defended by S, belongs to S ([Dung 1995] Def. 23). *)
definition completeExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>completeExt \<equiv> \<lambda>AF S. admissibleExt AF S \<and> (\<forall>a. defends AF S a \<longrightarrow> S a)\<close>

(* Alternatively, complete extensions can be defined as conflict-free fixed points of \<F> (see [Dung 1995] Lemma 24)*)
definition completeExt2 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>completeExt2 \<equiv> \<lambda>AF S. conflictfreeExt AF S \<and> fixpoint (\<F> AF) S\<close>

(***********************************************************)
(* Grounded extensions.                                    *)
(***********************************************************)

(* The grounded extension of an argumentation framework AF is a minimal complete extension ([BCG 2011] Def. 21). *)
definition groundedExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>groundedExt AF S \<equiv> minimal (completeExt AF) S id\<close>

(* Alternatively, grounded extensions can be defined as least complete extensions*)
definition groundedExt2 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>groundedExt2 AF S \<equiv> least (completeExt AF) S id\<close>

(* Alternatively, according to Dung, the grounded extension of an argumentation framework AF is
   the least fixed point of \<F> ([Dung 1995] Def. 20). *)
definition groundedExt3 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>groundedExt3 \<equiv> \<lambda>AF S. least (fixpoint (\<F> AF)) S id\<close>

(***********************************************************)
(* Preferred extensions.                                   *)
(***********************************************************)

(* A preferred extension of an argumentation framework AF is a maximal (with respect to set inclusion)
  complete extension of AF. *)
definition preferredExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>preferredExt \<equiv> \<lambda>AF S. maximal (completeExt AF) S id\<close>

(* Alternatively, preferred extensions can be defined as maximal admissible sets ([Dung 1995] Def. 7)*)
definition preferredExt2 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>preferredExt2 \<equiv> \<lambda>AF S. maximal (admissibleExt AF) S id\<close>

(***********************************************************)
(* Ideal extensions.                                       *)
(***********************************************************)

(* An ideal set is an admissible set that is subset of every preferred extension*)
definition idealSet :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>idealSet \<equiv> \<lambda>AF S. admissibleExt AF S \<and> (\<forall>E. preferredExt AF E \<longrightarrow> S \<subseteq> E)\<close>

(* An ideal extension of an argumentation framework AF is the (unique) 
  maximal (i.e greatest) ideal set. ([BCG 2011] Def. 30 and paragraph below). *)
definition idealExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>idealExt \<equiv> \<lambda>AF S. greatest (idealSet AF) S id\<close>
definition idealExt2 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>idealExt2 \<equiv> \<lambda>AF S. maximal (idealSet AF) S id\<close>

(***********************************************************)
(* Stable extensions.                                      *)
(***********************************************************)

(* We define the range of a set of arguments S as the union of S with the set 
  of its attacked arguments. *)
definition range :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close>
  where \<open>range AF \<equiv> \<lambda>S. S \<union> [AF|S]\<^sup>+\<close>

(* A stable extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ = Args ([BCG 2011] Def. 25). *)
definition stableExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>stableExt \<equiv> \<lambda>AF S. conflictfreeExt AF S \<and> range AF S \<approx> (\<lambda>x. True)\<close>

definition stableExt2 :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>stableExt2 \<equiv> \<lambda>AF S. S \<approx> (\<lambda>a. \<not>[AF|S]\<^sup>+ a)\<close>

(***********************************************************)
(* Semi-stable extensions.                                 *)
(***********************************************************)

(* A semi-stable extension of an argumentation framework AF is a complete extension E
   such that E \<union> E\<^sup>+ is maximal among all complete extensions. ([BCG 2011] Def. 27). *)
definition semistableExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>semistableExt \<equiv> \<lambda>AF S. maximal (completeExt AF) S (range AF)\<close>

(***********************************************************)
(* Stage extensions.                                       *)
(***********************************************************)

(* A stage extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ is maximal among all conflict-free extensions. ([BCG 2011] Def. 32). *)
definition stageExt :: \<open>'a Rel \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>stageExt \<equiv> \<lambda>AF S. maximal (conflictfreeExt AF) S (range AF)\<close>


(* Technical: Include labellings into Defs collection *)
declare conflictfreeExt_def[Defs] admissibleExt_def[Defs] 
        completeExt_def[Defs] completeExt2_def[Defs] 
        groundedExt_def[Defs] groundedExt2_def[Defs] groundedExt3_def[Defs]
        preferredExt_def[Defs] preferredExt2_def[Defs]
        stableExt_def[Defs] stableExt2_def[Defs]
        semistableExt_def[Defs]
        idealSet_def[Defs] idealExt_def[Defs] idealExt2_def[Defs]
        stageExt_def[Defs]
end
