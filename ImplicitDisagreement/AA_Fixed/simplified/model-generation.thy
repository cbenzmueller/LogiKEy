theory "model-generation"
  imports "correspondence-simpl"
begin
nitpick_params [box=false, card Label=3, sat_solver=SAT4J]

(* Exact datatype cardinalities avoid undersized, spurious search scopes. Cardinality
   display terms are omitted because their list/nat encoding can produce potential models.
   The returned families still show every extension or labelling.
   These Nitpick/oops commands are exploratory queries, not asserted theorems.
   In particular an empty returned family is different from an empty extension. *)

(* Example set-up from [BG2011], Figure 4 *)
locale ExFig4 begin
datatype Arg = A | B | C | D
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B C = True" |
    "att C D = True" |
    "att D C = True" |
    "att _ _ = False"

lemma all_Arg: "(\<forall>x::Arg. P x) \<longleftrightarrow> P A \<and> P B \<and> P C \<and> P D"
  by (metis Arg.exhaust)

lemma ex_Arg: "(\<exists>x::Arg. P x) \<longleftrightarrow> P A \<or> P B \<or> P C \<or> P D"
  by (metis Arg.exhaust)

(* Kernel-checked witnesses complement the exploratory Nitpick queries. *)
lemma preferred_AC: "preferredExt att \<lbrace>A,C\<rbrace>"
  unfolding preferredExt_def maximal_def completeExt_def admissibleExt_def
    conflictfreeExt_def defends_def id_def
  by (auto simp: all_Arg ex_Arg)

lemma preferred_AD: "preferredExt att \<lbrace>A,D\<rbrace>"
  unfolding preferredExt_def maximal_def completeExt_def admissibleExt_def
    conflictfreeExt_def defends_def id_def
  by (auto simp: all_Arg ex_Arg)

lemma ideal_A: "idealExt att \<lbrace>A\<rbrace>"
proof -
  have admissible: "admissibleExt att \<lbrace>A\<rbrace>"
    unfolding admissibleExt_def conflictfreeExt_def defends_def by (auto simp: all_Arg ex_Arg)
  have contains_A: "E A" if "preferredExt att E" for E
    using that unfolding preferredExt_def maximal_def completeExt_def defends_def
    by (auto simp: all_Arg ex_Arg)
  have ideal: "idealSet att \<lbrace>A\<rbrace>"
    using admissible contains_A unfolding idealSet_def by auto
  have greatest: "S \<subseteq> \<lbrace>A\<rbrace>" if "idealSet att S" for S
    using that preferred_AC preferred_AD unfolding idealSet_def by (auto simp: all_Arg ex_Arg)
  show ?thesis using ideal greatest unfolding idealExt_def greatest_def by auto
qed

lemma ideal_labelling:
  "idealLab att (\<lambda>x. if x = A then In else if x = B then Out else Undec)"
proof -
  have conversion: "Ext2Lab att \<lbrace>A\<rbrace> =
    (\<lambda>x. if x = A then In else if x = B then Out else Undec)"
    by (simp add: Ext2Lab_def plusset_def fun_eq_iff all_Arg ex_Arg)
  show ?thesis using ideal_EL[rule_format, OF ideal_A] by (simp only: conversion)
qed

(****************************************************)
(* Flexible Generation of Extensions and Labellings *)
(****************************************************)

abbreviation surjective where  "surjective f \<equiv> \<forall>y. \<exists>x. f x = y"

(* Admissible labelling where A is In *)
lemma \<open>admissibleLab att Lab \<and> (Lab A) = In\<close> nitpick[card Arg=4,satisfy]                                                 oops

(* Admissible labelling where Lab is surjective *)
lemma \<open>admissibleLab att Lab \<and> (surjective Lab)\<close> nitpick[card Arg=4,satisfy]                                          oops

(* More than two In arguments are impossible; prove the bound directly. *)
lemma admissible_at_most_two_in:
  assumes adm: "admissibleLab att Lab"
  shows "card {x. in Lab x} \<le> 2"
proof -
  have not_B: "\<not> in Lab B"
  proof
    assume ib: "in Lab B"
    have lb: "legallyIn att Lab B" using adm ib unfolding admissibleLab_def by blast
    have oa: "out Lab A" using lb[unfolded legallyIn_def, rule_format, of A] by simp
    have la: "legallyOut att Lab A" using adm oa unfolding admissibleLab_def by blast
    have no_attack: "\<forall>y. \<not> att y A" by (simp add: all_Arg)
    show False using la no_attack unfolding legallyOut_def by blast
  qed
  have not_CD: "\<not> (in Lab C \<and> in Lab D)"
  proof
    assume both: "in Lab C \<and> in Lab D"
    have lc: "legallyIn att Lab C" using adm both unfolding admissibleLab_def by blast
    have od: "out Lab D" using lc[unfolded legallyIn_def, rule_format, of D] by simp
    show False using both od unfolding inset_def outset_def by simp
  qed
  show ?thesis
  proof (cases "in Lab C")
    case True
    have sub: "Set.subset_eq {x. in Lab x} {A,C}"
      using not_B not_CD True by (auto simp: Set.subset_eq all_Arg)
    have "card {x. in Lab x} \<le> card {A,C}"
      by (rule card_mono[OF _ sub]) simp
    then show ?thesis by simp
  next
    case False
    have sub: "Set.subset_eq {x. in Lab x} {A,D}"
      using not_B False by (auto simp: Set.subset_eq all_Arg)
    have "card {x. in Lab x} \<le> card {A,D}"
      by (rule card_mono[OF _ sub]) simp
    then show ?thesis by simp
  qed
qed

(****************************************************)
(* Standard Generation of Extensions and Labellings *)
(****************************************************)

(**** conflict-free sets ****)
lemma \<open>findFor' att conflictfreeExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 8 conflict-free sets (7 non-empty) mentioned in [BG2011] p. 8:
     {}, {A}, {B}, {C}, {D}, {A, C}, {A, D}, {B, D} *)

(**** admissible semantics ****)
(* ask nitpick for all admissible extensions/labellings *) 
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 5 sets (4 non-empty) predicted in [BG2011] p. 8:
  {}, {A}, {D}, {A, C}, {A, D} *)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 7 labellings (7 non-empty) predicted in [BG2011] p. 7:
      {(A := In,    B := Out,   C := In,    D := Out),
       (A := In,    B := Out,   C := Out,   D := In),
       (A := In,    B := Out,   C := Undec, D := Undec),
       (A := In,    B := Undec, C := Out,   D := In),
       (A := In,    B := Undec, C := Undec, D := Undec),
       (A := Undec, B := Undec, C := Out,   D := In),
       (A := Undec, B := Undec, C := Undec, D := Undec)} *)

(* complete semantics *)
lemma \<open>findFor' att completeExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 3 sets predicted in [BG2011] p. 10: {A}, {A, C}, {A, D} *)
lemma \<open>findFor' att completeLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 3 labellings predicted in [BG2011] p. 10: 
  {(   (A := In, B := Out, C := In,    D := Out),
       (A := In, B := Out, C := Out,   D := In),
       (A := In, B := Out, C := Undec, D := Undec)} *)

(* grounded semantics *)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives exactly the one extension given in [BG2011] p. 10:  {A} *)   
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[card Arg=4,satisfy,box=false] oops
(* This gives exactly the one labelling given in [BG2011] p. 10: 
      {(A := In, B := Out, C := Undec, D := Undec)} *)   
(* comment: we have to disable boxing for nitpick to find the model.*)

(* preferred semantics *)
(* This gives us exactly the 2 sets predicted in [BCG2011] p. 12: {A, C}, {A, D} *)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[card Arg=4,satisfy]                          oops
(* This gives us exactly the two labellings predicted in [BCG2011] p. 12
  {(A := In, B := Out, C := In,  D := Out),
   (A := In, B := Out, C := Out, D := In)} *)
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[card Arg=4,satisfy,box=false]                    oops
(* comment: we have to disable boxing for nitpick to find the model *)

(* ideal semantics *)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[card Arg=4,satisfy,box=false,timeout=60] oops (*don't use eval*)
(* This gives us exactly the same (grounded) set predicted in [BG2011] p. 18: {A}*)
(* The concrete ideal labelling is proved in ideal_labelling above. *)

(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[card Arg=4,satisfy] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* checked: these are exactly the two (preferred) extensions/labellings given in [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[card Arg=4,satisfy,box=false] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[card Arg=4,satisfy,box=false] oops
(* checked: these are exactly the two (preferred) extensions/labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

end 


(* Example set-up from [BG2011], Figure 5 *)
locale ExFig5 begin
datatype Arg = A | B | C | D
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B A = True" |
    "att A C = True" |
    "att B C = True" |
    "att C D = True" |
    "att _ _ = False"

lemma all_Arg: "(\<forall>x::Arg. P x) \<longleftrightarrow> P A \<and> P B \<and> P C \<and> P D"
  by (metis Arg.exhaust)

lemma ex_Arg: "(\<exists>x::Arg. P x) \<longleftrightarrow> P A \<or> P B \<or> P C \<or> P D"
  by (metis Arg.exhaust)

lemma preferred_AD: "preferredExt att \<lbrace>A,D\<rbrace>"
  unfolding preferredExt_def maximal_def completeExt_def admissibleExt_def
    conflictfreeExt_def defends_def id_def
  by (auto simp: all_Arg ex_Arg)

lemma preferred_BD: "preferredExt att \<lbrace>B,D\<rbrace>"
  unfolding preferredExt_def maximal_def completeExt_def admissibleExt_def
    conflictfreeExt_def defends_def id_def
  by (auto simp: all_Arg ex_Arg)

lemma ideal_empty: "idealExt att \<lbrace>-\<rbrace>"
proof -
  have ideal: "idealSet att \<lbrace>-\<rbrace>"
    unfolding idealSet_def admissibleExt_def conflictfreeExt_def by simp
  have greatest: "S \<subseteq> \<lbrace>-\<rbrace>" if "idealSet att S" for S
    using that preferred_AD preferred_BD
    unfolding idealSet_def admissibleExt_def defends_def
    by (auto simp: all_Arg ex_Arg)
  show ?thesis using ideal greatest unfolding idealExt_def greatest_def by auto
qed

lemma ideal_labelling: "idealLab att (\<lambda>_. Undec)"
  using ideal_EL[rule_format, OF ideal_empty]
  unfolding Ext2Lab_def plusset_def by simp


(*** admissible semantics ***)
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 5 sets (4 non-empty) predicted in [BG2011] p. 8:
  {}, {A}, {B}, {A, D}, {B, D} *)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us 7 labellings. Note that their In-sets coincide with the corresponding
   admissible extensions (note that we can assign more than one labelling to each extension)
    Labs =
      {(A := In, B := Out, C := Out, D := In),
       (A := In, B := Out, C := Out, D := Undec),
       (A := In, B := Out, C := Undec, D := Undec),
       (A := Out, B := In, C := Out, D := In),
       (A := Out, B := In, C := Out, D := Undec),
       (A := Out, B := In, C := Undec, D := Undec),
       (A := Undec, B := Undec, C := Undec, D := Undec)} *) 

(*** complete semantics ***)
lemma \<open>findFor' att completeExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 3 sets predicted in [BG2011] p. 10: {}, {A, D}, {B, D} *)
lemma \<open>findFor' att completeLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 3 labellings indicated in [BG2011] p. 10
   Labs =  {(A := In, B := Out, C := Out, D := In),
            (A := Out, B := In, C := Out, D := In),
            (A := Undec, B := Undec, C := Undec, D := Undec)} *)

(*** grounded semantics ***)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* We verify that the grounded extension is the trivial one (i.e. empty) as indicated in [BG2011]*)
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[card Arg=4,satisfy, box=false] oops
(* Similarly we verify that the grounded labelling is the trivial one (i.e. empty) *)
(* (comment: we have to disable boxing for nitpick to find the model) *)


(*** preferred semantics ***)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[card Arg=4,satisfy] oops
(* This gives us exactly the 2 sets predicted in [BG2011] p. 12: {A, D}, {B, D} *)
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[card Arg=4,satisfy, box=false] oops
(* checked: these are exactly the two labellings given in [BG2011] p. 12 
  Labs = {(A := In, B := Out, C := Out, D := In), (A := Out, B := In, C := Out, D := In)}*)
(* comment: we have to disable boxing for nitpick to find the model *)

(*** ideal semantics ***)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[card Arg=4,satisfy] oops (*don't use eval*)
(* coincides with the grounded extension (empty) as predicted.*)
(* The concrete ideal labelling is proved in ideal_labelling above. *)


(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[card Arg=4,satisfy] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[card Arg=4,satisfy] oops
(* checked: these are exactly the sets o two extensions & labellings given in [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[card Arg=4,satisfy] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[card Arg=4,satisfy,box=false] oops
(* checked: these are exactly the two given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)
end

(* Example set-up from [BG2011], Figure 6 *)
locale ExFig6 begin
datatype Arg = A | B | C
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B C = True" |
    "att C A = True" |
    "att _ _ = False"

lemma all_Arg: "(\<forall>x::Arg. P x) \<longleftrightarrow> P A \<and> P B \<and> P C"
  by (metis Arg.exhaust)

lemma ex_Arg: "(\<exists>x::Arg. P x) \<longleftrightarrow> P A \<or> P B \<or> P C"
  by (metis Arg.exhaust)

lemma only_empty_admissible: "admissibleExt att S \<longleftrightarrow> S \<approx> \<lbrace>-\<rbrace>"
  unfolding admissibleExt_def conflictfreeExt_def defends_def
  by (auto simp: all_Arg ex_Arg)

lemma ideal_empty: "idealExt att \<lbrace>-\<rbrace>"
  unfolding idealExt_def greatest_def idealSet_def
  using only_empty_admissible by auto

lemma ideal_labelling: "idealLab att (\<lambda>_. Undec)"
  using ideal_EL[rule_format, OF ideal_empty]
  unfolding Ext2Lab_def plusset_def by simp


(*Similarly to the two examples above, we verify that the expected results obtain,
 namely, there exists only one admissible extension/labelling: the empty set*)

(*** admissible semantics ***)
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[card Arg=3,satisfy] oops
(* We verify the expected result: only the empty set is admissible*)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[card Arg=3,satisfy] oops
(* this gives us: Labs = {(\<lambda>x. _)(A := Undec, B := Undec, C := Undec)} *)
(* this is the one trivial labelling, as mentioned in [BG2011]. *) 

(*** complete semantics ***)
lemma \<open>findFor' att completeExt Exts\<close> nitpick[card Arg=3,satisfy] oops
lemma \<open>findFor' att completeLab Labs\<close> nitpick[card Arg=3,satisfy] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 

(*** grounded semantics ***)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[card Arg=3,satisfy] oops
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[card Arg=3,satisfy,box=false] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 

(*** preferred semantics ***)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[card Arg=3,satisfy] oops
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[card Arg=3,satisfy,box=false] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)

(*** ideal semantics ***)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[card Arg=3,satisfy] oops
(* The concrete ideal labelling is proved in ideal_labelling above. *)

(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[card Arg=3,satisfy] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[card Arg=3,satisfy] oops
(* checked: there are no stable extensionslabellings, see [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[card Arg=3,satisfy] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[card Arg=3,satisfy,box=false] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)
end

end

