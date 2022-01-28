theory "model-generation"
  imports "extensions-simpl"  "labellings-simpl"
begin
nitpick_params [box=false]

(* Example set-up from [BG2011], Figure 4 *)
locale ExFig4 begin
datatype Arg = A | B | C | D
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B C = True" |
    "att C D = True" |
    "att D C = True" |
    "att _ _ = False"

(****************************************************)
(* Flexible Generation of Extensions and Labellings *)
(****************************************************)

abbreviation surjective where  "surjective f \<equiv> \<forall>y. \<exists>x. f x = y"

(* Admissible labelling where A is In *)
lemma \<open>admissibleLab att Lab \<and> (Lab a) = In\<close> nitpick[satisfy]                                                 oops

(* Admissible labelling where Lab is surjective *)
lemma \<open>admissibleLab att Lab \<and> (surjective Lab)\<close> nitpick[satisfy]                                          oops

(* Admissible labelling where there are more than two arguments labelled In *)
lemma \<open>admissibleLab att Lab \<and> (card({x. in(Lab) x}) > 2)\<close> nitpick[satisfy]                                  oops

(****************************************************)
(* Standard Generation of Extensions and Labellings *)
(****************************************************)

(**** conflict-free sets ****)
lemma \<open>findFor' att conflictfreeExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 8 conflict-free sets (7 non-empty) mentioned in [BG2011] p. 8:
     {}, {A}, {B}, {C}, {D}, {A, C}, {A, D}, {B, D} *)

(**** admissible semantics ****)
(* ask nitpick for all admissible extensions/labellings *) 
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 5 sets (4 non-empty) predicted in [BG2011] p. 8:
  {}, {A}, {D}, {A, C}, {A, D} *)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* This gives us exactly the 7 labellings (7 non-empty) predicted in [BG2011] p. 7:
      {(A := In,    B := Out,   C := In,    D := Out),
       (A := In,    B := Out,   C := Out,   D := In),
       (A := In,    B := Out,   C := Undec, D := Undec),
       (A := In,    B := Undec, C := Out,   D := In),
       (A := In,    B := Undec, C := Undec, D := Undec),
       (A := Undec, B := Undec, C := Out,   D := In),
       (A := Undec, B := Undec, C := Undec, D := Undec)} *)

(* complete semantics *)
lemma \<open>findFor' att completeExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 3 sets predicted in [BG2011] p. 10: {A}, {A, C}, {A, D} *)
lemma \<open>findFor' att completeLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* This gives us exactly the 3 labellings predicted in [BG2011] p. 10: 
  {(   (A := In, B := Out, C := In,    D := Out),
       (A := In, B := Out, C := Out,   D := In),
       (A := In, B := Out, C := Undec, D := Undec)} *)

(* grounded semantics *)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives exactly the one extension given in [BG2011] p. 10:  {A} *)   
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* This gives exactly the one labelling given in [BG2011] p. 10: 
      {(A := In, B := Out, C := Undec, D := Undec)} *)   
(* comment: we have to disable boxing for nitpick to find the model.*)

(* preferred semantics *)
(* This gives us exactly the 2 sets predicted in [BCG2011] p. 12: {A, C}, {A, D} *)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[satisfy, eval = "card Exts"]                          oops
(* This gives us exactly the two labellings predicted in [BCG2011] p. 12
  {(A := In, B := Out, C := In,  D := Out),
   (A := In, B := Out, C := Out, D := In)} *)
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"]                    oops
(* comment: we have to disable boxing for nitpick to find the model *)

(* ideal semantics *)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[satisfy,box=false,timeout=60] oops (*don't use eval*)
(* This gives us exactly the same (grounded) set predicted in [BG2011] p. 18: {A}*)
lemma \<open>findFor' att idealLab Labs\<close> (*nitpick[satisfy,box=false, timeout=100]*) oops
(* TODO above not working - definition too complex? *)

(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: these are exactly the two (preferred) extensions/labellings given in [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[satisfy,box=false, eval = "card Exts"] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
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

(*** admissible semantics ***)
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 5 sets (4 non-empty) predicted in [BG2011] p. 8:
  {}, {A}, {B}, {A, D}, {B, D} *)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
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
lemma \<open>findFor' att completeExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 3 sets predicted in [BG2011] p. 10: {}, {A, D}, {B, D} *)
lemma \<open>findFor' att complete Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* This gives us exactly the 3 labellings indicated in [BG2011] p. 10
   Labs =  {(A := In, B := Out, C := Out, D := In),
            (A := Out, B := In, C := Out, D := In),
            (A := Undec, B := Undec, C := Undec, D := Undec)} *)

(*** grounded semantics ***)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* We verify that the grounded extension is the trivial one (i.e. empty) as indicated in [BG2011]*)
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[satisfy, box=false, eval = "card Labs"] oops
(* Similarly we verify that the grounded labelling is the trivial one (i.e. empty) *)
(* (comment: we have to disable boxing for nitpick to find the model) *)


(*** preferred semantics ***)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* This gives us exactly the 2 sets predicted in [BG2011] p. 12: {A, D}, {B, D} *)
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[satisfy, box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] p. 12 
  Labs = {(A := In, B := Out, C := Out, D := In), (A := Out, B := In, C := Out, D := In)}*)
(* comment: we have to disable boxing for nitpick to find the model *)

(*** ideal semantics ***)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[satisfy] oops (*don't use eval*)
(* coincides with the grounded extension (empty) as predicted.*)
lemma \<open>findFor' att idealLab Labs\<close> (*nitpick[satisfy,box=false, timeout=100]*) oops
(* TODO above not working - definition too complex? *)


(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: these are exactly the sets o two extensions & labellings given in [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
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

(*Similarly to the two examples above, we verify that the expected results obtain,
 namely, there exists only one admissible extension/labelling: the empty set*)

(*** admissible semantics ***)
lemma \<open>findFor' att admissibleExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
(* We verify the expected result: only the empty set is admissible*)
lemma \<open>findFor' att admissibleLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* this gives us: Labs = {(\<lambda>x. _)(A := Undec, B := Undec, C := Undec)} *)
(* this is the one trivial labelling, as mentioned in [BG2011]. *) 

(*** complete semantics ***)
lemma \<open>findFor' att completeExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att completeLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 

(*** grounded semantics ***)
lemma \<open>findFor' att groundedExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att groundedLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 

(*** preferred semantics ***)
lemma \<open>findFor' att preferredExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att preferredLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)

(*** ideal semantics ***)
lemma \<open>findFor' att idealExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att idealLab Labs\<close>  (*nitpick[satisfy,box=false, timeout=100]*) oops
(* TODO above not working - definition too complex? *)

(* stable labellings *)
lemma \<open>findFor' att stableExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att stableLab Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: there are no stable extensionslabellings, see [BG2011] *)   

(* semi-stable labellings *)
lemma \<open>findFor' att semistableExt Exts\<close> nitpick[satisfy, eval = "card Exts"] oops
lemma \<open>findFor' att semistableLab Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: this is the one trivial extension/labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)
end

end

