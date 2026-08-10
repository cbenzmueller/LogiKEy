theory Day1_LiarsStreet
  imports Main

begin

\<comment>\<open>LIAR'S STREET — background theory\<close>

  nitpick_params [user_axioms, format = 2, show_all, max_genuine = 4]
  declare [[show_abbrevs = false]]

\<comment>\<open>The world: there are two persons and the two roads to live.\<close>

  datatype    Entity = Nilda  | Carla 

  lemma   "\<not>(Nilda = Carla)" by simp

  datatype Street = LiarsStreet | TruthtellersRoad 

\<comment>\<open>The words: friendly names for ordinary logic, so the sentences read like English.\<close>

  definition And       ("_ and _")              where          "X and Y \<equiv> X \<and> Y"
  definition Or         ("_ or _")                 where            "X or Y \<equiv> X \<or> Y"
  definition Not        ("not _")                 where             "not X \<equiv> \<not>X"
  definition If_then   ("If _ then _")          where     "If X then Y \<equiv> X \<longrightarrow> Y"

  named_theorems Logic 
  declare And_def [Logic] Or_def [Logic] Not_def [Logic] If_then_def [Logic] 

  consts Says::"Entity\<Rightarrow>bool\<Rightarrow>bool"            ("_ says _")
  consts Knows::"Entity\<Rightarrow>bool\<Rightarrow>bool"         ("_ knows _")
  consts Believes::"Entity\<Rightarrow>bool\<Rightarrow>bool"      ("_ believes _")
  consts Obligation::"Entity\<Rightarrow>bool\<Rightarrow>bool"   ("_ must-do _")
  consts Lives_in::"Entity\<Rightarrow>Street\<Rightarrow>bool"    ("_ lives-in _")

  definition Lies                  ("_ lies")                   where                    "X lies \<equiv> \<forall>Y. If (X says Y) then not Y"
  definition Says_the_truth ("_ says-the-truth")   where    "X says-the-truth \<equiv> \<forall>Y. If (X says Y) then Y"
  definition Lives_not_in     ("_ lives-not-in _")     where      "X lives-not-in G \<equiv> not (X lives-in G)"
  definition Neither_nor_live_in ("neither _ nor _ live-in _")      
                                                       where        "neither X nor Y live-in G \<equiv> (not (X lives-in G)) and (not (Y lives-in G))"
  definition Both_live_in  ("both _ and _ live-in _")         
                                                       where           "both X and Y live-in G \<equiv> (X lives-in G) and (Y lives-in G)"

  named_theorems Language
  declare  Lies_def [Language] Says_the_truth_def [Language] Lives_not_in_def [Language] 
    Neither_nor_live_in_def [Language] Both_live_in_def [Language]

\<comment>\<open>The rules of the town (delete A3 for the looser "open world" version).\<close>

  axiomatization where
    A1: "\<forall>X. If (X lives-in LiarsStreet) then (X lies)"  and
    A2: "\<forall>X. If (X lives-in TruthtellersRoad) then (X says-the-truth)"  and
    A3: "\<forall>X.       ((X lives-in LiarsStreet) \<or> (X lives-in TruthtellersRoad)) 
                 \<and> \<not> ((X lives-in LiarsStreet) \<and> (X lives-in TruthtellersRoad))"

\<comment>\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 1 — The accusation
     Nilda:  "Carla lives on Liars Street!"
     Carla:  "Neither of us lives on Liars Street."
   Who lives where?  Predict: ONE solution, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>

  lemma DEMO_1:
    assumes
      "Nilda says (Carla lives-in LiarsStreet)"
      "Carla says (neither Nilda nor Carla live-in LiarsStreet)"
    shows
      "((Nilda lives-in S1) and (Carla lives-in S2))" 

      using assms unfolding Language unfolding Logic
      nitpick[satisfy] 
      oops

\<comment>\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 2 — The compliments
     Nilda:  "Carla lives on Truthtellers Road."
     Carla:  "Nilda lives on Truthtellers Road."
   How sweet. But can we tell where they live?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>

  lemma DEMO_2:
    assumes
      "Nilda says (Carla lives-in TruthtellersRoad)"
      "Carla says (Nilda lives-in TruthtellersRoad)"
    shows
      "((Nilda lives-in S1) and (Carla lives-in S2))" 

      using assms unfolding Language unfolding Logic
      nitpick[satisfy] 
      oops

\<comment>\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 3 — The confession
     Nilda:  "Carla lives on Liars Street."
     Carla:  "I live on Liars Street."
   Wait — can Carla even SAY that?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>

  lemma DEMO_3:
    assumes
      "Nilda says (Carla lives-in LiarsStreet)"
      "Carla says (Carla lives-in LiarsStreet)"
    shows
      "((Nilda lives-in S1) and (Carla lives-in S2))" 

      using assms unfolding Language unfolding Logic
      nitpick[satisfy] 
      oops

\<comment>\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 4 — Your turn! Edit the two "says" lines below and invent your own riddle.
     Can you build one with exactly one solution? One with none?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>

  lemma DEMO_4_make_your_own:
    assumes
      "Nilda says (Carla lives-in TruthtellersRoad)"
      "Carla says (Nilda lives-in LiarsStreet)"
    shows
      "((Nilda lives-in S1) and (Carla lives-in S2))" 

    using assms unfolding Language unfolding Logic
    nitpick[satisfy] 
    oops

\<comment>\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 5 — The impossible sentence In this town, NOBODY can ever say "I am a liar" — not the liars, not the
     truthtellers. This time it is not a puzzle but a THEOREM, and the prover finds the argument on its own 
     (try sledgehammer!). Nitpick agrees: uncomment it and it finds no world at all.
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>

  lemma DEMO_5_the_impossible_sentence:
    assumes "Nilda says (Nilda lies)"
    shows False 

    using assms unfolding Language unfolding Logic
    nitpick[satisfy] 
    nitpick
    sledgehammer
    by (smt (verit) A1 A2 A3 If_then_def Lies_def Not_def Says_the_truth_def)

\<comment>\<open>BONUS — a first crack in the model: "says"/"knows" are naive truth-functions here, so saying/knowing one true 
  thing forces saying/knowing EVERY true thing — a crude model of knowledge (the "logical omniscience" problem).
  Tomorrow (Day 2) we repair this properly, with possible-worlds semantics  embedded in HOL.\<close>

  consts It_holds_that_One_plus_One_Equals_Two::bool
  consts It_holds_that_Fermats_last_Theorem_is_True::bool

  lemma BONUS_says_too_much:
    assumes 
      "It_holds_that_One_plus_One_Equals_Two" 
      "It_holds_that_Fermats_last_Theorem_is_True" 
      "Carla says It_holds_that_One_plus_One_Equals_Two"
    shows 
      "Carla says It_holds_that_Fermats_last_Theorem_is_True"

    using assms unfolding Language unfolding Logic
    nitpick[satisfy] 
    nitpick 
    sledgehammer
    oops

  lemma BONUS_knows_too_much:
    assumes 
      "It_holds_that_One_plus_One_Equals_Two" 
      "It_holds_that_Fermats_last_Theorem_is_True" 
      "Carla knows It_holds_that_One_plus_One_Equals_Two"
    shows 
      "Carla knows It_holds_that_Fermats_last_Theorem_is_True"

      using assms unfolding Language unfolding Logic
      nitpick[satisfy] 
      nitpick
      sledgehammer
      oops

end
