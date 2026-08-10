theory Day1_LiarsStreet
  imports Main

  abbrevs "and" = "and"
      and "or" = "or"
      and "not" = "not"
      and "If" = "If"
      and "then" = "then"
      and "says" = "says"
      and "knows" = "knows"
      and "believes" = "believes"
      and "mustdo" = "must-do"
      and "lies" = "lies"
      and "saysthetruth" = "says-the-truth"
      and "livesin" = "lives-in"
      and "livesnotin" = "lives-not-in"
      and "neither" = "neither"
      and "nor" = "nor"
      and "both" = "both"
      and "livein" = "live-in"
      and "Nilda" = "Nilda"
      and "Carla" = "Carla"
      and "LiarsStreet" = "LiarsStreet"
      and "TruthtellersRoad" = "TruthtellersRoad"

begin


text\<open>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>
   LIAR'S STREET — riddles the computer solves for you
   \<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>

   Somewhere there is a little town with exactly two streets:

      LIARS STREET        — everyone who lives here ALWAYS lies;
      TRUTHTELLERS ROAD   — everyone who lives here ALWAYS tells the truth.

   Two kids, NILDA and CARLA, live in this town (in the spirit of Raymond
   Smullyan's classic knights-and-knaves puzzles). We overhear what they say —
   and from their words alone we work out where they live. Or rather: the
   computer does. Each demo below states a riddle. To solve it, remove the
   comment brackets around the  nitpick[satisfy]  line: Nitpick searches every
   possible world and reports what it finds.

   THE GAME: before you click, make your own prediction —
   does the riddle have exactly ONE solution, MANY, or NONE at all?
   (Spoilers at the very end of the file.)

   TIP — typing the riddle language: all constructs of our little language are
   registered as input abbreviations in the theory header above ("abbrevs").
   Just type the plain word —  says, lies, livesin, neither, Nilda, Carla, ... —
   and Isabelle/jEdit's completion popup offers the matching construct; confirm
   with ENTER or TAB (dismiss with ESC). Copy-pasting from the demos below
   works too, of course.\<close>

nitpick_params [user_axioms, format = 2, show_all]
declare [[show_abbrevs = false]]

text\<open>The world: who is there, and the two places to live.\<close>
datatype Entity = Nilda ("Nilda") | Carla ("Carla")
lemma "\<not>(Nilda = Carla)" by simp
datatype Street = LiarsStreet ("LiarsStreet") | TruthtellersRoad ("TruthtellersRoad")

text\<open>The words: friendly names for ordinary logic, so the sentences read like English.\<close>
definition And ("_ and _") where "X and Y \<equiv> X \<and> Y"
abbreviation Or ("_ or _") where "X or Y \<equiv> X \<or> Y"
definition Not ("not _") where "not X \<equiv> \<not>X"
definition If_then ("If _ then _") where "If X then Y \<equiv> X \<longrightarrow> Y"

consts Says::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ says _")
consts Knows::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ knows _")
consts Believes::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ believes _")
consts Obligation::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ must-do _")

definition Lies ("lies _") where "lies X \<equiv> \<forall>Y. If (X says Y) then not Y"
definition Says_the_truth ("says-the-truth _") where "says-the-truth X \<equiv> \<forall>Y. If (X says Y) then Y"
named_theorems Defs
declare Lies_def [Defs] Says_the_truth_def [Defs]

consts Lives_in::"Entity\<Rightarrow>Street\<Rightarrow>bool" ("_ lives-in _")
definition Lives_not_in ("_ lives-not-in _") where "X lives-not-in G \<equiv> not (X lives-in G)"
definition Neither_nor_live_in ("neither _ nor _ live-in _") where
  "neither X nor Y live-in G \<equiv> (not (X lives-in G)) and (not (Y lives-in G))"
definition Both_live_in ("both _ and _ live-in _") where
  "both X and Y live-in G \<equiv> (X lives-in G) and (Y lives-in G)"
declare Lives_not_in_def [Defs] Neither_nor_live_in_def [Defs] Both_live_in_def [Defs]

text\<open>The rules of the town (delete OneHome for the looser "open world" version).\<close>
axiomatization where
  A1: "\<forall>X. If (X lives-in LiarsStreet) then (lies X)"  and
  A2: "\<forall>X. If (X lives-in TruthtellersRoad) then (says-the-truth X)"  and
  OneHome: "\<forall>X. ((X lives-in LiarsStreet) \<or> (X lives-in TruthtellersRoad))
                  \<and> \<not> ((X lives-in LiarsStreet) \<and> (X lives-in TruthtellersRoad))"

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 1 — The accusation
     Nilda:  "Carla lives on Liars Street!"
     Carla:  "Neither of us lives on Liars Street."
   Who lives where?  Predict: ONE solution, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_1:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)"
   "Carla says (neither Nilda nor Carla live-in LiarsStreet)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 2 — The compliments
     Nilda:  "Carla lives on Truthtellers Road."
     Carla:  "Nilda lives on Truthtellers Road."
   How sweet. But can we tell where they live?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_2:
  assumes
   "Nilda says (Carla lives-in TruthtellersRoad)"
   "Carla says (Nilda lives-in TruthtellersRoad)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 3 — The confession
     Nilda:  "Carla lives on Liars Street."
     Carla:  "I live on Liars Street."
   Wait — can Carla even SAY that?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_3:
  assumes
   "Nilda says (Carla lives-in LiarsStreet)"
   "Carla says (Carla lives-in LiarsStreet)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 4 — Your turn!
     Edit the two "says" lines below and invent your own riddle.
     Can you build one with exactly one solution? One with none?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_4_make_your_own:
  assumes
   "Nilda says (Carla lives-in TruthtellersRoad)"
   "Carla says (Nilda lives-in LiarsStreet)"
  shows
   "((Nilda lives-in S1) and (Carla lives-in S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops



text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 5 — The impossible sentence
     In this town, NOBODY can ever say "I am a liar" — not the liars, not the
     truthtellers. This time it is not a puzzle but a THEOREM, and the prover
     finds the argument on its own (try sledgehammer!). Nitpick agrees:
     uncomment it and it finds no world at all.
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_5_the_impossible_sentence:
  assumes "Nilda says (lies Nilda)"
  shows False
  (* nitpick[satisfy] *)
  using assms A1 A2 OneHome unfolding Defs If_then_def Not_def by (smt (verit))



text\<open>BONUS — a first crack in the model: "says"/"knows" are naive truth-functions
   here, so saying/knowing one true thing forces saying/knowing EVERY true
   thing — a crude model of knowledge (the "logical omniscience" problem).
   Tomorrow (Day 2) we repair this properly, with possible-worlds semantics
   embedded in HOL.\<close>
consts It_holds_that_One_plus_One_Equals_Two::bool
consts It_holds_that_Fermats_last_Theorem_is_True::bool
lemma BONUS_says_too_much:
  assumes 
    "It_holds_that_One_plus_One_Equals_Two" 
    "It_holds_that_Fermats_last_Theorem_is_True" 
    "Carla says It_holds_that_One_plus_One_Equals_Two"
  shows 
    "Carla says It_holds_that_Fermats_last_Theorem_is_True"
  using assms(1) assms(2) assms(3) by auto

lemma BONUS_knows_too_much:
  assumes 
    "It_holds_that_One_plus_One_Equals_Two" 
    "It_holds_that_Fermats_last_Theorem_is_True" 
    "Carla knows It_holds_that_One_plus_One_Equals_Two"
  shows 
    "Carla knows It_holds_that_Fermats_last_Theorem_is_True"
  using assms(1) assms(2) assms(3) by auto


text\<open>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>
   SPOILERS — don't peek before you've made your predictions!

   DEMO 1 (The accusation): exactly ONE solution. If Nilda lived on Liars
     Street, her accusation would be false, so Carla would live on Truthtellers
     Road — but then Carla's (true!) statement would put Nilda off Liars
     Street: contradiction. So Nilda tells the truth, Carla lives on Liars
     Street, and Carla's statement is duly a lie.

   DEMO 2 (The compliments): MANY (two) solutions. Both on Truthtellers Road
     works — but so does both on Liars Street, each falsely praising the other!
     The riddle does not determine where they live.

   DEMO 3 (The confession): NO solution. Carla's sentence is the liar paradox
     in disguise: a liar saying "I live on Liars Street" would be telling the
     truth, a truthteller would be lying. Nitpick searches every world and
     finds none.

   DEMO 5 (The impossible sentence): the same phenomenon, now as a theorem —
     in this town, "I am a liar" is a sentence nobody can utter.
   \<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<Midarrow>\<close>

end
