theory Day1_LiarsStreet
  imports Main

  abbrevs "and" = "\<^bold>a\<^bold>n\<^bold>d"
      and "or" = "\<^bold>o\<^bold>r"
      and "not" = "\<^bold>n\<^bold>o\<^bold>t"
      and "If" = "\<^bold>I\<^bold>f"
      and "then" = "\<^bold>t\<^bold>h\<^bold>e\<^bold>n"
      and "says" = "\<^bold>s\<^bold>a\<^bold>y\<^bold>s"
      and "knows" = "\<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s"
      and "believes" = "\<^bold>b\<^bold>e\<^bold>l\<^bold>i\<^bold>e\<^bold>v\<^bold>e\<^bold>s"
      and "mustdo" = "\<^bold>m\<^bold>u\<^bold>s\<^bold>t\<^bold>-\<^bold>d\<^bold>o"
      and "lies" = "\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
      and "saysthetruth" = "\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h"
      and "livesin" = "\<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n"
      and "livesnotin" = "\<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n"
      and "neither" = "\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r"
      and "nor" = "\<^bold>n\<^bold>o\<^bold>r"
      and "both" = "\<^bold>b\<^bold>o\<^bold>t\<^bold>h"
      and "livein" = "\<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n"
      and "Nilda" = "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a"
      and "Carla" = "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a"
      and "LiarsStreet" = "\<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t"
      and "TruthtellersRoad" = "\<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d"

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
   and Isabelle/jEdit's completion popup offers the bold construct; confirm
   with ENTER or TAB (dismiss with ESC). Copy-pasting from the demos below
   works too, of course.\<close>

nitpick_params [user_axioms, format = 2, show_all]
declare [[show_abbrevs = false]]

text\<open>The world: who is there, and the two places to live.\<close>
datatype Entity = Nilda ("\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a") | Carla ("\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a")
lemma "\<not>(\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a = \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a)" by simp
datatype Street = LiarsStreet ("\<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t") | TruthtellersRoad ("\<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d")

text\<open>The words: friendly names for ordinary logic, so the sentences read like English.\<close>
definition And ("_ \<^bold>a\<^bold>n\<^bold>d _") where "X \<^bold>a\<^bold>n\<^bold>d Y \<equiv> X \<and> Y"
abbreviation Or ("_ \<^bold>o\<^bold>r _") where "X \<^bold>o\<^bold>r Y \<equiv> X \<or> Y"
definition Not ("\<^bold>n\<^bold>o\<^bold>t _") where "\<^bold>n\<^bold>o\<^bold>t X \<equiv> \<not>X"
definition If_then ("\<^bold>I\<^bold>f _ \<^bold>t\<^bold>h\<^bold>e\<^bold>n _") where "\<^bold>I\<^bold>f X \<^bold>t\<^bold>h\<^bold>e\<^bold>n Y \<equiv> X \<longrightarrow> Y"

consts Says::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ \<^bold>s\<^bold>a\<^bold>y\<^bold>s _")
consts Knows::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s _")
consts Believes::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ \<^bold>b\<^bold>e\<^bold>l\<^bold>i\<^bold>e\<^bold>v\<^bold>e\<^bold>s _")
consts Obligation::"Entity\<Rightarrow>bool\<Rightarrow>bool" ("_ \<^bold>m\<^bold>u\<^bold>s\<^bold>t\<^bold>-\<^bold>d\<^bold>o _")

definition Lies ("\<^bold>l\<^bold>i\<^bold>e\<^bold>s _") where "\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<equiv> \<forall>Y. \<^bold>I\<^bold>f (X \<^bold>s\<^bold>a\<^bold>y\<^bold>s Y) \<^bold>t\<^bold>h\<^bold>e\<^bold>n \<^bold>n\<^bold>o\<^bold>t Y"
definition Says_the_truth ("\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h _") where "\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h X \<equiv> \<forall>Y. \<^bold>I\<^bold>f (X \<^bold>s\<^bold>a\<^bold>y\<^bold>s Y) \<^bold>t\<^bold>h\<^bold>e\<^bold>n Y"
named_theorems Defs
declare Lies_def [Defs] Says_the_truth_def [Defs]

consts Lives_in::"Entity\<Rightarrow>Street\<Rightarrow>bool" ("_ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n _")
definition Lives_not_in ("_ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n _") where "X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>n\<^bold>o\<^bold>t\<^bold>-\<^bold>i\<^bold>n G \<equiv> \<^bold>n\<^bold>o\<^bold>t (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)"
definition Neither_nor_live_in ("\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r _ \<^bold>n\<^bold>o\<^bold>r _ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n _") where
  "\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r X \<^bold>n\<^bold>o\<^bold>r Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n G \<equiv> (\<^bold>n\<^bold>o\<^bold>t (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)) \<^bold>a\<^bold>n\<^bold>d (\<^bold>n\<^bold>o\<^bold>t (Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G))"
definition Both_live_in ("\<^bold>b\<^bold>o\<^bold>t\<^bold>h _ \<^bold>a\<^bold>n\<^bold>d _ \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n _") where
  "\<^bold>b\<^bold>o\<^bold>t\<^bold>h X \<^bold>a\<^bold>n\<^bold>d Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n G \<equiv> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G) \<^bold>a\<^bold>n\<^bold>d (Y \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n G)"
declare Lives_not_in_def [Defs] Neither_nor_live_in_def [Defs] Both_live_in_def [Defs]

text\<open>The rules of the town (delete OneHome for the looser "open world" version).\<close>
axiomatization where
  A1: "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>l\<^bold>i\<^bold>e\<^bold>s X)"  and
  A2: "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h X)"  and
  OneHome: "\<forall>X. ((X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<or> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d))
                  \<and> \<not> ((X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<and> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d))"

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 1 — The accusation
     Nilda:  "Carla lives on Liars Street!"
     Carla:  "Neither of us lives on Liars Street."
   Who lives where?  Predict: ONE solution, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_1:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r \<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>n\<^bold>o\<^bold>r \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 2 — The compliments
     Nilda:  "Carla lives on Truthtellers Road."
     Carla:  "Nilda lives on Truthtellers Road."
   How sweet. But can we tell where they live?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_2:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 3 — The confession
     Nilda:  "Carla lives on Liars Street."
     Carla:  "I live on Liars Street."
   Wait — can Carla even SAY that?  Predict: ONE, MANY, or NONE?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_3:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 4 — Your turn!
     Edit the two "says" lines below and invent your own riddle.
     Can you build one with exactly one solution? One with none?
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_4_make_your_own:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops



text\<open>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   DEMO 5 — The impossible sentence
     In this town, NOBODY can ever say "I am a liar" — not the liars, not the
     truthtellers. This time it is not a puzzle but a THEOREM, and the prover
     finds the argument on its own (try sledgehammer!). Nitpick agrees:
     uncomment it and it finds no world at all.
   \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<close>
lemma DEMO_5_the_impossible_sentence:
  assumes "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a)"
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
    "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows 
    "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"
  using assms(1) assms(2) assms(3) by auto

lemma BONUS_knows_too_much:
  assumes 
    "It_holds_that_One_plus_One_Equals_Two" 
    "It_holds_that_Fermats_last_Theorem_is_True" 
    "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows 
    "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"
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
