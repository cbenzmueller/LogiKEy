theory Day1_LiarsStreet
  imports Main
begin

(* LIAR'S STREET — a riddle the computer solves by itself.
   Two kids, NILDA and CARLA, each live on LIAR'S STREET (everyone there always lies)
   or TRUTHTELLER'S ROAD (everyone there always tells the truth). From their
   statements alone, click a  nitpick[satisfy]  line: the computer searches every
   possible world and reports ONE answer, MANY, or NONE. *)

nitpick_params [user_axioms, format = 2, show_all]
declare [[show_abbrevs = false]]

(* The world: who is there, and the two places to live. *)
datatype Entity = Nilda ("\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a") | Carla ("\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a")
lemma "\<not>(\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a = \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a)" by simp
datatype Street = LiarsStreet ("\<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t") | TruthtellersRoad ("\<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d")

(* The words: friendly names for ordinary logic, so the sentences read like English. *)
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

(* The rules of the town (delete OneHome for the looser "open world" version). *)
axiomatization where
  A1: "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>l\<^bold>i\<^bold>e\<^bold>s X)"  and
  A2: "\<forall>X. \<^bold>I\<^bold>f (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d) \<^bold>t\<^bold>h\<^bold>e\<^bold>n (\<^bold>s\<^bold>a\<^bold>y\<^bold>s\<^bold>-\<^bold>t\<^bold>h\<^bold>e\<^bold>-\<^bold>t\<^bold>r\<^bold>u\<^bold>t\<^bold>h X)"  and
  OneHome: "\<forall>X. ((X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<or> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d))
                  \<and> \<not> ((X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t) \<and> (X \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d))"

(* DEMO 1 *)
lemma DEMO_1:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>n\<^bold>e\<^bold>i\<^bold>t\<^bold>h\<^bold>e\<^bold>r \<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>n\<^bold>o\<^bold>r \<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

(* DEMO 2 *)
lemma DEMO_2:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

(* DEMO 3 *)
lemma DEMO_3:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops

(* DEMO 4  *)
lemma DEMO_4_make_your_own:
  assumes
   "\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>T\<^bold>r\<^bold>u\<^bold>t\<^bold>h\<^bold>t\<^bold>e\<^bold>l\<^bold>l\<^bold>e\<^bold>r\<^bold>s\<^bold>R\<^bold>o\<^bold>a\<^bold>d)"
   "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s (\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n \<^bold>L\<^bold>i\<^bold>a\<^bold>r\<^bold>s\<^bold>S\<^bold>t\<^bold>r\<^bold>e\<^bold>e\<^bold>t)"
  shows
   "((\<^bold>N\<^bold>i\<^bold>l\<^bold>d\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S1) \<^bold>a\<^bold>n\<^bold>d (\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>l\<^bold>i\<^bold>v\<^bold>e\<^bold>s\<^bold>-\<^bold>i\<^bold>n S2))"
  (* nitpick[satisfy, max_genuine = 4] *) oops



(* BONUS — "says"/"knows" are naive truth-functions here, so saying/knowing one true
   thing forces saying/knowing EVERY true thing — a crude model of knowledge. *)
consts It_holds_that_One_plus_One_Equals_Two::bool
consts It_holds_that_Fermats_last_Theorem_is_True::bool
lemma BONUS_says_too_much:
  assumes "It_holds_that_One_plus_One_Equals_Two" "It_holds_that_Fermats_last_Theorem_is_True" "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>s\<^bold>a\<^bold>y\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"
  using assms(1) assms(2) assms(3) by auto
lemma BONUS_knows_too_much:
  assumes "It_holds_that_One_plus_One_Equals_Two" "It_holds_that_Fermats_last_Theorem_is_True" "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_One_plus_One_Equals_Two"
  shows "\<^bold>C\<^bold>a\<^bold>r\<^bold>l\<^bold>a \<^bold>k\<^bold>n\<^bold>o\<^bold>w\<^bold>s It_holds_that_Fermats_last_Theorem_is_True"
  using assms(1) assms(2) assms(3) by auto

end
