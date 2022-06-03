theory Scratch
  imports Main
  abbrevs nec = \<open>\<box>\<close>
begin

typedecl i

(* declare[[show_types]] *)

lemma "(x::nat) < 4 \<Longrightarrow> x < 5"
  by linarith


(* some comment *)

typ i
typ bool

term "x::bool"
term "x::i"

term "p \<longrightarrow> p"
term "p \<longrightarrow> p"

thm impI

lemma "p \<longrightarrow> p"
proof -
  {
    assume 0: p
    have p using 0 by simp
  }
  thus "p \<longrightarrow> p"
    by (rule impI)
qed

lemma aux: \<open>\<forall> x . P x \<longrightarrow> P x\<close>
proof
  fix x 
  show "P x \<longrightarrow> P x"
    by simp
qed

consts daniel :: i

lemma "F daniel \<longleftrightarrow> F daniel"
  by simp


definition LeibnizEquality :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "\<doteq>" 900)
  where "x \<doteq> y \<equiv> \<forall> F . F x \<longrightarrow> F y"

thm LeibnizEquality_def

definition LeibnizEquality2 :: "i \<Rightarrow> i \<Rightarrow> bool"
  where "LeibnizEquality2 \<equiv> \<lambda> x y . \<forall> F . F x \<longleftrightarrow> F y"

lemma \<open>(\<doteq>) = LeibnizEquality2\<close>
proof
  fix x
  show "(\<doteq>) x = LeibnizEquality2 x"
  proof
    fix y
    show "x \<doteq> y = LeibnizEquality2 x y"
    proof
      assume "LeibnizEquality x y"
      hence 1: "\<forall> F . F x \<longrightarrow> F y"
        by (simp add: LeibnizEquality_def)
      hence \<open>\<forall> F . F x \<longleftrightarrow> F y\<close>
        by (metis LeibnizEquality2_def)
      then show "LeibnizEquality2 x y"
        unfolding LeibnizEquality2_def by auto

    next
      assume "LeibnizEquality2 x y"
      hence \<open>\<forall> F . F x \<longleftrightarrow> F y\<close>
        by (simp add: LeibnizEquality2_def)
      have "\<forall> F . F x \<longrightarrow> F y"
         by (simp add: \<open>\<forall>F. F x = F y\<close>)
      thus "LeibnizEquality x y"
        by (simp add: LeibnizEquality_def)
    qed
  qed
qed



typedecl w \<comment> \<open>type for possible worlds\<close>

consts w\<^sub>0 :: w \<comment> \<open>designated actual world\<close>
(* for w\<^sub>0 : type w \sub 0 *)

type_synonym \<o> = \<open>w \<Rightarrow> bool\<close>
(* for \<o> : type \<o> *)


definition valid :: \<open>\<o> \<Rightarrow> bool\<close> ("[\<Turnstile> _]") where
  \<open>valid \<equiv> \<lambda> p . p w\<^sub>0\<close>
(* sometimes people also define validity as
  \<open>valid \<equiv> \<lambda> p . \<forall> v . p v\<close> instead *)

definition valid_in :: \<open>w \<Rightarrow> \<o> \<Rightarrow> bool\<close> ("[_ \<Turnstile> _]") where
  \<open>valid_in w p \<equiv> p w\<close>

(*
   For bold syntax use \<^bold>. But be careful, it can be confusing:
   \<^bold> acts as an invisibile marker that results in the following
   symbol to become bold. If you want to delete the bold symbol e.g. via
   backspace be sure to delete the invisible \<^bold> symbol as well.
*)

definition mimp :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<rightarrow>\<close> 25) where
  \<open>(p \<^bold>\<rightarrow> q) \<equiv> \<lambda> w . p w \<longrightarrow> q w\<close>

definition mnot :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<not>_\<close> [52] 54) where
  \<open>\<^bold>\<not>p \<equiv> \<lambda> w . \<not>p w\<close>

definition mnec :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [54]55) where
  \<open>\<^bold>\<box>p \<equiv> \<lambda> w . \<forall> v. p v\<close>

(*
   No reachability relation is required for S5.
   If you want one, you can add:
        consts R :: \<open>w \<Rightarrow> w \<Rightarrow> bool\<close>
   and replace the last definition with
        definition mnec :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [54]55) where
            \<open>\<^bold>\<box>p \<equiv> \<lambda> w . \<forall> v. R w v \<longrightarrow> p v\<close>

   You can axiomatize it e.g. via:
       axiomatization
          where R_refl: \<open>\<forall> x y . R x y \<longleftrightarrow> R y x\<close>

   You can confirm the consistency of your axiomatization using
       lemma \<open>True\<close>
          nitpick[satisfy, user_axioms, show_consts, expect = genuine]
          (* Place your cursor here and look at the proof state window for a model! *)
          oops

   Alternatively, you can use also use *specify* some properties of constants,
   which is guaranteed to be consistent, since it requires you to provide an explicit witness:

      consts R :: \<open>w \<Rightarrow> w \<Rightarrow> bool\<close>
      
      specification (R)
        R_refl: \<open>\<forall> x y . R x y \<longleftrightarrow> R y x\<close>
        (* The proof goal here is to provide a witness for all the specified properties of R. *)
      proof -
        (* Current goal is \<exists>R . \<forall> x y . R x y = R y x - we use the universally true relation
           as witness. *)
        have \<open>\<forall> x y . (\<lambda> x y . True) x y = (\<lambda> x y . True) y x\<close>
          by auto
        thus \<open>\<exists>R . \<forall> x y . R x y = R y x\<close>
          by auto
      qed
      (* Now R has the proper R_refl - however models can still choose
         any arbitrary relation for R as long as it also satisfies R_refl, i.e.
         R has not *become* the witness, but the witness is only required to
         ensure consistency, i.e. that there *is* a model for the specified
         property. *)
 *)


lemma \<open>[\<Turnstile> \<^bold>\<box>p \<^bold>\<rightarrow> p]\<close>
  by (simp add: mimp_def mnec_def valid_def)

definition mpos (\<open>\<^bold>\<diamond>_\<close> [54]55) where
  \<open>\<^bold>\<diamond>p \<equiv> \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>p\<close>


lemma \<open>[\<Turnstile> \<^bold>\<box>p \<^bold>\<rightarrow> p]\<close>
  by (simp add: mimp_def mnec_def valid_def)

lemma \<open>[\<Turnstile> \<^bold>\<diamond>p \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>p]\<close>
  using mimp_def mnec_def mnot_def mpos_def valid_def by presburger

lemma \<open>[\<Turnstile> \<^bold>\<box>\<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>p]\<close>
  by (simp add: mimp_def mnec_def valid_def)

lemma \<open>[\<Turnstile> \<^bold>\<box>(p \<^bold>\<rightarrow> q) \<^bold>\<rightarrow> (\<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>q)]\<close>
  by (metis mimp_def mnec_def valid_def)

lemma assumes \<open>\<forall>w. [w \<Turnstile> p]\<close>
  shows \<open>[v \<Turnstile> \<^bold>\<box>p]\<close>
  using assms mnec_def valid_in_def by auto


lemma assumes \<open>\<forall>w. [w \<Turnstile> p]\<close>
  shows \<open>[\<Turnstile> \<^bold>\<box>p]\<close>
  by (meson assms mnec_def valid_def valid_in_def)

definition mforall :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 8)
  where \<open>(\<^bold>\<forall> x . p x) \<equiv> \<lambda> w . \<forall> x . p x w \<close>

lemma \<open>[\<Turnstile> (\<^bold>\<forall>x . \<^bold>\<box>p x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x . p x)]\<close>
  by (simp add: mforall_def mimp_def mnec_def valid_def)



end