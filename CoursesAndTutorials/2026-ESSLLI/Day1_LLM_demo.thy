theory Day1_LLM_demo
  imports Main
begin

(* One theorem, many proof styles. *)

(* 1. Fully automatic (try also: by blast, by (metis conjE mp), or run
      sledgehammer to watch external ATPs race for a one-liner). *)
theorem modus_ponens: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B" by presburger

(* 2. Interactive Isar proof, using natural deduction rules only:
      implication introduction, conjunction elimination, modus ponens. *)
theorem mp_Isar: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B"
proof (rule impI)
  assume ab_a: "(A \<longrightarrow> B) \<and> A"
  from ab_a have ab: "A \<longrightarrow> B" by (rule conjunct1)
  from ab_a have a: "A" by (rule conjunct2)
  from ab a show "B" by (rule mp)
qed

(* 3. Apply-style tactic script: backward proof, watch the goal state
      shrink after each step. *)
theorem mp_apply: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B"
  apply (rule impI)
  apply (erule conjE)
  apply (erule mp)
  apply assumption
  done

(* 4. Forward proof by rule composition: theorems are first-class objects,
      composed with OF — no goal state needed for the core argument. *)
theorem mp_forward: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B"
proof (rule impI)
  assume ab_a: "(A \<longrightarrow> B) \<and> A"
  show "B" by (rule mp[OF conjunct1[OF ab_a] conjunct2[OF ab_a]])
qed

(* 5. Classical proof by contradiction (reductio ad absurdum): not needed
      for this intuitionistic theorem, but the pattern to remember. *)
theorem mp_contradiction: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B"
proof (rule impI, rule ccontr)
  assume ab_a: "(A \<longrightarrow> B) \<and> A" and nb: "\<not> B"
  from ab_a have "B" by (blast dest: mp)
  with nb show False by (rule notE)
qed

(* 6. Minimalist Isar: ".." applies the single obvious standard rule —
      the proof almost writes itself. *)
theorem mp_minimal: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B"
proof
  assume ab_a: "(A \<longrightarrow> B) \<and> A"
  from ab_a have ab: "A \<longrightarrow> B" ..
  from ab_a have a: "A" ..
  from ab a show "B" ..
qed

end
