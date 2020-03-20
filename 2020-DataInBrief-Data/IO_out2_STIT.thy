theory IO_out2_STIT imports Main                (*Paul Meder, 2018*)
begin
  typedecl i (* "type for possible worlds" *)
  type_synonym e = "(i\<Rightarrow>bool)"

  consts a1::"i \<Rightarrow> i \<Rightarrow> bool" a2::"i \<Rightarrow> i \<Rightarrow> bool"   (* Relation for agents: a1 & a2 *)
  consts r_box :: "i\<Rightarrow>i\<Rightarrow>bool"  (infixr "rbox" 70)  (* Relation R_Box *)
  consts r_agt :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "ragt" 70)  (* Relation R_Agt *)
  consts r_G :: "i\<Rightarrow>i\<Rightarrow>bool"    (infixr "rG" 70 )  (* Relation R_G *)
  consts r_H :: "i\<Rightarrow>i\<Rightarrow>bool"    (infixr "rH" 70 )   (* Relation R_H *)
  consts r_45 :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r45" 70)   (* relation for a modal logic K45 *)
  consts aw :: i   (*actual world *)

  definition knot :: "e\<Rightarrow>e" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w) " (* Negation *)
  definition kor :: "e\<Rightarrow>e\<Rightarrow>e" (infixr "\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"  (* Disjunction *)
  definition kand :: "e\<Rightarrow>e\<Rightarrow>e" (infixr "\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)" (* Conjunction *)
  definition kimp :: "e\<Rightarrow>e\<Rightarrow>e" (infixr "\<^bold>\<supset>" 49) where "\<phi>\<^bold>\<supset>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)" (* Implication *)
 
  definition k45box :: "e\<Rightarrow>e" ("\<^bold>\<box>\<^sub>l") where " \<^bold>\<box>\<^sub>l \<phi> \<equiv> \<lambda>w. \<forall>v. w r45 v \<longrightarrow> \<phi>(v)" (*\<box> for Modal logic K45*)
  definition k45dia :: "e\<Rightarrow>e" ("\<^bold>\<diamond>\<^sub>l") where "\<^bold>\<diamond>\<^sub>l \<phi> \<equiv> \<^bold>\<not> \<^bold>\<box>\<^sub>l( \<^bold>\<not> \<phi>) " (* Dual operator for \<box> *)

  definition kbox :: "e\<Rightarrow>e" ("\<^bold>\<box>") where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. w rbox v \<longrightarrow> \<phi>(v)" (* \<box> for T-STIT logic*)
  definition kdia :: "e\<Rightarrow>e" ("\<^bold>\<diamond>") where "\<^bold>\<diamond> \<phi> \<equiv> \<^bold>\<not> \<^bold>\<box>( \<^bold>\<not> \<phi>) " (* Dual *)
  definition kcstit :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>e\<Rightarrow>e" ("_ cstit _") where "r cstit \<phi> \<equiv> \<lambda>w. \<forall>v. r w v \<longrightarrow> \<phi>(v) " (* STIT [i]  *)
  definition kgstit :: "e\<Rightarrow>e" ("gstit _") where "gstit \<phi> \<equiv> \<lambda>w. \<forall>v. w ragt v \<longrightarrow> \<phi>(v)" (*Group STIT [Agt]*)

  definition kvalid :: "e\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8]109) where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p(w)" (* Validity *)
  definition actual :: "e \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) where "\<lfloor>\<phi>\<rfloor>\<^sub>l \<equiv> \<phi>(aw)" (* Validity for actual world *)


  definition ktrue  :: "e" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" (* Tautology *)
  definition kfalse :: "e" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"  (* Falsum *)

  definition kfuture :: "e\<Rightarrow>e" ("F _") where "F \<phi> \<equiv> \<lambda>w. \<forall>v. w rG v \<longrightarrow> \<phi>(v)"
  definition kpast :: "e\<Rightarrow>e" ("H _") where "H \<phi> \<equiv> \<lambda>w. \<forall>v. w rH v \<longrightarrow> \<phi>(v)"
 (* P - dual of the past tense operator H
    P\<phi> stands for '\<phi> has been true at some point in the past ' *)
  definition kpastpoint :: "e\<Rightarrow>e" ("P _")
    where "P \<phi> \<equiv> \<^bold>\<not> H \<^bold>\<not> \<phi>"
  definition kdstit :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>e\<Rightarrow>e" ("_ dstit _") where "r dstit \<phi> \<equiv> (r cstit \<phi>)  \<^bold>\<and> \<^bold>\<not> \<^bold>\<box> \<phi>"

  definition union_set :: "(e\<Rightarrow>bool)\<Rightarrow>(e\<Rightarrow>bool)\<Rightarrow>(e\<Rightarrow>bool)"  ("_ \<^bold>\<union> _")
  where "A \<^bold>\<union> B \<equiv> \<lambda>w. (A w) \<or> (B w)"

  named_theorems Defs
  declare knot_def[Defs] kor_def[Defs] kand_def[Defs] kimp_def[Defs] kvalid_def[Defs]
          kbox_def[Defs] kdia_def[Defs] kcstit_def[Defs] kdstit_def[Defs] kgstit_def[Defs] 
          kfuture_def[Defs] kpast_def[Defs] kpastpoint_def[Defs] ktrue_def[Defs] kfalse_def[Defs]
             union_set_def[Defs] 
          k45box_def[Defs] k45dia_def[Defs]

 (* Subset for relations *)
 abbreviation subset_rel :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>bool"  ("_ \<^bold>\<subseteq> _")
   where "r1 \<^bold>\<subseteq> r2 \<equiv> \<forall>w. \<forall>v. (r1 w v) \<longrightarrow> (r2 w v) "
 (* Composition of 2 relations *)
 abbreviation comp_rel :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)"  ("_ \<^bold>\<circ> _")
   where "r1 \<^bold>\<circ> r2 \<equiv> \<lambda>w. \<lambda>v. \<exists>u.( (r1 w u) \<and> (r2 u v))"
 (* Intersection between 2 relations *)
 abbreviation intersection_rel :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)"  ("_ \<^bold>\<inter> _")
  where "r1 \<^bold>\<inter> r2 \<equiv> \<lambda>w. \<lambda>v. (r1 w v) \<and> (r2 w v)"
 (* Reflexive relation *)
 abbreviation reflexive 
   where "reflexive r \<equiv> (\<forall>x. r x x)"
 (* Symmetric relation *)
 abbreviation symmetric 
   where "symmetric r \<equiv> (\<forall>x y. r x y \<longrightarrow> r y x)"
 (* Transitive relation *)
 abbreviation transitive 
   where "transitive r \<equiv> (\<forall>x y z. ((r x y) \<and> (r y z) \<longrightarrow> (r x z)))"
 (* Serial relation *)
 abbreviation serial 
   where "serial r \<equiv> (\<forall>w. \<exists>v. r w v)"
 (* Inverse relation *)
 abbreviation inverse :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>bool"
  where "inverse r s \<equiv> \<forall>w. \<forall>v. (r w v) \<longleftrightarrow> (s v w)"
 abbreviation euclidean
   where "euclidean rel \<equiv> (\<forall>x y z. ((rel x y) \<and> (rel x z) \<longrightarrow> (rel y z)))"


 (* Abbrevations for conditions on the relations *)
 abbreviation axC1
   where "axC1 r \<equiv> r \<^bold>\<subseteq> r_box"
 abbreviation axC2 :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>bool" 
   where "axC2 r s \<equiv> ( \<forall>w. \<forall>v. ((w rbox w) \<and> (v rbox v) 
                                  \<and> (w rbox v) \<and> (v rbox w))
                         \<longrightarrow> (\<exists>x. r w x \<and> s v x))"
 abbreviation axC3 :: "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>bool"
   where "axC3 r s \<equiv> (\<forall>w.\<forall>v. (w ragt v) = (r w v \<and> s w v))" 

axiomatization where
  (* r45 fulfills transitivity and euclideaness *)
 (* ax_reflex_r45 : "reflexive r_45" *)
  ax_trans_r45 : "transitive r_45" and
  ax_euclidean_r45 : "euclidean r_45" 

lemma  "\<lfloor> ( \<^bold>\<box>\<^sub>l\<phi>)  \<^bold>\<supset> ( \<^bold>\<box>\<^sub>l ( \<^bold>\<box>\<^sub>l \<phi>))\<rfloor>" 
  by (smt ax_trans_r45 k45box_def kimp_def kvalid_def)

lemma  "\<lfloor> (\<^bold>\<diamond>\<^sub>l\<phi>)  \<^bold>\<supset> ( \<^bold>\<box>\<^sub>l(\<^bold>\<diamond>\<^sub>l \<phi>))\<rfloor>"
  by (smt ax_euclidean_r45 k45box_def k45dia_def kimp_def knot_def kvalid_def)

axiomatization where
  (* rbox is an equivalence relation between the worlds in W *)
  ax_refl_rbox: "reflexive r_box" and
  ax_sym_rbox : "symmetric r_box" and
  ax_trans_rbox : "transitive r_box" and

  (* ragt is an equivalence relation between the worlds in W *)
  ax_refl_ragt: "reflexive r_agt" and
  ax_sym_ragt: "symmetric r_agt" and
  ax_trans_ragt: "transitive r_agt" and

  (* every r is an equivalence relation between the worlds in W *)
  ax_refl_a1:  "reflexive a1" and
  ax_sym_a1: "symmetric a1" and
  ax_trans_a1:  "transitive a1" and

  ax_refl_a2:  "reflexive a2" and
  ax_sym_a2: "symmetric a2" and
  ax_trans_a2:  "transitive a2" and

  (*  rG and rH are binary relations between worlds in W  such that 
    rG is serial and transitive, 
    rH is the inverse relation of rG *)
 (* ax_ser_rG: "serial r_G" and *)
  ax_trans_rG: "transitive r_G" and
  ax_inverse_rG_rH: "inverse r_G r_H" 
lemma ax_1: "\<exists>w. w=w" by simp (* W is a nonempty set of possible worlds *)

axiomatization where
  axC1_a1: "axC1 a1" 

axiomatization where
  axC1_a2: "axC1 a2" 

axiomatization where
  axC2_a1_a2 : "axC2 a1 a2 " 

axiomatization where
  axC3_a1_a2 : "axC3 a1 a2 "

lemma True nitpick [satisfy,user_axioms,show_all] oops

axiomatization where
  ax_C4 : "\<forall>w. \<forall>v. \<forall>u. ((w rG u) \<and> (w rG v))
           \<longrightarrow> ((u rG v) \<or> (v rG u) \<or> (u=v))" 

lemma True nitpick [satisfy,user_axioms,show_all] oops

axiomatization where
  ax_C5 : "\<forall>w. \<forall>v. \<forall>u. ((w rH u) \<and> (w rH v))
           \<longrightarrow> ((u rH v) \<or> (v rH u) \<or> (u=v))" 

lemma True nitpick [satisfy,user_axioms,show_all] oops

axiomatization where
  ax_C6 : "(r_G \<^bold>\<circ> r_box) \<^bold>\<subseteq> (r_agt \<^bold>\<circ> r_G)" 

axiomatization where
  ax_C7 : "\<forall>w.\<forall>v. (w rbox v) \<longrightarrow> \<not> (w rG v)" 

lemma True nitpick [satisfy,user_axioms,show_all] oops

(* Some Test *)

consts a::e b::e x::e y::e
(* K = {(a, [a1 cstit x])}, A = {a} *)
(* [a1 cstit x] \<in> out2(K,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>" 
  by (simp add: kand_def kimp_def kvalid_def)

(* WO rule of I/O STIT logic with out2 *)
(*  x \<in> out2(K,A) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (x) \<rfloor>" 
  using ax_refl_a1 k45box_def kand_def kcstit_def kimp_def kvalid_def by auto 
(* \<^bold>\<diamond>[a1 cstit x] \<in> out2(K,A) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<diamond>(a1 cstit x)) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (\<^bold>\<diamond>(a1 cstit x)) \<rfloor>"
   using ax_refl_rbox k45box_def kand_def kbox_def kdia_def kimp_def knot_def kvalid_def by auto
(* [a1 cstit (x\<or>y)] \<in> out2(K,A) *)
lemma "\<lfloor>((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x)))\<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x\<^bold>\<or>y)) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit (x\<^bold>\<or>y))\<rfloor>" 
  by (simp add: k45box_def kand_def kcstit_def kimp_def kor_def kvalid_def)

(* SI rule for I/O STIT with out2 *)
(* [a1 cstit x] \<in> out2(K,{a\<and>b}) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a \<^bold>\<and> b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>" 
  by (simp add: kand_def kimp_def kvalid_def)

definition "G \<equiv> (\<lambda>X. X=(a, (a1 cstit x)))" declare G_def[Defs]
definition "A \<equiv>(\<lambda>X. X=a)" declare A_def[Defs]
definition "G_Box \<equiv> \<lambda>x. \<exists>y z. ( (x=(y \<^bold>\<supset> \<^bold>\<box>\<^sub>lz)) \<and> G(y,z)) " declare G_Box_def[Defs]

lemma "G_Box(a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x))" 
  by (simp add: G_Box_def G_def)  

lemma "(G_Box \<^bold>\<union> A)(a)" 
  by (simp add: A_def union_set_def)

(*lemma "G_L G (a1 cstit x)"
  by (simp add: G_L_def G_def)*)

(* Sledgehammer times out / Nitpick no counter model *)
lemma "out2 G (a1 cstit x)" 
  nitpick[user_axioms,show_all] oops

lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor>"
  by (simp add: kand_def kimp_def kvalid_def)
consts z::e

(* K = {(a, [a1 cstit x])} A = {a} *)
definition "K \<equiv> (\<lambda>X. X= (a, (a1 cstit x))) " declare K_def[Defs] 
(* WO rule of I/O STIT logic with out1 *)
(*out1 *)
(* [a1 cstit x] \<in> out1(K,a)  - timeout*)
lemma "out1 K a (a1 cstit x)"   nitpick[user_axioms,show_all] oops
(*  x \<in> out1(K,a)  - timeout*)
lemma "out1 K a x" nitpick[user_axioms,show_all] oops 
(* \<^bold>\<diamond>[a1 cstit x] \<in> out1(K,a)  - timeout*)
lemma "out1 K a (\<^bold>\<diamond>(a1 cstit x))"  nitpick[user_axioms,show_all] oops 
(* [a1 cstit (x\<or>y)] \<in> out1(K,a)  - timeout*)
lemma "out1 K a (a1 cstit (x\<^bold>\<or>y))" nitpick[user_axioms,show_all] oops 

(* SI rule for I/O STIT with out1 *)
(* [a1 cstit x] \<in> out1(K,{a\<and>b})  - timeout*)
lemma "out1 K (a \<^bold>\<and> b) (a1 cstit x)" nitpick[user_axioms,show_all] oops 

(* M = {(a, [a1 cstit x]), (a, [a1 cstit y])} *)
definition "M \<equiv> (\<lambda>X. X= (a, (a1 cstit x)) \<or> X=(a, (a1 cstit y))) " declare M_def[Defs] 
(* AND rule for I/O STIT  with out1*)
(* [a1 cstit x] \<in> out1(M,a)  - timeout*)
lemma "out1 M a ((a1 cstit x)\<^bold>\<and>(a1 cstit y))"  nitpick[user_axioms,show_all] oops 
(* [a1 cstit (x\<and>y)] \<in> out2(M,a) - timeout  *)
lemma "out1 M a (a1 cstit (x\<^bold>\<and>y))"  nitpick[user_axioms,show_all] oops 

(* OR rule for I/O STIT with out1*)
(* T = {(a, [a1 cstit x]), (b, [a1 cstit x]))} *)
definition "T \<equiv> (\<lambda>X. X= (a, (a1 cstit x)) \<or> X= (b, (a1 cstit x)))" declare T_def[Defs]

(* [a1 cstit x] \<in> out1(T,{a \<or> b})? No, countermodel*)
lemma "out1 T (a \<^bold>\<or> b) (a1 cstit x)"  nitpick[user_axioms,show_all] oops


(* K = {(a, [a1 cstit x])}, A = {a} *)
(* [a1 cstit x] \<in> out2(K,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>" 
  by (simp add: kand_def kimp_def kvalid_def)

(* WO rule of I/O STIT logic with out2 *)
(*  x \<in> out2(K,A) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (x) \<rfloor>" 
  using ax_refl_a1 k45box_def kand_def kcstit_def kimp_def kvalid_def by auto 
(* \<^bold>\<diamond>[a1 cstit x] \<in> out2(K,A) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<diamond>(a1 cstit x)) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (\<^bold>\<diamond>(a1 cstit x)) \<rfloor>"
   using ax_refl_rbox k45box_def kand_def kbox_def kdia_def kimp_def knot_def kvalid_def by auto
(* [a1 cstit (x\<or>y)] \<in> out2(K,A) *)
lemma "\<lfloor>((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x)))\<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x\<^bold>\<or>y)) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit (x\<^bold>\<or>y))\<rfloor>" 
  by (simp add: k45box_def kand_def kcstit_def kimp_def kor_def kvalid_def)

(* SI rule for I/O STIT with out2 *)
(* [a1 cstit x] \<in> out2(K,{a\<and>b}) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a \<^bold>\<and> b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor> \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>" 
  by (simp add: kand_def kimp_def kvalid_def)

(* AND rule for I/O STIT with out2 *)
(* M = {(a, [a1 cstit x]), (a, [a1 cstit y])} *)
(* ([a1 cstit (x)] \<and> [a1 cstit (y)]) \<in> out2(M,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x))) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (y))) \<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l((a1 cstit x)\<^bold>\<and>(a1 cstit y)) \<rfloor>
         \<and> \<lfloor>((a1 cstit x)\<^bold>\<and>(a1 cstit y)) \<^bold>\<supset> ((a1 cstit x)\<^bold>\<and>(a1 cstit y)) \<rfloor>"
  by (simp add: k45box_def kand_def kimp_def kvalid_def)
(* [a1 cstit (x\<and>y)] \<in> out2(M,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x))) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (y))) \<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x\<^bold>\<and>y)) \<rfloor>
         \<and> \<lfloor>((a1 cstit x)\<^bold>\<and>(a1 cstit y)) \<^bold>\<supset> (a1 cstit (x\<^bold>\<and>y)) \<rfloor>"
  by (simp add: k45box_def kand_def kcstit_def kimp_def kvalid_def)

(* OR rule for the I/O STIT with out2 *)
(* T = {(a, [a1 cstit x]), (b, [a1 cstit x]))} *)
(* [a1 cstit x] \<in> out2(T,{a \<or> b}) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a \<^bold>\<or> b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor>
       \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>"
  using kand_def kimp_def kor_def kvalid_def by auto

(* ID
(*out1 *)
(* [a1 cstit x] \<in> out1(T,[a1 cstit x])? No, countermodel*)
lemma "out1 T (a1 cstit x) (a1 cstit x)"  nitpick[user_axioms,show_all] oops *)
(*out2 *)
(* [a1 cstit x] not \<in> out2(T,{[a1 cstit x]} *)
lemma  "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (a1 cstit x)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x) \<rfloor>
       \<and> \<lfloor>(a1 cstit x)\<^bold>\<supset> (a1 cstit x) \<rfloor>"   nitpick[user_axioms,show_all] oops
(* Cumulative Transitivity *)
definition "T1 \<equiv> (\<lambda>X. X= (a1 cstit a, a1 cstit x) \<or> X = ((a1 cstit a) \<^bold>\<and> (a1 cstit x),a1 cstit y))"
(*out1 *)
(* [a1 cstit y] \<in> out1(T1, [a1 cstit a])? No, countermodel*)
lemma "out1 T1 (a1 cstit a) (a1 cstit y)"  nitpick[user_axioms,show_all] oops
(*out2 *)
(* [a1 cstit y] \<in> out2(T1, [a1 cstit a]) *)
lemma "\<lfloor> (( (a1 cstit a ) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit x)) \<^bold>\<and> (((a1 cstit a) \<^bold>\<and> (a1 cstit x)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit y))
           \<^bold>\<and> (a1 cstit a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit y) \<rfloor>
       \<and> \<lfloor>((a1 cstit x) \<^bold>\<and> (a1 cstit y))\<^bold>\<supset> (a1 cstit y) \<rfloor>"  nitpick[user_axioms,show_all] oops

definition "T2 \<equiv> (\<lambda>X. X= (a1 cstit x, a1 cstit y) \<or> X = ((a1 cstit y),a1 cstit z))"
(*out1 *)
(* [a1 cstit z] \<in> out1(TT, [a1 cstit x])? No, countermodel*)
lemma "out1 T2 (a1 cstit x) (a1 cstit z)"  nitpick[user_axioms,show_all] oops
(*out2 *)
(* [a1 cstit z] \<in> out2(T2, [a1 cstit x]) *)
lemma "\<lfloor> (( (a1 cstit x ) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit y)) \<^bold>\<and> ((a1 cstit y) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit z))
           \<^bold>\<and> (a1 cstit x)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit z) \<rfloor>
       \<and> \<lfloor>((a1 cstit y) \<^bold>\<and> (a1 cstit z))\<^bold>\<supset> (a1 cstit z) \<rfloor>"  nitpick[user_axioms,show_all] oops

definition "S \<equiv> (\<lambda>X. X= (a, (a1 cstit x)) \<or> X=(a, (a2 cstit y))) " 
declare S_def[Defs] 
(*out1 *)
(* [gstit (x \<and> y)] \<in> out1(S,a)? Timeout*)
lemma "out1 S (a) (gstit (x \<^bold>\<and> y))" nitpick[user_axioms,show_all] oops
(*out2 *)
(* [gstit (x \<and> y)] \<in> out2(S,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x) )) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a2 cstit (y) )) \<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(gstit (x \<^bold>\<and> y) ) \<rfloor>
         \<and> \<lfloor>((a1 cstit x)\<^bold>\<and>(a2 cstit y)) \<^bold>\<supset> (gstit (x \<^bold>\<and> y)) \<rfloor>"
  by (simp add: axC3_a1_a2 k45box_def kand_def kcstit_def kgstit_def kimp_def kvalid_def) 


definition "W \<equiv> (\<lambda>X. X= (a,gstit z))" declare W_def[Defs]
(*out1 *)
(* [a1 cstit z] \<and> [a2 cstit z] \<in> out1(W,a)? No*)
lemma "out1 W (a) ((a1 cstit z) \<^bold>\<and> (a2 cstit z))" nitpick[user_axioms,show_all] oops
(*out2 *)
(* [a1 cstit z] \<and> [a2 cstit z] \<in> out2(W,a) ? 
  No, we dont have  [gstit z] \<supset> ([a1 cstit z] \<and> [a2 cstit z])   *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(gstit (z)))\<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l((a1 cstit z)\<^bold>\<and>(a2 cstit z)) \<rfloor>
         \<and> \<lfloor>(gstit z) \<^bold>\<supset> ((a1 cstit z) \<^bold>\<and> (a2 cstit z)) \<rfloor>" unfolding Defs nitpick[user_axioms,show_all] oops 

definition "L \<equiv> (\<lambda>X. X= (a, (a1 cstit x)) \<or> X=(a, (a2 cstit x))) " declare L_def[Defs] 
(* [gstit x] \<in> out2(L,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (x) )) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a2 cstit (x) )) \<^bold>\<and>(a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(gstit x) \<rfloor>
         \<and> \<lfloor>((a1 cstit x)\<^bold>\<and>(a2 cstit x)) \<^bold>\<supset> (gstit x) \<rfloor>" 
  by (simp add: axC3_a1_a2 k45box_def kand_def kcstit_def kgstit_def kimp_def kvalid_def)

(* Some test with \<^bold>\<box>\<^sub>l and \<^bold>\<box> *)
definition "R \<equiv> (\<lambda>X. X = (a, \<^bold>\<box>x))" declare R_def[Defs]
(* \<^bold>\<box> x \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) (\<^bold>\<box>x)" nitpick[user_axioms,show_all] oops
(* \<^bold>\<box> x \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)  \<rfloor> \<and> \<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (\<^bold>\<box> x) \<rfloor>"
  by (simp add: kand_def kimp_def kvalid_def)
(* \<diamond>x \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) (\<^bold>\<diamond>x)" nitpick[user_axioms,show_all] oops
(* \<diamond>x \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<diamond> x)  \<rfloor> \<and> \<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (\<^bold>\<diamond> x) \<rfloor>"
  using ax_refl_rbox k45box_def kand_def kbox_def kdia_def kimp_def knot_def kvalid_def by auto
(* x \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) (x)" nitpick[user_axioms,show_all] oops
(* x \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l( x)  \<rfloor> \<and> \<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> ( x) \<rfloor>" 
  by (simp add: ax_refl_rbox k45box_def kand_def kbox_def kimp_def kvalid_def)
(* (x \<^bold>\<or> y) \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) (x \<^bold>\<or> y)" nitpick[user_axioms,show_all] oops
(* (x \<or> y) \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l( x \<^bold>\<or> y)  \<rfloor> \<and> \<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (x \<^bold>\<or> y) \<rfloor>" 
  by (simp add: ax_refl_rbox k45box_def kand_def kbox_def kimp_def kor_def kvalid_def)
(* [a1 cstit x] \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) ( a1 cstit x)" nitpick[user_axioms,show_all] oops
(* [a1 cstit x] \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l( a1 cstit x)  \<rfloor>"
  by (simp add: axC1_a1 k45box_def kand_def kbox_def kcstit_def kimp_def kvalid_def)
lemma "\<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (a1 cstit x) \<rfloor>" 
  by (simp add: axC1_a1 kbox_def kcstit_def kimp_def kvalid_def) 
(* [a2 cstit x] \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) ( a2 cstit x)" nitpick[user_axioms,show_all] oops
(* [a2 cstit x] \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l( a2 cstit x)  \<rfloor>"
  by (simp add: axC1_a2 k45box_def kand_def kbox_def kcstit_def kimp_def kvalid_def)
lemma "\<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (a2 cstit x) \<rfloor>"
  by (simp add: axC1_a2 kbox_def kcstit_def kimp_def kvalid_def)
(* ([a1 cstit x] \<and> [a2 cstit x]) \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) ((a1 cstit x) \<^bold>\<and> (a2 cstit x))" nitpick[user_axioms,show_all] oops
(* ([a1 cstit x] \<and> [a2 cstit x]) \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l((a1 cstit x) \<^bold>\<and> (a2 cstit x))  \<rfloor>"
  by (simp add: axC1_a1 axC1_a2 k45box_def kand_def kbox_def kcstit_def kimp_def kvalid_def)
lemma "\<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> ((a1 cstit x) \<^bold>\<and> (a2 cstit x)) \<rfloor>" 
  by (simp add: axC1_a1 axC1_a2 kand_def kbox_def kcstit_def kimp_def kvalid_def)
(* [gstit x] \<in> out1(R,a) - Timeout *)
lemma "out1 R (a) (gstit x)" nitpick[user_axioms,show_all] oops
(* [gstit x] \<in> out2(R,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box> x)) \<^bold>\<and> (a))\<^bold>\<supset> \<^bold>\<box>\<^sub>l(gstit x)  \<rfloor>"
  by (simp add: axC1_a2 axC3_a1_a2 k45box_def kand_def kbox_def kgstit_def kimp_def kvalid_def)
lemma "\<lfloor> (\<^bold>\<box> x)\<^bold>\<supset> (gstit x) \<rfloor>"
  by (simp add: axC1_a1 axC3_a1_a2 kbox_def kgstit_def kimp_def kvalid_def)
end