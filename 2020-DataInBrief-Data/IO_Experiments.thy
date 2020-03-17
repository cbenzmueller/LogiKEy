theory IO_Experiments imports IO_out2_STIT             (*Paul Meder, 2018*)
begin
(* Xin Paper - Example proof theory *)

consts e::e f::e
(* G = (a \<or> b, [a1 cstit e]) *)
(* [a1 cstit (e \<or> f)] \<in> out1(G, {a2 cstit b } *)
lemma "out1 (\<lambda>X. X=(a \<^bold>\<or> b, (a1 cstit e))) (a2 cstit b) (a1 cstit (e \<^bold>\<or> f))" nitpick[user_axioms,show_all] oops

(* [a1 cstit (e \<or> f)] \<in> out2(G, {a2 cstit b } *)
(* [a1 cstit (e \<or> f)] \<in> Cn(G(L))  *)
(* old version - times out *)
lemma " out2 (\<lambda>X. X=(a \<^bold>\<or> b, (a1 cstit e))) (a1 cstit (e \<^bold>\<or> f)) " oops
(* new version - finds proof *)
lemma "\<lfloor>(a1 cstit e)\<^bold>\<supset>(a1 cstit (e \<^bold>\<or> f)) \<rfloor>" 
  using kcstit_def kimp_def kor_def kvalid_def by auto

(* Modal logic part *)
lemma "\<lfloor> (((a \<^bold>\<or> b) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a2 cstit b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (e \<^bold>\<or> f)) \<rfloor>" 
  by (simp add: ax_refl_a2 k45box_def kand_def kcstit_def kimp_def kor_def kvalid_def)

(* together *)

lemma "\<lfloor> (((a \<^bold>\<or> b) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a2 cstit b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (e \<^bold>\<or> f)) \<rfloor> \<and>
       \<lfloor>(a1 cstit e)\<^bold>\<supset>(a1 cstit (e \<^bold>\<or> f)) \<rfloor> " unfolding Defs 
  using ax_refl_a2 by blast

(* Xin Paper - Ross Paradox *)
(* We have that [a1 dstit (e \<or> f)] not in out2({(\<top>, [a1 dstit e])}, {\<top>}) *)
lemma "out1 (\<lambda>X. X=(\<^bold>\<top>, (a1 dstit e))) \<^bold>\<top>  (a1 dstit (e \<^bold>\<or> f))" nitpick[user_axioms,show_all] oops
(* We have that [a1 dstit (e \<or> f)] not in out2({(\<top>, [a1 dstit e])}, {\<top>}) *)
lemma "\<lfloor> (\<^bold>\<top> \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 dstit e)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 dstit (e \<^bold>\<or> f))  \<rfloor>"
  nitpick[user_axioms,show_all] oops

(* With Chellas's STIT, the paradax is not solved *)
lemma "out1 (\<lambda>X. X=(\<^bold>\<top>, (a1 cstit e))) \<^bold>\<top>  (a1 cstit (e \<^bold>\<or> f))" nitpick[user_axioms,show_all] oops
lemma "\<lfloor> (\<^bold>\<top> \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (e \<^bold>\<or> f))  \<rfloor> "
  by (simp add: k45box_def kcstit_def kimp_def kor_def ktrue_def kvalid_def)


(* out2 *)
(* G = {(a,[a1 cstit e]), (a,[a2 cstit f]),(b,e \<and> f)} *)
(* [a1 cstit e] \<in> out2(G,a) *)
lemma  "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit f))\<^bold>\<and>(b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit (e)) \<rfloor> \<and>
       \<lfloor>((a1 cstit e) \<^bold>\<and> (a1 cstit f) \<^bold>\<and> (e \<^bold>\<and> f))\<^bold>\<supset>(a1 cstit (e)) \<rfloor> "  unfolding Defs by simp
(*  e \<in> out2(G,a) *)
lemma  "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit f))\<^bold>\<and>(b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e) \<rfloor> \<and>
       \<lfloor>((a1 cstit e) \<^bold>\<and> (a1 cstit f) \<^bold>\<and> (e \<^bold>\<and> f))\<^bold>\<supset>e \<rfloor> "  unfolding Defs 
  by (simp add: ax_refl_a1)
(*  (e\<and>f) \<in> out2(G,a) *)
lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit f)) \<^bold>\<and>(b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)) \<^bold>\<and> (a)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)\<rfloor> \<and>
       \<lfloor>((a1 cstit e) \<^bold>\<and> (a1 cstit f) \<^bold>\<and> (e \<^bold>\<and> f))\<^bold>\<supset>(e\<^bold>\<and>f)\<rfloor>" unfolding Defs
  by (simp add: ax_refl_a1) 

lemma "\<lfloor> ((a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit e)) \<^bold>\<and> (a \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit f)) \<^bold>\<and>(b \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)) \<^bold>\<and> (a1 cstit b)) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(e\<^bold>\<and>f)\<rfloor> \<and>
       \<lfloor>((a1 cstit e) \<^bold>\<and> (a1 cstit f) \<^bold>\<and> (e \<^bold>\<and> f))\<^bold>\<supset>(e\<^bold>\<and>f)\<rfloor>" 
  using ax_refl_a1 kand_def kcstit_def kimp_def kvalid_def by auto

(* Moral Luck example *)
consts Drunk::e Drive::e DriveCarefully::e Jump::e Kill::e Hurt::e Stay::e
(* \<diamond>(a1 cstit DriveCarefully) \<in> out2(N,A) *)
lemma "\<lfloor> ((\<^bold>\<top> \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<not>Kill \<^bold>\<and> \<^bold>\<not>Hurt)) \<^bold>\<and> (\<^bold>\<top>  \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box>DriveCarefully))
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit Stay)) 
           \<^bold>\<and> (Drunk \<^bold>\<and> (a1 cstit Drive) \<^bold>\<and> (Jump) \<^bold>\<and> (Drunk \<^bold>\<supset>\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully)
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<and> Jump \<^bold>\<and> (a1 cstit Drive)\<^bold>\<supset>(Kill \<^bold>\<or> Hurt)))
          )) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<diamond>(a1 cstit DriveCarefully))\<rfloor>  " 
  by (smt axC1_a1 ax_refl_rbox k45box_def kand_def kbox_def
      kcstit_def kdia_def kimp_def knot_def ktrue_def kvalid_def)
(*(a1 cstit Stay) \<in> out2(N,A) *)
lemma "\<lfloor> ((\<^bold>\<top> \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<not>Kill \<^bold>\<and> \<^bold>\<not>Hurt)) \<^bold>\<and> (\<^bold>\<top>  \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box>DriveCarefully))
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit Stay)) 
           \<^bold>\<and> (Drunk \<^bold>\<and> (a1 cstit Drive) \<^bold>\<and> (Jump) \<^bold>\<and> (Drunk \<^bold>\<supset>\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully)
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<and> Jump \<^bold>\<and> (a1 cstit Drive)\<^bold>\<supset>(Kill \<^bold>\<or> Hurt)))
         )) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit Stay)\<rfloor>"
  by (simp add: kand_def kimp_def kvalid_def)
(*(\<not>Kill \<^bold>\<and> \<^bold>\<not>Hurt) \<in> out2(N,A) *)
lemma "\<lfloor> ((\<^bold>\<top> \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<not>Kill \<^bold>\<and> \<^bold>\<not>Hurt)) \<^bold>\<and> (\<^bold>\<top>  \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<box>DriveCarefully))
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(a1 cstit Stay)) 
           \<^bold>\<and> (Drunk \<^bold>\<and> (a1 cstit Drive) \<^bold>\<and> (Jump) \<^bold>\<and> (Drunk \<^bold>\<supset>\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully)
           \<^bold>\<and> (\<^bold>\<not>\<^bold>\<diamond>(a1 cstit DriveCarefully) \<^bold>\<and> Jump \<^bold>\<and> (a1 cstit Drive)\<^bold>\<supset>(Kill \<^bold>\<or> Hurt)))
         )) \<^bold>\<supset> \<^bold>\<box>\<^sub>l(\<^bold>\<not>Kill \<^bold>\<and> \<^bold>\<not>Hurt)\<rfloor>" 
  by (simp add: kand_def kimp_def ktrue_def kvalid_def)
end