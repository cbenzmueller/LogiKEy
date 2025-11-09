
theory FATIO_v1_examples imports FATIO_v1

begin

(* example from the paper: The Brigade Restaurant *)
term "[ assert[a,r\<^sup>a], challenge[b,a,r\<^sup>a], justify[a,n\<^sup>a\<turnstile>\<^sup>+r\<^sup>a], question[c,b,r\<^sup>a], justify[b,m\<^sup>a \<and> s\<^sup>a\<turnstile>\<^sup>-r\<^sup>a], retract[a,r\<^sup>a,+] ]"


lemma 
  "FatioCheckRec (
    [ assert[a,r\<^sup>a], challenge[b,a,r\<^sup>a], justify[a,n\<^sup>a\<turnstile>\<^sup>+r\<^sup>a], question[c,b,r\<^sup>a], justify[b,m\<^sup>a \<and> s\<^sup>a\<turnstile>\<^sup>-r\<^sup>a], retract[a,r\<^sup>a,+] ],
    [],
    {}
    )"
  apply simp
  (* Nitpick found a counterexample *)
  oops


lemma 
  "successfulResult (FatioCheck (
    [assert[a,r\<^sup>a]],
    [],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a})
    )
   ))"
  apply simp
  using Speaker.exhaust global_consequence_def member_rec(2)
  by (smt (verit) Speaker.exhaust global_consequence_def member_rec(2))



lemma 
  "FatioCheckRec (
    [assert[a,r\<^sup>a]],
    [],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a})
    )
   )"
  apply simp
  using Speaker.exhaust global_consequence_def member_rec(2)
  by (smt (verit) Speaker.exhaust global_consequence_def member_rec(2))


(* apply one step *)
lemma 
  "FatioCheck (
    [assert[a,r\<^sup>a]],
    [],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a})
    )
    ) = (
    [],
    [(Entry a (r\<^sup>a) +)],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
    (\<forall>k j. k \<noteq> a \<and> j \<noteq> a \<longrightarrow> x = \<^bold>B\<^sub>k \<^bold>D\<^sub>a \<^bold>B\<^sub>j \<^bold>B\<^sub>a mkHOMMLatom r) \<or> (x = MapDone assert[a,r\<^sup>a])
    ))"
  apply (simp add: member_rec(2))
  by (smt (verit) Speaker.exhaust global_consequence_def)

(*
lemma 
  "FatioCheck (
[assert[a,r\<^sup>a]],
[],
(
\<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a (\<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c (\<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
( x = (\<^bold>D\<^sub>b (\<^bold>B\<^sub>a (\<^bold>D\<^sub>b (\<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a])))))) \<or>
( x = (\<^bold>D\<^sub>b (\<^bold>B\<^sub>c (\<^bold>D\<^sub>b (\<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a])))))) 
)
) = (
[],
[(Entry a (r\<^sup>a) +)],
(
\<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
(\<forall>k j. k \<noteq> a \<and> j \<noteq> a \<longrightarrow> x = \<^bold>B\<^sub>k \<^bold>D\<^sub>a \<^bold>B\<^sub>j \<^bold>B\<^sub>a mkHOMMLatom r) \<or> (x = MapDone assert[a,r\<^sup>a]) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a (\<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c (\<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>D\<^sub>b (\<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a])))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>D\<^sub>b (\<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))))
)
)"
  oops
*)

(* after this, try to apply the next step *)
lemma 
  "successfulResult (FatioCheck (
    [challenge[b,a,r\<^sup>a]],
    [(Entry a (r\<^sup>a) +)],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
    (\<forall>k j. k \<noteq> a \<and> j \<noteq> a \<longrightarrow> x = \<^bold>B\<^sub>k \<^bold>D\<^sub>a \<^bold>B\<^sub>j \<^bold>B\<^sub>a mkHOMMLatom r) \<or> (x = MapDone assert[a,r\<^sup>a]) \<or>
    (\<forall>k. (k\<noteq>b \<longrightarrow> x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>k \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
    (\<forall>k. (k\<noteq>b \<longrightarrow> x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>k \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))))
    )
    ))"
  apply simp
  apply (simp add: member_rec(1))
  (* Nitpick found a counterexample *)
  oops

(* try as above but instead of using quantifiers, listing the agents.. it works! *)
lemma 
  "successfulResult (FatioCheck (
    [challenge[b,a,r\<^sup>a]],
    [(Entry a (r\<^sup>a) +)],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
    (\<forall>k j. k \<noteq> a \<and> j \<noteq> a \<longrightarrow> x = \<^bold>B\<^sub>k \<^bold>D\<^sub>a \<^bold>B\<^sub>j \<^bold>B\<^sub>a mkHOMMLatom r) \<or> (x = MapDone assert[a,r\<^sup>a]) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) 
    )
  ))"
  apply simp
  apply (simp add: member_rec(1))
  by (smt (verit) Speaker.exhaust global_consequence_def)

(* i can also prove it with fatiocheckrec *)
lemma 
  "FatioCheckRec (
    [challenge[b,a,r\<^sup>a]],
    [(Entry a (r\<^sup>a) +)],
    (
    \<lambda>x. (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>b\<^bold>B\<^sub>a  {r\<^sup>a}) \<or> (x = \<^bold>D\<^sub>a\<^bold>B\<^sub>c\<^bold>B\<^sub>a  {r\<^sup>a}) \<or>
    (\<forall>k j. k \<noteq> a \<and> j \<noteq> a \<longrightarrow> x = \<^bold>B\<^sub>k \<^bold>D\<^sub>a \<^bold>B\<^sub>j \<^bold>B\<^sub>a mkHOMMLatom r) \<or> (x = MapDone assert[a,r\<^sup>a]) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) \<or>
    ( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) 
    )
  )"
  apply simp
  apply (simp add: member_rec(1))
  by (smt (verit) Speaker.exhaust global_consequence_def)

(* but then, those 2 formulas were different!?  *)
lemma "(\<lambda>x. (\<forall>k. (k\<noteq>b \<longrightarrow> x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>k \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r)))) \<or>
(\<forall>k. (k\<noteq>b \<longrightarrow> x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>k \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))))) 
=
(\<lambda>x. 
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>\<not>\<^bold>B\<^sub>b (mkHOMMLatom r))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>a \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) \<or>
( x = (\<^bold>D\<^sub>b \<^bold>B\<^sub>c \<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone justify[a,\<Delta>\<turnstile>\<^sup>+r\<^sup>a]))) 
)" 
  nitpick
  oops


(* try only the 2nd step, written differently *)
term "successfulResult (FatioCheck (
[ challenge[b,a,r\<^sup>a] ],
[(Entry a (r\<^sup>a) +)],
(
\<lambda>x. (
    (x= ( ((\<^bold>D\<^sub>b\<^bold>B\<^sub>a (\<^bold>\<not>\<^bold>B\<^sub>b (Map1 (r\<^sup>a)))) \<^bold>\<and> ( \<^bold>D\<^sub>b\<^bold>B\<^sub>a\<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone (justify[a, \<Delta> \<turnstile>\<^sup>+ r\<^sup>a])))  ))) \<or>
    (x= ( ((\<^bold>D\<^sub>b\<^bold>B\<^sub>c (\<^bold>\<not>\<^bold>B\<^sub>b  (Map1 (r\<^sup>a)))) \<^bold>\<and> ( \<^bold>D\<^sub>b\<^bold>B\<^sub>c\<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>.(MapDone (justify[a, \<Delta> \<turnstile>\<^sup>+ r\<^sup>a])))  )))
))
))"

lemma "successfulResult (FatioCheck (
[ challenge[b,a,r\<^sup>a] ],
[(Entry a (r\<^sup>a) +)],
(
\<lambda>x. (
    (x= ( ((\<^bold>D\<^sub>b\<^bold>B\<^sub>a (\<^bold>\<not>\<^bold>B\<^sub>b (Map1 (r\<^sup>a)))) \<^bold>\<and> ( \<^bold>D\<^sub>b\<^bold>B\<^sub>a\<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>. (MapDone (justify[a, \<Delta> \<turnstile>\<^sup>+ r\<^sup>a])))  ))) \<or>
    (x= ( ((\<^bold>D\<^sub>b\<^bold>B\<^sub>c (\<^bold>\<not>\<^bold>B\<^sub>b  (Map1 (r\<^sup>a)))) \<^bold>\<and> ( \<^bold>D\<^sub>b\<^bold>B\<^sub>c\<^bold>D\<^sub>b \<^bold>\<exists>\<Delta>.(MapDone (justify[a, \<Delta> \<turnstile>\<^sup>+ r\<^sup>a])))  )))
))
))"
  apply simp
  apply (simp add: member_rec(1))
  by (smt (verit, del_insts) Speaker.exhaust global_consequence_def mand_def)


end