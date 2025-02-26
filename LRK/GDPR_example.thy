\<comment> \<open>GDPR Example\<close>
theory GDPR_example
  imports 
    LRK
begin

consts
pa::\<sigma> pb::\<sigma> pc::\<sigma>
a::i  (* 000 *)  
b::i  (* 001 *)  
c::i  (* 010 *)  
d::i  (* 011 *)  
e::i  (* 100 *)  
f::i  (* 101 *)  
g::i  (* 110 *)  
h::i  (* 111 *)  

abbreviation (input) check_subset::"(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>bool" where
  "check_subset S T \<equiv> (\<forall>x. S x \<longrightarrow> T x)"  

axiomatization where
  a0:"(\<forall>x::i. (x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=g \<or> x=h))"   (* 8 distinct worlds *)
  and
  a00:"(\<forall>x::i. (x=a \<longrightarrow> \<not>(x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=g \<or> x=h)))" and  
  a01:"(\<forall>x::i. (x=b \<longrightarrow> \<not>(x=a \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=g \<or> x=h)))" and  
  a02:"(\<forall>x::i. (x=c \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=d \<or> x=e \<or> x=f \<or> x=g \<or> x=h)))" and  
  a03:"(\<forall>x::i. (x=d \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=c \<or> x=e \<or> x=f \<or> x=g \<or> x=h)))" and  
  a04:"(\<forall>x::i. (x=e \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=f \<or> x=g \<or> x=h)))" and  
  a05:"(\<forall>x::i. (x=f \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=g \<or> x=h)))" and  
  a06:"(\<forall>x::i. (x=g \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=h)))" and  
  a07:"(\<forall>x::i. (x=h \<longrightarrow> \<not>(x=a \<or> x=b \<or> x=c \<or> x=d \<or> x=e \<or> x=f \<or> x=g)))"  
  and
  aa:"\<not>\<lfloor>\<^sup>Apa\<rfloor>\<^sub>a \<and> \<not>\<lfloor>\<^sup>Apb\<rfloor>\<^sub>a \<and> \<not>\<lfloor>\<^sup>Apc\<rfloor>\<^sub>a" and (*000*)
  ab:"\<not>\<lfloor>\<^sup>Apa\<rfloor>\<^sub>b \<and> \<not>\<lfloor>\<^sup>Apb\<rfloor>\<^sub>b \<and> \<lfloor>\<^sup>Apc\<rfloor>\<^sub>b" and (*001*)
  ac:"\<not>\<lfloor>\<^sup>Apa\<rfloor>\<^sub>c \<and> \<lfloor>\<^sup>Apb\<rfloor>\<^sub>c \<and> \<not>\<lfloor>\<^sup>Apc\<rfloor>\<^sub>c" and (*010*)
  ad:"\<not>\<lfloor>\<^sup>Apa\<rfloor>\<^sub>d \<and> \<lfloor>\<^sup>Apb\<rfloor>\<^sub>d \<and> \<lfloor>\<^sup>Apc\<rfloor>\<^sub>d" and (*011*)
  ae:"\<lfloor>\<^sup>Apa\<rfloor>\<^sub>e \<and> \<not>\<lfloor>\<^sup>Apb\<rfloor>\<^sub>e \<and> \<not>\<lfloor>\<^sup>Apc\<rfloor>\<^sub>e" and (*100*)
  af:"\<lfloor>\<^sup>Apa\<rfloor>\<^sub>f \<and> \<not>\<lfloor>\<^sup>Apb\<rfloor>\<^sub>f \<and> \<lfloor>\<^sup>Apc\<rfloor>\<^sub>f" and (*101*)
  ag:"\<lfloor>\<^sup>Apa\<rfloor>\<^sub>g \<and> \<lfloor>\<^sup>Apb\<rfloor>\<^sub>g \<and> \<not>\<lfloor>\<^sup>Apc\<rfloor>\<^sub>g" and (*110*) 
  ah:"\<lfloor>\<^sup>Apa\<rfloor>\<^sub>h \<and> \<lfloor>\<^sup>Apb\<rfloor>\<^sub>h \<and> \<lfloor>\<^sup>Apc\<rfloor>\<^sub>h"  and (*111*)
  til1:"a \<^bold>\<sim> b" and  
  til2:"b \<^bold>\<sim> c" and  
  til3:"c \<^bold>\<sim> d" and  
  til4:"d \<^bold>\<sim> e" and  
  til5:"e \<^bold>\<sim> f" and  
  til6:"f \<^bold>\<sim> g" and  
  til7:"g \<^bold>\<sim> h" and  
  til8:"h \<^bold>\<sim> a" 
  and
  dtil1:"a \<^bold>\<approx> b" and  
  dtil2:"c \<^bold>\<approx> d" and  
  dtil3:"e \<^bold>\<approx> f" and  
  dtil4:"g \<^bold>\<approx> h" and
  dtil5:"\<not>(a \<^bold>\<approx> c)" and dtil6: "\<not>(a \<^bold>\<approx> e)" and dtil7:"\<not>(a \<^bold>\<approx> g)" and
  dtil8:"\<not>(c \<^bold>\<approx> e)" and dtil9:"\<not>(c \<^bold>\<approx> g)" and 
  dtil10: "\<not>(e \<^bold>\<approx> g)"
  and
  Neigh: "\<forall>w. \<forall>H. ((N w) H \<longleftrightarrow> (H w \<and> (\<not> (check_subset H (\<lambda>x. (x=a \<or> x=c \<or> x=e \<or> x=g))))  
    \<and> (\<not> (check_subset H (\<lambda>x. (x=b \<or> x=d \<or> x=f \<or> x=h))))))"
 

\<comment> \<open>Right to know pa and pb, but no right to know pc in world h.\<close>
lemma ex_ra: "\<lfloor>Rr \<^sup>Apa\<rfloor>\<^sub>h" by (smt (verit) a0 aa ab ac ad ae af ag ah dtil1 dtil2 dtil3 dtil4 dtil6 dtil7 dtil8 dtil9 dtil_sym dtil_trans)
lemma ex_rb: "\<lfloor>Rr \<^sup>Apb\<rfloor>\<^sub>h" by (smt (verit) a0 aa ab ac ad ae af ag ah dtil1 dtil10 dtil2 dtil3 dtil4 dtil5 dtil6 dtil7 dtil8 dtil_sym dtil_trans)
lemma ex_rc: "\<lfloor>\<^bold>\<not>Rr \<^sup>Apc\<rfloor>\<^sub>h" using aa ab dtil1 dtil_ref by auto

lemma ex_oa: "\<lfloor>(Os \<^sup>Apa)\<rfloor>\<^sub>h" 
  nitpick[user_axioms] \<comment> \<open>Nitpick found a counterexample\<close> 
  oops

lemma ex_ob: "\<lfloor>Os \<^sup>Apb\<rfloor>\<^sub>h" 
  nitpick[user_axioms] \<comment> \<open>Nitpick found a counterexample\<close> 
  oops

lemma ex_oc: "\<lfloor>Os \<^sup>Apc\<rfloor>\<^sub>h" 
  nitpick[user_axioms] \<comment> \<open>Nitpick found a counterexample\<close> 
  oops

\<comment> \<open>Obligation for data processor to announce pa if asked.\<close>
\<comment> \<open>Model updated with pa.\<close>
lemma ex_aska_ra: "\<lfloor>[r:\<^sup>Apa?]Rr \<^sup>Apa\<rfloor>\<^sub>h" by (simp add: ex_ra)
lemma ex_aska_rb: "\<lfloor>[r:\<^sup>Apa?]Rr \<^sup>Apb\<rfloor>\<^sub>h" by (metis ex_rb)
lemma ex_aska_rc: "\<lfloor>[r:\<^sup>Apa?]\<^bold>\<not>Rr \<^sup>Apc\<rfloor>\<^sub>h" using ex_rc by auto
lemma ex_aska_oa: "\<lfloor>[r:\<^sup>Apa?]Os \<^sup>Apa\<rfloor>\<^sub>h" using Nax ah ex_ra by blast

\<comment> \<open>Obligation for data processor to announce pb if asked.\<close>
\<comment> \<open>Model updated first with pa and then with pb.\<close>
lemma ex_askb_ra: "\<lfloor>[r:\<^sup>Apb?]([r:\<^sup>Apa?]Rr \<^sup>Apa)\<rfloor>\<^sub>h" using ex_ra by force
lemma ex_askb_rb: "\<lfloor>[r:\<^sup>Apb?]([r:\<^sup>Apa?]Rr \<^sup>Apb)\<rfloor>\<^sub>h" using ex_aska_rb by presburger
lemma ex_askb_rc: "\<lfloor>[r:\<^sup>Apb?]([r:\<^sup>Apa?]\<^bold>\<not>Rr \<^sup>Apc)\<rfloor>\<^sub>h" using ex_rc by blast
lemma ex_askb_oa: "\<lfloor>[r:\<^sup>Apb?]([r:\<^sup>Apa?]Os \<^sup>Apa)\<rfloor>\<^sub>h" by (smt (z3) Nax ah ex_ra ex_rb)
lemma ex_askb_ob: "\<lfloor>[r:\<^sup>Apb?]([r:\<^sup>Apa?]Os \<^sup>Apb)\<rfloor>\<^sub>h" by (smt (z3) Nax ah ex_ra ex_rb)

\<comment> \<open>No obligation for data processor to announce pc if asked.\<close>
\<comment> \<open>Model updated first with pa and then with pc.\<close>
lemma ex_askc_ra: "\<lfloor>[r:\<^sup>Apc?]([r:\<^sup>Apa?]Rr \<^sup>Apa)\<rfloor>\<^sub>h" using ex_ra by force
lemma ex_askc_rb: "\<lfloor>[r:\<^sup>Apc?]([r:\<^sup>Apa?]Rr \<^sup>Apb)\<rfloor>\<^sub>h" using ex_rb by blast
lemma ex_askc_rc: "\<lfloor>[r:\<^sup>Apc?]([r:\<^sup>Apa?]\<^bold>\<not>Rr \<^sup>Apc)\<rfloor>\<^sub>h" using ex_rc by blast
lemma ex_askc_oa: "\<lfloor>[r:\<^sup>Apc?]([r:\<^sup>Apa?]Os \<^sup>Apa)\<rfloor>\<^sub>h" by (smt (z3) Nax ah ex_ra ex_rb)
lemma ex_askc_oc: "\<lfloor>[r:\<^sup>Apc?]([r:\<^sup>Apa?]Os \<^sup>Apc)\<rfloor>\<^sub>h" 
  nitpick[user_axioms] \<comment> \<open>Nitpick found a counterexample\<close> 
  oops



end
