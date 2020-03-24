theory IOL_out2 imports Main      
begin
  typedecl i \<comment> \<open>type for possible worlds \<close>  
  type_synonym \<tau> = "(i\<Rightarrow>bool)"
  consts r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)(* relation for a modal logic K *)
  abbreviation knot :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w) " 
  abbreviation kor :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)" 
  abbreviation kand :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)" 
  abbreviation kimp :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<longrightarrow>" 49) where "\<phi>\<^bold>\<longrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)"
  abbreviation kvalid :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8]109) where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p(w)"
  abbreviation kbox :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<box>\<^sub>k") where " \<^bold>\<box>\<^sub>k \<phi> \<equiv> \<lambda>w. \<forall>v. w r v \<longrightarrow> \<phi>(v)"
  abbreviation kdiamond :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<diamond>\<^sub>k") where " \<^bold>\<diamond>\<^sub>k \<phi> \<equiv> \<lambda>w. \<exists>v. w r v \<longrightarrow> \<phi>(v)"
  abbreviation ktrue  :: "\<tau>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
  abbreviation kfalse :: "\<tau>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 

(*Idea:  x \<in> out2(G,A) iff G\<^sup>\<box>\<union>A \<turnstile>\<^sub>K\<^bold>\<box>x \<and> x \<in> Cn(G(L))  *)  
  
locale TestExample =        (* OR example:  G = {(a,e),(b,e)}, e \<in> out2(G,{a \<or> b}) *)
  fixes a::\<tau> and b::\<tau> and e::\<tau>  
 begin
 (* G\<^sup>\<box>\<union>{a \<or> b} \<turnstile>\<^sub>K \<box>e *)
 lemma "\<lfloor>((a \<^bold>\<longrightarrow>\<^bold>\<box>\<^sub>ke) \<^bold>\<and> (b\<^bold>\<longrightarrow>\<^bold>\<box>\<^sub>ke) \<^bold>\<and> (a \<^bold>\<or> b)) \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>ke  \<rfloor>" by auto
 (* e \<in> Cn(G(L)) *)
 lemma " \<lfloor> (e \<^bold>\<and> e) \<^bold>\<longrightarrow> e \<rfloor>"  by simp 
 end

(*Drink and Drive Example*)
datatype indiv= Ali | Paul| Child
consts  Kill::"indiv\<Rightarrow>\<tau>" Hurt::"indiv\<Rightarrow>\<tau>" Drive_carefully::"indiv\<Rightarrow>\<tau>" Stay::"indiv\<Rightarrow>\<tau>"
               Drunk::"indiv\<Rightarrow>\<tau>" Jump::"indiv\<Rightarrow>\<tau>" Drive::"indiv\<Rightarrow>\<tau>"

locale PaulContext =
  assumes
  (* Norms *)
  A0: "\<lfloor> (\<^bold>\<top> \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>k (\<^bold>\<not> Kill Child \<^bold>\<and> \<^bold>\<not> Hurt Child )) \<rfloor>" and
  A1: "\<lfloor>  (\<^bold>\<top> \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>k ( Drive_carefully Paul ) )\<rfloor>" and
  A2: "\<lfloor>( (\<^bold>\<not>Drive_carefully Paul) \<^bold>\<longrightarrow>\<^bold>\<box>\<^sub>k(Stay Paul ) ) \<rfloor>"and
  (* Input set *) 
  A3: "\<lfloor>Drunk Paul\<rfloor>" and
  A4: "\<lfloor>Drive Paul\<rfloor>"  and
  A5: "\<lfloor>Jump Child\<rfloor>" and
  A6: "\<lfloor>Drunk Paul \<^bold>\<longrightarrow> \<^bold>\<not> Drive_carefully Paul\<rfloor>" and
  A7:"\<lfloor>((\<^bold>\<not>Drive_carefully Paul) \<^bold>\<and> Drive Paul \<^bold>\<and> Jump Child )\<^bold>\<longrightarrow> ((Kill Child \<^bold>\<or> Hurt Child))\<rfloor>"
  begin
  lemma "\<lfloor>\<^bold>\<box>\<^sub>k(Stay Paul)\<rfloor>"   using A2 A3 A6 by auto 
  lemma "\<lfloor>\<^bold>\<box>\<^sub>k(Drive_carefully Paul)\<^bold>\<and>(\<^bold>\<not>Drive_carefully Paul) \<rfloor>"  using A1 A3 A6 by simp
  lemma "\<lfloor>\<^bold>\<box>\<^sub>k(\<^bold>\<not>Kill Child \<^bold>\<and> \<^bold>\<not>Hurt Child ) \<^bold>\<and> (Kill Child \<^bold>\<or> Hurt Child) \<rfloor>"  using A0 A3 A4 A5 A6 A7 by simp
  lemma True  nitpick [satisfy,user_axioms,show_all,expect=genuine] oops (*consistency*)
  end

locale AliContext =
  assumes
  (* Norms *)
  A0: "\<lfloor>\<^bold>\<top> \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>k(\<^bold>\<not> Kill Child \<^bold>\<and> \<^bold>\<not> Hurt Child)\<rfloor>" and
  A1: "\<lfloor>\<^bold>\<top> \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>k(Drive_carefully Ali)\<rfloor>" and
  A2: "\<lfloor>\<^bold>\<not> Drive_carefully Ali \<^bold>\<longrightarrow> \<^bold>\<box>\<^sub>k(Stay Ali)\<rfloor>"and
  (* Input set *)
  A3: "\<lfloor>Drunk Ali\<rfloor>" and
  A4: "\<lfloor>Drive Ali\<rfloor>" and
  A6: "\<lfloor>Drunk Ali \<^bold>\<longrightarrow> \<^bold>\<not> Drive_carefully Ali\<rfloor>" and
  A7: "\<lfloor>(\<^bold>\<not> Drive_carefully Ali \<^bold>\<and> Drive Ali \<^bold>\<and> Jump Child) \<^bold>\<longrightarrow> (Kill Child \<^bold>\<or> Hurt Child)\<rfloor>"
  begin
  lemma "\<lfloor>\<^bold>\<box>\<^sub>k(Stay Ali)\<rfloor>"   using A2 A3 A6 by simp
  lemma "\<lfloor>\<^bold>\<box>\<^sub>k(Drive_carefully Ali) \<^bold>\<and> \<^bold>\<not> Drive_carefully Ali\<rfloor>"  using A1 A3 A6 by simp
  lemma"\<lfloor>\<^bold>\<box>\<^sub>k(\<^bold>\<not>Kill Child \<^bold>\<and> \<^bold>\<not>Hurt Child) \<^bold>\<and> (Kill Child \<^bold>\<or> Hurt Child)\<rfloor>" nitpick [user_axioms] oops (*countermodel*)
  lemma True  nitpick [satisfy,user_axioms,show_all,expect=genuine] oops (*consistency*)
  end

end
  
