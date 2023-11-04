theory ddlsf imports Main            (* Christoph Benzmüller & Xavier Parent, 2023  *)

begin (* System E with neighborhood function *)
 typedecl i (*type for possible worlds*)
 type_synonym \<tau> = "(i\<Rightarrow>bool)"
 type_synonym \<gamma> = "\<tau>\<Rightarrow>\<tau>" 
 type_synonym \<rho> = "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>"

consts  ob::"\<tau>\<Rightarrow>(\<tau>\<Rightarrow>bool)" (*neighborhoud function*)
          
 axiomatization where
  ax_ref: "\<forall>X. ob(X)(X)" and 
  ax_or: "\<forall>X Y Z. (ob(X)(Z) \<and> ob(Y)(Z)) \<longrightarrow> (ob(\<lambda>w. (X)(w)\<or>(Y)(w))(Z))" and
  ax_cok:  "\<forall>X Y Z. (\<forall>w. (Y(w) \<longrightarrow> Z(w))) \<longrightarrow> (ob(X)(Y) \<longrightarrow> ob(X)(Z))" and
  ax_nec:  "\<forall>X Y. (\<forall>w. Y(w)) \<longrightarrow> ob(X)(Y)" and
  ax_transit: "\<forall>X Y Z. \<not>(ob(\<lambda>w. (X)(w)\<or>(Y)(w))(\<not>Z))\<and> \<not>(ob(\<lambda>w. (Y)(w)\<or>(Z)(w))(\<not>Y))\<longrightarrow> 
                          \<not>(ob(\<lambda>w. (X)(w)\<or>(Z)(w))(\<not>X))"

lemma rm: "\<forall>X Y Z.  (\<not>(ob(X)(\<not>Z) ) \<and> ob(X)(Y)) \<longrightarrow> ob(\<lambda>w.(X w)\<and>(Z w))(Y)"
 nitpick [show_all, card=3]
 sledgehammer oops







(* Consistency *) 
 lemma True nitpick [satisfy,user_axioms,show_all] oops 
end


