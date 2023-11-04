theory sf_DDL imports Main            (* Christoph Benzmüller & Xavier Parent, 2023  *)

begin (* DDL: Dyadic Deontic Logic with selection function *)
 typedecl i (*type for possible worlds*)
 type_synonym \<tau> = "(i\<Rightarrow>bool)"
 type_synonym \<gamma> = "\<tau>\<Rightarrow>\<tau>" 
 type_synonym \<rho> = "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>"

consts  ob::"\<tau>\<Rightarrow>\<tau>" (*selection function takes a set of worlds as input and
 gives a set of worlds as output*)

axiomatization where
 (* ax_1: "\<forall>X Y.  X=Y  \<longrightarrow> (ob(X) = ob(Y))" and(*extrnsionality*)*)
  ax_2: "\<forall>X Y.  ob(X\<inter>Y)\<subseteq> ob(X)\<inter>Y" and (*Chernoff*)
  ax_3: "\<forall>X.  ob(X) \<subseteq> X"  (*Inclusion*) and
  ax_4: "\<forall>X Y.  (ob(X)\<subseteq> ob( X \<union> Y)) \<or>  (ob(Y)\<subseteq> ob( X \<union> Y))"   (*s-drat*)

lemma  "\<forall>X Y.  (X \<subseteq> Y  \<longrightarrow> (ob(X \<inter> Y ) \<subseteq> ob(Y)))"
  sledgehammer [user_axioms,show_all]

lemma arrow: "\<forall>X Y.  ( (ob(X)\<inter>Y)\<noteq>(\<lambda>x. False)  ) \<longrightarrow> ( ob(X)\<inter>Y \<subseteq> ob(X\<inter>Y) )"
  nitpick [user_axioms,show_all, format=2] 
  sledgehammer


lemma True nitpick [satisfy,user_axioms,show_all] oops 
end


