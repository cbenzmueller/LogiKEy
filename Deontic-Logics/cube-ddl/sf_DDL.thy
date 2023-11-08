theory sf_DDL imports Main            (* Christoph Benzmüller & Xavier Parent, 2023  *)

begin (* DDL: this is a selection function semantics for DDL--we just introduce the 
selection function *)
 typedecl i (*type for possible worlds*)
 type_synonym \<tau> = "(i\<Rightarrow>bool)"
 type_synonym \<gamma> = "\<tau>\<Rightarrow>\<tau>" 

consts  ob::"\<gamma>" (*selection function takes a set of worlds as input and
 gives a set of worlds as output. Is the type correct? This is taken from the IJCAI-13 paper*)

axiomatization where (*X and Y are sets of possible worlds: why do I get some pink here?*)
 ax_0: "\<forall>Y Z. (\<forall>w. (Y(w) \<longleftrightarrow> Z(w))) \<longrightarrow> (ob(Y) \<longleftrightarrow> ob(Z))"  and(*extrnsionality*)*)
  ax_1: "\<forall>Y Z.  ob((\<lambda>w. Y(w) \<and> Z(w))\<subseteq> ob(X)\<inter>Y" and (*Chernoff*)
  ax_2: "\<forall>X.  ob(X) \<subseteq> X"  (*Inclusion*) and
  ax_3: "\<forall>X Y.  (ob(X)\<subseteq> ob( X \<union> Y)) \<or>  (ob(Y)\<subseteq> ob( X \<union> Y))"   (*s-drat*)

(*consistency verified *)

lemma True nitpick [satisfy,user_axioms,show_all] oops

(*This is just another test, but it fails: it should be derivable, but it is not *)
 
lemma  "\<forall>X Y.  (X \<subseteq> Y  \<longrightarrow> (ob(X \<inter> Y ) \<subseteq> ob(Y)))"
  sledgehammer [user_axioms,show_all] oops  (*no proof state*)
  nitpick oops (*no proof state*)

(*The following should be falsifiable in a model where user_axioms are all true, for any value 
of X and Y*)

lemma arrow: "\<forall>X Y.   ((ob(X)\<inter>Y)\<noteq>(\<lambda>x. False) )  \<longrightarrow> ( ob(X)\<inter>Y \<subseteq> ob(X\<inter>Y) )"
  nitpick [user_axioms,show_all] oops (*no proof state*)
  sledgehammer (*no proof state*)




end


