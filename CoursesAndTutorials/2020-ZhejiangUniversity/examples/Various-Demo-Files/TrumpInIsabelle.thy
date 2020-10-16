theory TrumpInIsabelle           (*Christoph Benzmüller and Alexander Steen, 2019*)
imports Definitions (*import of basic modal logic concepts in HOL *)
begin               (*unimportant*) sledgehammer_params[type_enc=mono_native,verbose]
                    (*unimportant*) nitpick_params[user_axioms,show_all,format=4]

consts (*accessibility relation for time, belief (of an agent), speech (of an agent)*)
  AnyTimeRel::\<alpha>   BeliefOfRel::"\<mu>\<Rightarrow>\<alpha>"   SaysRel::"\<mu>\<Rightarrow>\<alpha>"   

abbreviation "ANYTIME \<phi> \<equiv> \<^bold>\<box>AnyTimeRel \<phi>"       (*ANYTIME as modal operator*)
abbreviation "BELIEF x \<phi> \<equiv> \<^bold>\<box>(BeliefOfRel x) \<phi>" (*BELIEF as modal operator*)   
abbreviation "SAYS x \<phi> \<equiv> \<^bold>\<box>(SaysRel x) \<phi>"       (*SAYS as modal operator*)

consts (*uninterpreted, scenario specific constant symbols*) 
 Trump::\<mu> campaignOfTrump::\<mu> officeOfTrump::\<mu> birthCertObama::\<mu> calls::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" 
 isAbout::"\<sigma>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" source::"\<mu>\<Rightarrow>\<sigma>" credible::"\<mu>\<Rightarrow>\<sigma>" isFraud::"\<mu>\<Rightarrow>\<sigma>" 

axiomatization where  (*formalisation of Trump's tweets in multi-modal logic*)
 Tweet1: "\<lfloor>SAYS Trump (\<^bold>\<exists>x. source x \<^bold>\<and> credible x \<^bold>\<and> calls x officeOfTrump \<^bold>\<and> 
                          SAYS x (isFraud birthCertObama))\<rfloor>" and
 Tweet2: "\<lfloor>SAYS Trump (ANYTIME 
           (\<^bold>\<forall>\<^sup>\<sigma>s. ((isAbout s Trump \<^bold>\<or> isAbout s campaignOfTrump)
                   \<^bold>\<and> (\<^bold>\<exists>x. source x \<^bold>\<and> SAYS x s))
                 \<^bold>\<rightarrow> (\<^bold>\<forall>y. \<^bold>\<not>(BELIEF y s))))\<rfloor>" 

axiomatization where  (*a little implicit knowledge is needed*)
 Implicit: "\<lfloor>isAbout (isFraud birthCertObama) campaignOfTrump\<rfloor>" and
 AnyTimeIncludesNow: "\<lfloor>\<^bold>\<forall>\<^sup>\<sigma>s. ANYTIME s \<^bold>\<rightarrow> s\<rfloor>"  

(*consistency check*)
lemma True nitpick [satisfy,user_axioms,show_all] oops (*yes, model by nitpick*)

(*Trump (essentially) says that he does not belief that birthCertObama is fraud*)
lemma L1: "\<lfloor>SAYS Trump (\<^bold>\<not>(BELIEF Trump (isFraud birthCertObama)))\<rfloor>"  
 sledgehammer (*proof found*)
 by (metis AnyTimeIncludesNow Implicit Tweet1 Tweet2)

(*Trump does not belief that birthCertObama is fraud — not yet provable*)
lemma "\<lfloor>(\<^bold>\<not>(BELIEF Trump (isFraud birthCertObama)))\<rfloor>" 
  sledgehammer (*timeout*)
  nitpick oops (*countermodel*)

axiomatization where 
 TrumpBelievesWhatHeSays: "\<lfloor>\<^bold>\<forall>\<^sup>\<sigma>s. SAYS Trump s \<^bold>\<rightarrow> BELIEF Trump s\<rfloor>" and
 TrumpsBeliefIsTruth: "\<lfloor>\<^bold>\<forall>\<^sup>\<sigma>s. BELIEF Trump s \<^bold>\<leftrightarrow> s\<rfloor>"

(*Trump does not belief that birthCertObama is fraud*)
lemma L2: "\<lfloor>(\<^bold>\<not>(BELIEF Trump (isFraud birthCertObama)))\<rfloor>" 
  sledgehammer (*proof found*)
  using L1 TrumpBelievesWhatHeSays TrumpsBeliefIsTruth by auto

(*birthCertObama is no fraud*)
lemma "\<lfloor>(\<^bold>\<not>(isFraud birthCertObama))\<rfloor>" 
 sledgehammer (*proof found*)
 using L2 TrumpsBeliefIsTruth by auto 

axiomatization where TrumpBelievesCredibleSources: 
 "\<lfloor>\<^bold>\<forall>\<^sup>\<sigma>s. (\<^bold>\<exists>x. source x \<^bold>\<and> credible x \<^bold>\<and> SAYS x s) \<^bold>\<rightarrow> BELIEF Trump s\<rfloor>"  

(*Trump is an inconsistent, irrational agent*)
lemma False        
  sledgehammer (*proof found*)
 by (metis L2 TrumpBelievesCredibleSources TrumpBelievesWhatHeSays 
           TrumpsBeliefIsTruth Tweet1) 

end