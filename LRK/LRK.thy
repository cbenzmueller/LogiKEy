\<comment> \<open>Lara Lawniczak, Luca Pasetto, Christoph Benzmüller, Xu Li and Réka Markovich
Reasoning with Epistemic Rights and Duties: Automating a Dynamic Logic of the Right to Know in LogiKEy\<close>

\<comment> \<open>Implementation of "A Dynamic Logic of the Right to Know" by Xu Li and Réka Markovich

We present a shallow embedding of a dynamic logic of the right to know (LRK)
in HOL. We then use LKR to encode the example provided within the paper.\<close>

\<comment> \<open>While there are different notions of the right to know, the paper at hand 
focuses on the power to know in a sender-receiver setting. Intuitively, we are
trying to express the receiver's power to know whether P, which is equivalent
to the sender's obligation to truthfully state P. LRK is a dynamic logic. It 
focuses on the dynamics of asking questions, announcing information, and
updating the model in accordance with new information.\<close>

theory LRK
  imports Main 
begin 

 \<comment> \<open>LRK uses the following types:\<close>
 \<comment> \<open>type for possible worlds\<close>
typedecl i
\<comment>\<open>type for formulas: A proposition holds in a world\<close>
type_synonym \<sigma> = "(i\<Rightarrow>bool)" 
\<comment>\<open>type for accessibility relations\<close>
type_synonym \<gamma> = "(i\<Rightarrow>i\<Rightarrow>bool)" 
\<comment>\<open>type for neighborhood function\<close>
type_synonym \<upsilon> = "(i\<Rightarrow>((i\<Rightarrow>bool)\<Rightarrow>bool))" 
\<comment>\<open>formulas within their context, consisting of the accessibility relation
@{text"til"} and the neighborhood relation @{text"N"}. Both these relations can change with
the updates of the model, which is why they are needed in the context.\<close>

\<comment>\<open>changed to include Rq as well\<close>
type_synonym \<tau> = "\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<upsilon>\<Rightarrow>\<sigma>"

consts
\<comment> \<open>The set of questions the receiver is allowed to know the answers to\<close>
 dtil::\<gamma> (infix "\<^bold>\<approx>" 50)
\<comment> \<open>The usual indistinguishability relation for the receiver\<close>
 til::\<gamma> (infix "\<^bold>\<sim>" 50)
\<comment> \<open>The ideal epistemic states of the receiver\<close>
 N::"i\<Rightarrow>((i\<Rightarrow>bool)\<Rightarrow>bool)" 

\<comment> \<open>@{text"Rt"} and @{text "Rq"} are equivalence relations and therefore reflexive, transitive,
and symmetric. The axiom @{text "Nax"} constrains the neighborhood relation @{text "N"}, saying 
that all sets of worlds that are in the set of sets of worlds returned by @{text "N w"} 
contain @{text "w"} itself. This implies that none of the sets is empty.\<close>

axiomatization where
  til_ref: "\<forall>w. w \<^bold>\<sim> w" and
  til_sym: "\<forall>w v. w \<^bold>\<sim> v \<longrightarrow> v \<^bold>\<sim> w" and 
  til_trans: "\<forall>w v u. w \<^bold>\<sim> v \<and> v \<^bold>\<sim> u \<longrightarrow> w \<^bold>\<sim> u" and

  dtil_ref: "\<forall>w. w \<^bold>\<approx> w " and
  dtil_sym: "\<forall>w v. w \<^bold>\<approx> v \<longrightarrow> v \<^bold>\<approx> w" and 
  dtil_trans: "\<forall>w v u. w \<^bold>\<approx> v \<and> v \<^bold>\<approx> u \<longrightarrow> w \<^bold>\<approx> u" and

  Nax: "\<forall>w. \<forall>H. (N w H \<longrightarrow> H w)" 

\<comment> \<open>Embedding of the standard connectives. All formulas carry @{text "Rt"} and @{text "N"} 
in their context\<close>
abbreviation (input) atom::"\<sigma>\<Rightarrow>\<tau>" ("\<^sup>A_"[79]80) where "\<^sup>Ap \<equiv> \<lambda>t q n w. p w" 
abbreviation (input) lrkTop::\<tau> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>t q n w. True"
abbreviation (input) lrkBot::\<tau> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>t q n w. False" 
abbreviation (input) lrkNot::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_") where "\<^bold>\<not>\<phi> \<equiv> \<lambda>t q n w. \<not>(\<phi> t q n w)" 
abbreviation (input) lrkAnd::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("_\<^bold>\<and>_") where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>t q n w. (\<phi> t q n w) \<and> (\<psi> t q n w)"   
abbreviation (input) lrkOr::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("_ \<^bold>\<or> _") where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>t q n w. (\<phi> t q n w) \<or> (\<psi> t q n w)"   
abbreviation (input) lrkImp::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("_\<^bold>\<rightarrow>_") where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>t q n w. (\<phi> t q n w) \<longrightarrow> (\<psi> t q n w)"  
abbreviation (input) lrkEquiv::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("_\<^bold>\<leftrightarrow>_") where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>t q n w. (\<phi> t q n w)\<longleftrightarrow> (\<psi> t q n w)" 

\<comment> \<open>These are the abbreviations used to perform the updates on @{text "Rt"} and @{text "N"}, whenever
a question is asked or a new announcement is made.\<close>
abbreviation (input) update_t::"\<tau>\<Rightarrow>\<upsilon>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>"
  where "update_t \<phi> n t q \<equiv> \<lambda>u v. t u v \<and> (\<phi> t q n u \<longleftrightarrow> \<phi> t q n v)"
abbreviation (input) update_N::"\<tau>\<Rightarrow>\<upsilon>\<Rightarrow>\<gamma>\<Rightarrow>\<gamma>\<Rightarrow>\<upsilon>"
  where "update_N \<phi> n t q \<equiv> \<lambda>w.\<lambda>X. n w X \<and> 
    (((\<forall>v. (X v \<longrightarrow> (\<phi> t q n v))) \<or> 
    (\<forall>v. (X v \<longrightarrow> ((\<^bold>\<not>\<phi>) t q n v)))))"

\<comment> \<open>Connectives of LRK: @{text "U"} is the universal modality, @{text "Rr"} represents the right
to know of the receiver, @{text "Kr"} represents the knowledge of the receiver, and @{text "Os"}
the obligation of the sender to truthfully announce something. @{text "Q"} is only a 
technical modality.\<close>
abbreviation (input) lrkU::"\<tau>\<Rightarrow>\<tau>" ("U _") where "U \<phi> \<equiv> \<lambda>t q n w. \<forall>v. \<phi> t q n v"
abbreviation (input) lrkQ::"\<tau>\<Rightarrow>\<tau>" ("Q _") where "Q \<phi> \<equiv> \<lambda>t q n w. \<forall>v. (q w v) \<longrightarrow> (\<phi> t q n v)" 
abbreviation (input) lrkRr::"\<tau>\<Rightarrow>\<tau>" ("Rr _") where "Rr \<phi> \<equiv> \<lambda>t q n w. \<forall>va. \<forall>v. (q va v) \<longrightarrow> (\<phi> t q n v) \<or> (\<forall>v. q va v \<longrightarrow> (\<not>\<phi> t q n v))"
abbreviation (input) lrkKr::"\<tau>\<Rightarrow>\<tau>" ("Kr _") where "Kr \<phi> \<equiv> \<lambda>t q n w. \<forall>v. (t w v) \<longrightarrow> (\<phi> t q n v)"
abbreviation (input) lrkO::"\<tau>\<Rightarrow>\<tau>" ("Os _") where "Os \<phi> \<equiv> \<lambda>t q n w. \<forall>H. (n w H) \<longrightarrow> (\<forall>v. H v \<longrightarrow> (t w v)) \<longrightarrow> (\<forall>i. H i \<longrightarrow> (\<phi> t q n i))"

\<comment> \<open>The question and exclamation operators are the dynamic part of the logic,                                    
since they use the update functions defined previously.\<close>
abbreviation (input) lrkQuestion::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("[_?]_") 
  where "[\<phi>?]\<psi> \<equiv> \<lambda>t q n w. (\<psi> t q (update_N \<phi> n t q) w)"
abbreviation (input) lrkExclamation::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("[_!]_") 
  where "[\<phi>!]\<psi> \<equiv> \<lambda>t q n w. (\<psi> (update_t \<phi> n t q) q n w)" 
abbreviation (input) lrkExclamationPos::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("<_!>_")
  where "<\<phi>!>\<psi> \<equiv> \<^bold>\<not>[\<phi>!]\<^bold>\<not>\<psi>"
abbreviation (input) lrkQuestionPos::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("<_?>_") 
  where "<\<phi>?>\<psi> \<equiv> \<^bold>\<not>[\<phi>?]\<^bold>\<not>\<psi>"

\<comment> \<open>The after question operator checks what holds after a question has been 
asked by the receiver.\<close>
abbreviation (input) lrkAfterQuestion::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("[r:_?]_") 
  where "[r:\<phi>?]\<psi> \<equiv>  (((\<^bold>\<not> Rr \<phi>) \<^bold>\<and> \<psi>) \<^bold>\<or> ((Rr \<phi>) \<^bold>\<and> [\<phi>?]\<psi>))"
\<comment> \<open>The after exclamation operator checks what holds after an exclamation has been 
made by the sender.\<close>
abbreviation (input) lrkAfterExclamation::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("[s:_!]_") 
  where "[s:\<phi>!]\<psi> \<equiv> \<phi> \<^bold>\<rightarrow> [\<phi>!]\<psi>"

\<comment> \<open>Finally, we define the notions of local and global validity.\<close>
abbreviation (input) rtkValidLocal::"\<tau>\<Rightarrow>i\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>_") where "\<lfloor>\<phi>\<rfloor>\<^sub>w \<equiv> \<phi> til dtil N w"
abbreviation (input) rtkValidGlobal::"\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> til dtil N w" 

\<comment> \<open>Consistency Check: Nitpick finds a model\<close>
lemma True nitpick [satisfy,user_axioms,show_all, card i=3] oops

end
