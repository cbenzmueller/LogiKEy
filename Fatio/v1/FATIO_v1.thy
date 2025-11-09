section ‹FATIO›


theory FATIO_v1 imports HOMML 

begin

(* nitpick_params[user_axioms,format=2,show_all,expect=genuine] *)
nitpick_params[user_axioms,format=2,show_all]
named_theorems FatioDefs


section ‹Introduction›

(* maybe we want postulate that: "∀x y. ¬(x = y) ⟶ ¬(@⇧Bx = @⇧By)" ?*)
(* maybe we want postulate that: "∀x y. ¬(x = y) ⟶ ¬(@⇧Dx = @⇧Dy)" ?*) 

datatype Speaker = a | b | c 

consts BeliefRelationOf::"Speaker⇒α" ("@⇧B_") 
consts DesireRelationOf::"Speaker⇒α" ("@⇧D_") 
(*
definition BeliefOfSpeaker::"Speaker⇒σ⇒σ" ("❙B⇩_ _" [501,400] 500) where
*)
definition BeliefOfSpeaker::"Speaker⇒σ⇒σ" ("❙B⇩_ _" ) where
  "❙B⇩x φ ≡ (❙□ (@⇧B x) φ)"
definition DesireOfSpeaker::"Speaker⇒σ⇒σ" ("❙D⇩_ _" ) where
  "❙D⇩x φ ≡ (❙□ (@⇧D x) φ)"

(* checking the priorities of the symbols *)
lemma "❙B⇩a ❙B⇩a φ = ❙B⇩a (❙B⇩a φ)" ..
  

axiomatization where
  AxiomKD45b: "∀s::Speaker. serial (@⇧B s) ∧ transitive (@⇧B s) ∧ euclidean (@⇧B s)" 
axiomatization where
  AxiomKDd: "∀s::Speaker. serial (@⇧D s)" 

definition BDvalid::"σ⇒bool" ("⊨⇧B⇧D_") where 
  "⊨⇧B⇧D φ ≡ ⌊φ⌋"

(* 
definition BDconsequence::"(σ ⇒ bool) ⇒ σ ⇒ bool" ("_ ⊨ _") where 
  "Γ ⊨ φ ≡ Γ ❙⊨ φ" 
*)


(* adding to FatioDefs *) 
declare L_global_consequence_def[FatioDefs] global_consequence_def[FatioDefs] BDvalid_def[FatioDefs] BeliefOfSpeaker_def[FatioDefs] DesireOfSpeaker_def[FatioDefs] 

(* allows to use {} notation for σ⇒bool, which is not a set *)
abbreviation eset::"σ⇒bool" ("{}") where
  "eset ≡ λx. False"


term "((❙B⇩a φ) ❙→ (❙B⇩a (❙B⇩a φ)))"
term "⊨⇧B⇧D (❙B⇩a φ)"
term "⊨⇧B⇧D ((❙B⇩a φ) ❙→ (❙B⇩a (❙B⇩a φ)))"
term "(φ ❙→ (❙B⇩a φ))"

(* testing consequence *)
term "{} ⊨ (❙B⇩a φ)"
lemma "{} ⊨ (❙B⇩a φ)"
  unfolding FatioDefs
  oops

term "{❙B⇩a φ}"
term "λx. x=(❙B⇩a φ)"

term "[] ⊨l (❙B⇩a φ)"
term "[❙B⇩a φ]"

 (* this is using the notion of consequence with sets *)
lemma "{❙B⇩a φ} ⊨s (❙B⇩a φ)"
  by (simp add: global_consequence_s_def)


lemma "(λx. x=(❙B⇩a φ)) ⊨ (❙B⇩a φ)"
  unfolding FatioDefs
  by (simp add: global_consequence_def)  

term "[❙B⇩a φ] ⊨l (❙B⇩a φ)"
lemma "[❙B⇩a φ] ⊨l (❙B⇩a φ)"
  by (metis L_global_consequence_def in_set_member list.set_intros(1))

(* testing beliefs *)
term "⊨⇧B⇧D (❙B⇩a φ)"
lemma "⊨⇧B⇧D (❙B⇩a φ)"
  oops

term "( φ) ❙↔ ( ❙¬❙¬φ)"
lemma "{}⊨ ( φ) ❙↔ ( ❙¬❙¬φ)"
  by (simp add: global_consequence_def mequ_def mneg_def)

term "⊨⇧B⇧D ( φ) ❙↔ ( ❙¬❙¬φ)"
lemma "⊨⇧B⇧D ( φ) ❙↔ ( ❙¬❙¬φ)"
  by (simp add: BDvalid_def global_valid_def mequ_def mneg_def)

lemma "⊨⇧B⇧D (❙B⇩a φ) ❙↔ (❙B⇩a ❙¬❙¬φ)"
  by (simp add: BDvalid_def global_valid_def mequ_def mneg_def)
    (* expected because it's shallow *)

lemma "⊨⇧B⇧D (❙B⇩a φ) ⟷ ⊨⇧B⇧D (❙B⇩a ❙¬❙¬φ)"
  by (simp add: mneg_def)
 


lemma test1: "⊨⇧B⇧D ((❙B⇩a φ) ❙→ (❙B⇩a (❙B⇩a φ)))"
  unfolding BDvalid_def global_valid_def 
  unfolding BeliefOfSpeaker_def 
  unfolding mbox_def 
  unfolding mimp_def 
  by (meson AxiomKD45b transitive_def)

lemma test1a: "⊨⇧B⇧D ((❙B⇩a (❙B⇩a φ)) ❙→ (❙B⇩a φ))"
  unfolding BDvalid_def global_valid_def 
  unfolding BeliefOfSpeaker_def 
  unfolding mbox_def 
  unfolding mimp_def 
  by (meson AxiomKD45b euclidean_def)

lemma test1b: "⊨⇧B⇧D ((❙B⇩a (❙B⇩a φ)) ❙↔ (❙B⇩a φ))"
  by (smt (verit, ccfv_SIG) BDvalid_def global_valid_def mequ_def mimp_def test1 test1a)


lemma test2: "⊨⇧B⇧D ((❙B⇩a φ) ❙→ (❙B⇩b (❙B⇩a φ)))" 
  oops

lemma test2a: "⊨⇧B⇧D (φ ❙→ (❙B⇩a φ))" 
  oops

lemma test2b: "⊨⇧B⇧D ((❙B⇩a φ) ❙→  φ)" 
  oops


(* testing desires *)
lemma test3: "⊨⇧B⇧D ((❙D⇩a φ) ❙→ (❙D⇩a (❙D⇩a φ)))" 
  oops

lemma test3b: "⊨⇧B⇧D (( φ) ❙→ (❙D⇩a (❙D⇩a φ)))" 
  oops

lemma test4: "⊨⇧B⇧D ((❙D⇩a φ) ❙→  φ)" 
  oops

lemma test5: "⊨⇧B⇧D ((❙D⇩a (❙D⇩a φ)) ❙→ (❙D⇩a φ))" 
  oops

lemma test6: "⊨⇧B⇧D (φ ❙→ (❙D⇩a φ))" 
  oops


datatype AtomExpression = p | q | r | n 

datatype Formula =   ―‹Formulas›
  Atom AtomExpression ("_⇧a")
  | Bot ("⊥") 
  | Neg Formula ("¬") 
  | And Formula Formula (infixr "∧" 97) 
  | Or Formula Formula (infixr "∨" 93) 
  | Imp Formula Formula (infixr "→" 95) 

fun Lit::"Formula⇒bool" where
  "Lit (Atom _) = True"
| "Lit (Neg (Atom _)) = True"
| "Lit _ = False"

term "Lit (Atom p)"
value "Lit (Atom p)"

datatype Sign = Plus ("+") | Minus ("-")

datatype FatioL =   ―‹Fatio Language›
  Assert Speaker Formula ("assert[_,_]")
  | Question Speaker Speaker Formula ("question[_,_,_]")
  | Justify Speaker Formula Sign Formula ("justify[_,_⊢⇧__]")
  | Challenge Speaker Speaker Formula ("challenge[_,_,_]")
  | Retract Speaker Formula Sign ("retract[_,_,_]")

(* mappings to shallow embedding *)
consts mkHOMMLatom::"AtomExpression⇒σ" (* valuation of atoms *)
consts MapDone::"FatioL⇒σ"
consts MapEntailment::"Sign⇒Formula⇒Formula⇒σ"

(* mapping of Formula, from deep to shallow *)
fun Map1::"Formula⇒σ" ("{_}") where
  "Map1 ((Atom x)) = mkHOMMLatom (x)"
| "Map1 (Bot) = mbot" 
| "Map1 (Neg φ) = (❙¬(Map1 φ))"
| "Map1 ((And φ ψ)) = ((Map1  (φ)) ❙∧ (Map1 (ψ)))"
| "Map1 ((Or φ ψ)) = ((Map1  (φ)) ❙∨ (Map1 (ψ)))"
| "Map1 ((Imp φ ψ)) = ((Map1  (φ)) ❙→ (Map1 (ψ)))"


(*
term "{φ}"
this would be ambiguous because it can be the mapping orthe set
*)

term "assert[i,φ]"
term "(Map1 (Atom at))"
term "(MapDone assert[i,φ])"

(* extensionality tests *)
term "(Atom p)"
term "assert[i,(Atom p)]"
term "⊨⇧B⇧D (Map1 (Atom p) ❙→ Map1 (Atom p))"
lemma "(⊨⇧B⇧D (Map1 (Atom p) ❙→ Map1 (Atom p))) = (⊨⇧B⇧D (Map1 (Atom q) ❙→ Map1 (Atom q))) "
  by (simp add: mimp_def)

lemma "(Map1 (Atom p) ❙→ Map1 (Atom p)) = (Map1 (Atom q) ❙→ Map1 (Atom q))"
  by (simp add: mimp_def)

lemma "(Map1 (Atom p) ❙→ Map1 (Atom q)) = (Map1 (¬ (Atom q)) ❙→ Map1 (¬ (Atom p)))"
  using mimp_def mneg_def by auto

lemma "(Map1 (Atom p) ❙→ Map1 (Atom p)) = (Map1 ( ¬⊥ ))"
  by (simp add: mbot_def mimp_def mneg_def)

lemma "(Map1 ((Atom p) → (Atom p))) = (Map1 ( ¬⊥ ))"
  by (simp add: mbot_def mimp_def mneg_def)

lemma "((Atom p) → (Atom p)) = ( ¬⊥ )"
  nitpick
  oops


  term "assert[i, (Atom p)]"
  term "assert[i, (Atom p) → (Atom p)]"
  term "(assert[i, (Atom p) → (Atom p)]) = (assert[i, (Atom p) → (Atom p)])"
lemma "∀i. ((assert[i, (Atom p) → (Atom p)]) = (assert[i, (Atom p) → (Atom p)]))"
  by simp
lemma "(assert[a, (Atom p) → (Atom p)]) = (assert[a, (Atom q) → (Atom q)])"
  oops
    (* it is deep *)
lemma "MapDone (assert[a, (Atom p) → (Atom p)]) = MapDone (assert[a, (Atom q) → (Atom q)])"
  oops

lemma "(assert[a, (Atom p) → (Atom p)]) = (assert[a, ¬⊥])"
  nitpick
  oops

lemma "MapDone (assert[a, (Atom p) → (Atom p)]) = MapDone (assert[a, ¬⊥])" 
  nitpick
  oops

lemma "¬(assert[a, (Atom p) → (Atom p)] = assert[a, ¬⊥])"
  by simp

lemma "¬(MapDone (assert[a, (Atom p) → (Atom p)]) = MapDone (assert[a, ¬⊥]))" 
  oops


term "(❙D⇩a φ)"
term "(❙D⇩a (at ❙∧ bt))"

term "(❙D⇩a(❙B⇩a(❙B⇩a (φ))))"



(*
type_synonym DOS = "Speaker⇒(Speaker⇒Formula⇒Sign⇒bool)"
*)
(*
type_synonym DOS = "Speaker⇒(Formula⇒Sign⇒bool)"
consts dos::"DOS list"
*)

(* DOS Entry *)
datatype DOS = Entry Speaker Formula Sign 
  (* consts dos::"DOSEntry list" *)
  (* datatype DOS = DOSEntry list *)
  (* maybe a stack instead of a list for DOS? *)


(*
the following is to check  what happens for reasoning modulo Boolean extensionality
using lists, like we do for DOS
*)

lemma "[r⇧a → r⇧a] = []"
  oops

lemma "[r⇧a → r⇧a] = [¬⊥]" (* this is not extensional, good, we can use the list inthis way *)
  apply simp 
  oops

lemma "(remove1 (r⇧a → r⇧a) ([r⇧a → r⇧a])) = []"
  by simp

lemma "(remove1 (r⇧a → r⇧a) ([r⇧a, r⇧a → r⇧a])) = []"
  apply simp
  oops

lemma "[Map1 (r⇧a → r⇧a)] = [Map1 (¬⊥)]" (* this is extensional (shallow) *)
  by (simp add: mbot_def mimp_def mneg_def)

lemma "Map1 (r⇧a → r⇧a) = Map1 (¬⊥)" 
  by (simp add: mbot_def mimp_def mneg_def)

lemma "Map1 (r⇧a → r⇧a) = (Map1 (r⇧a) ❙→ Map1 (r⇧a))" 
  by simp

(* there is a choice to make on where to put the existential *)

lemma ent:"(⊨⇧B⇧D (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ ⊥]))) ⟶ (∃Δ. (⊨⇧B⇧D (MapDone justify[i, Δ ⊢⇧+ ⊥])))"
  unfolding FatioDefs
  unfolding Defs
  (* nitpick[box=false, eval="MapDone justify[i, Δ ⊢⇧+ ⊥]"] *)
  oops

lemma ent2:"(⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))) ⟶ 
            (∃Δ. (⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (MapDone justify[i, Δ ⊢⇧+ φ])))"
  unfolding FatioDefs
  unfolding Defs
  nitpick
  oops

lemma ent3:"(∃Δ. (⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (MapDone justify[i, Δ ⊢⇧+ φ])) ⟶ 
            (⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))))"
  unfolding FatioDefs
  unfolding Defs
  by simp

lemma ent4:"(⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (❙∀Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))) ⟶ (∀Δ. (⊨⇧B⇧D ❙D⇩j❙B⇩k❙D⇩j (MapDone justify[i, Δ ⊢⇧+ φ])))"
  unfolding FatioDefs
  unfolding Defs 
  by auto



(* use List.member instead
primrec isIn :: "DOS ⇒ DOS list ⇒ bool" where
  "isIn x [] = False" |
  "isIn x (y # xs) = (if x = y then True else isIn x xs)"
*)
value "List.member  [1, 2, 3, 4, 5] (3::int)"
lemma "List.member  [1, 2, 3, 4, 5] (3::int)" (* use this to check that an element is ∈a list *)
  by (simp add: member_rec(1))

fun reverse_list :: "'a list ⇒ 'a list ⇒ 'a list" where
  "reverse_list [] acc = acc" |
  "reverse_list (x # xs) acc = reverse_list xs (x # acc)"

definition reverse :: "'a list ⇒ 'a list" where
  "reverse xs = reverse_list xs []"

lemma "reverse [1, 2, 3] = [3, 2, 1]"
  by (simp add: reverse_def)

(* DOS update *)
fun
  DOSUpdate::"FatioL ⇒ DOS list ⇒ DOS list" 
  where
    "(DOSUpdate assert[i,φ] dos) = 
      ((Entry i φ +) # dos)"
  | "(DOSUpdate question[j,i,φ] dos) = 
         dos"
  | "(DOSUpdate justify[i, ψ ⊢⇧S φ] dos) = 
      ((Entry i ψ +) # dos)"   
  | "(DOSUpdate challenge[j,i,φ] dos) = 
      ((Entry j φ -) # dos)" 
  | "(DOSUpdate retract[i,φ,S] dos) = 
      ((remove1 (Entry i φ S) dos))"


(* for now the existentials are like inthe paper, maybe they can be taken outside the formula to simplify it*)
(* i put the dos as a parameter of the functions, so that precond andpostcond can be connected 
maybe also done has to be something like this? i can keep done inthe theory
*)

fun PreCond::"FatioL ⇒ (DOS list) ⇒ (σ ⇒ bool) ⇒ bool" 
  where
    "(PreCond assert[i,φ] dos Γ) =      
     (¬(List.member dos (Entry i φ +)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨ ❙D⇩i❙B⇩j❙B⇩i {φ})))"
  | "(PreCond question[j,i,φ] dos Γ) = 
      (¬(j = i) ∧ (List.member dos (Entry i φ +)) ∧ 
        (∀k. ¬(k = j) ⟶ ( (Γ ⊨ ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))))))"
  | "(PreCond justify[i, ψ ⊢⇧S φ] dos Γ) = 
      ((List.member dos (Entry i φ S)) ∧ 
       ( ∃j. ( (Γ ⊨ (MapDone question[j,i,φ]))  ∨  (Γ ⊨ (MapDone challenge[j,i,φ])) )
       ∧ 
       (∀k. ¬(k = i) ⟶ (Γ ⊨ ❙D⇩i❙B⇩k❙B⇩i (MapEntailment S ψ φ) )) ))"
  | "(PreCond challenge[j,i,φ] dos Γ) = 
      (¬(j = i) ∧ (List.member dos (Entry i φ +)) ∧ 
        (∀k. ¬(k = j) ⟶ ((Γ ⊨ ❙D⇩j❙B⇩k ❙¬❙B⇩j {φ}) ∧ (Γ ⊨ ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))))))"
  | "(PreCond retract[i,φ,S] dos Γ) = 
      (if S=+ then
        ((List.member dos (Entry i φ +)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨ ❙D⇩i❙B⇩j ❙¬❙B⇩i {φ})))
      else
        ((List.member dos (Entry i φ -)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨ ❙D⇩i❙B⇩j ❙¬❙¬❙B⇩i {φ})))
    )"

fun L_PreCond::"FatioL ⇒ (DOS list) ⇒ (σ list) ⇒ bool" 
  where
    "(L_PreCond assert[i,φ] dos Γ) =      
     (¬(List.member dos (Entry i φ +)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨l ❙D⇩i❙B⇩j❙B⇩i {φ})))"
  | "(L_PreCond question[j,i,φ] dos Γ) = 
      (¬(j = i) ∧ (List.member dos (Entry i φ +)) ∧ 
        (∀k. ¬(k = j) ⟶ ( (Γ ⊨l ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))))))"
  | "(L_PreCond justify[i, ψ ⊢⇧S φ] dos Γ) = 
      ((List.member dos (Entry i φ S)) ∧ 
       ( ∃j. ( (Γ ⊨l (MapDone question[j,i,φ]))  ∨  (Γ ⊨l (MapDone challenge[j,i,φ])) )
       ∧ 
       (∀k. ¬(k = i) ⟶ (Γ ⊨l ❙D⇩i❙B⇩k❙B⇩i (MapEntailment S ψ φ) )) ))"
  | "(L_PreCond challenge[j,i,φ] dos Γ) = 
      (¬(j = i) ∧ (List.member dos (Entry i φ +)) ∧ 
        (∀k. ¬(k = j) ⟶ ((Γ ⊨l ❙D⇩j❙B⇩k ❙¬❙B⇩j {φ}) ∧ (Γ ⊨l ❙D⇩j❙B⇩k❙D⇩j (❙∃Δ.(MapDone justify[i, Δ ⊢⇧+ φ]))))))"
  | "(L_PreCond retract[i,φ,S] dos Γ) = 
      (if S=+ then
        ((List.member dos (Entry i φ +)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨l ❙D⇩i❙B⇩j ❙¬❙B⇩i {φ})))
      else
        ((List.member dos (Entry i φ -)) ∧ (∀j. ¬(j = i) ⟶ (Γ ⊨l ❙D⇩i❙B⇩j ❙¬❙¬❙B⇩i {φ})))
     )"



(*
export_code PreCond in SML module_name Example
*)



(* characteristic predicate of objects of type σ 
choose this
set theory also has comprehension axioms, that complicate things
*)

(* this gives the formulas that satisfy the PostCond *)
fun GammaAdd::"FatioL ⇒ (σ ⇒ bool)" 
  where 
    "(GammaAdd assert[i,φ]) = 
      (λx. (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ (x =  ❙B⇩k❙D⇩i❙B⇩j❙B⇩i {φ})))"
  | "(GammaAdd question[j,i,φ]) = 
      (λx. True)" (* simplified *) (* (λx. (∃Δ. (x = (MapDone justify[i, Δ ⊢⇧+ φ])))) *)
  | "(GammaAdd justify[i, ψ ⊢⇧S φ]) =  
      (λx. (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ (x =  ❙B⇩k❙D⇩i❙B⇩j❙B⇩i (MapEntailment S ψ φ) )))"   
  | "(GammaAdd challenge[j,i,φ]) =  
      (λx. True)" (* simplified *) (* (λx. (∃Δ. (x = (MapDone justify[i, Δ ⊢⇧+ φ]))) ) *)
  | "(GammaAdd retract[i,φ,S]) = 
      (λx. (if S=+ then
              (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ (x =  ❙B⇩k❙D⇩i❙B⇩j ❙¬❙B⇩i {φ}))
            else 
              (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ (x =  ❙B⇩k❙D⇩i❙B⇩j ❙¬❙¬❙B⇩i {φ}))
     ))"

(* list version *)
(* have 2 Speaker lists + a backup to iterate on j k *)
(* i also check that the elements do not appear already inGamma *)
fun LGA1::"Speaker ⇒ Speaker list ⇒ Speaker list ⇒ Speaker list ⇒ Formula ⇒ (σ list) ⇒ (σ list)" 
  where 
    "LGA1 i (k#sp1) (j#sp2) sp2copy φ Γ = 
      (if i=k then (LGA1 i (sp1) (j#sp2) sp2copy φ Γ) else 
       (if i=j then (LGA1 i (k#sp1) (sp2) sp2copy φ Γ) else
        (if List.member Γ (❙B⇩k❙D⇩i❙B⇩j❙B⇩i {φ}) then (LGA1 i (k#sp1) (sp2) sp2copy φ (Γ))  else
          (LGA1 i (k#sp1) (sp2) sp2copy φ ((❙B⇩k❙D⇩i❙B⇩j❙B⇩i {φ}) # Γ))
        )
       )
      )"
  | "LGA1 i (k#sp1) [] sp2copy φ Γ =
      LGA1 i sp1 sp2copy sp2copy φ Γ"
  | "LGA1 i [] (sp2) sp2copy φ Γ = Γ"

fun LGA3::"Speaker ⇒ Speaker list ⇒ Speaker list ⇒ Speaker list ⇒ Formula ⇒ Sign ⇒ Formula ⇒ (σ list) ⇒ (σ list)" 
  where 
    "LGA3 i (k#sp1) (j#sp2) sp2copy ψ S φ Γ = 
      (if i=k then (LGA3 i (sp1) (j#sp2) sp2copy ψ S φ Γ) else 
       (if i=j then (LGA3 i (k#sp1) (sp2) sp2copy ψ S φ Γ) else
         (if List.member Γ ( ❙B⇩k❙D⇩i❙B⇩j❙B⇩i (MapEntailment S ψ φ) )  then (LGA3 i (k#sp1) (sp2) sp2copy ψ S φ Γ) else
          (LGA3 i (k#sp1) (sp2) sp2copy ψ S φ (( ❙B⇩k❙D⇩i❙B⇩j❙B⇩i (MapEntailment S ψ φ) ) # Γ))
         ) 
       )
      )"
  | "LGA3 i (k#sp1) [] sp2copy ψ S φ Γ =
      LGA3 i sp1 sp2copy sp2copy ψ S φ Γ"
  | "LGA3 i [] (sp2) sp2copy ψ S φ Γ = Γ"

(* todo this is only retracting positively *)
fun LGA5::"Speaker ⇒ Speaker list ⇒ Speaker list ⇒ Speaker list ⇒ Formula ⇒ (σ list) ⇒ (σ list)" 
  where 
    "LGA5 i (k#sp1) (j#sp2) sp2copy φ Γ = 
      (if i=k then (LGA5 i (sp1) (j#sp2) sp2copy φ Γ) else 
       (if i=j then (LGA5 i (k#sp1) (sp2) sp2copy φ Γ) else
        (if List.member Γ ( ❙B⇩k❙D⇩i❙B⇩j ❙¬❙B⇩i {φ} ) then (LGA5 i (k#sp1) (sp2) sp2copy φ Γ) else
         (LGA5 i (k#sp1) (sp2) sp2copy φ (( ❙B⇩k❙D⇩i❙B⇩j ❙¬❙B⇩i {φ} ) # Γ)) 
        )
       )
      )" 
  | "LGA5 i (k#sp1) [] sp2copy φ Γ =
      LGA5 i sp1 sp2copy sp2copy φ Γ"
  | "LGA5 i [] (sp2) sp2copy φ Γ = Γ"

term "[a, b, c]"

fun L_GammaAdd::"FatioL ⇒ (σ list) ⇒ (σ list)"
  where 
    "(L_GammaAdd assert[i,φ] Γ) = (LGA1 i [a, b, c] [a, b, c] [a, b, c] φ Γ)"
  | "(L_GammaAdd question[j,i,φ] Γ) = Γ"
  | "(L_GammaAdd justify[i, ψ ⊢⇧S φ] Γ) = (LGA3 i [a, b, c] [a, b, c] [a, b, c] ψ S φ Γ)"   
  | "(L_GammaAdd challenge[j,i,φ] Γ) = Γ" 
  | "(L_GammaAdd retract[i,φ,S] Γ) = (LGA5 i [a, b, c] [a, b, c] [a, b, c] φ Γ)"


(*
fun L_GammaAdd::"FatioL ⇒ (σ list) ⇒ (σ list)"
  where 
    "(L_GammaAdd assert[i,φ] Γ) = 
       (∀k j. (if (¬(k = i) ∧ ¬(j = i)) then ((❙B⇩k❙D⇩i❙B⇩j❙B⇩i {φ}) # Γ) else Γ ))"
*)

(* gives me the formulas that we want to keep because consistent with what is added *)
fun GammaKeep::"FatioL ⇒ (σ ⇒ bool)"
  where 
    "(GammaKeep assert[i,φ]) = 
      (λx. (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ ¬ (x =  ❙¬ ❙B⇩k❙D⇩i❙B⇩j❙B⇩i {φ})))"
  | "(GammaKeep question[j,i,φ]) = 
      (λx. ¬ (∃Δ. (x =  ❙¬ (MapDone justify[i, Δ ⊢⇧+ φ]))))"
  | "(GammaKeep justify[i, ψ ⊢⇧S φ]) =  
      (λx. (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ ¬ (x =  ❙¬ ❙B⇩k❙D⇩i❙B⇩j❙B⇩i (MapEntailment S ψ φ) )))"   
  | "(GammaKeep challenge[j,i,φ]) =  
      (λx. ¬ (∃Δ. (x = ❙¬ (MapDone justify[i, Δ ⊢⇧+ φ]))) )"
  | "(GammaKeep retract[i,φ,S]) = 
      (λx. (if S=+ then
              (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ ¬ (x =  ❙¬ ❙B⇩k❙D⇩i❙B⇩j ❙¬❙B⇩i {φ}))
            else
              (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ ¬ (x =  ❙¬ ❙B⇩k❙D⇩i❙B⇩j ❙¬❙¬❙B⇩i {φ}))
     ))"


(* Gamma Update *)
(* applies PostCond *)
(* add with disjunction *)
(* also add the relevant Done formula *)
(* remove with conjunction of negation *)
fun
  GammaUpdate::"FatioL ⇒ (σ ⇒ bool) ⇒ (σ ⇒ bool)" 
  where
    "(GammaUpdate statement Γ) = 
     (λx. ((Γ x) ∨ (GammaAdd statement x) ∨ (x = MapDone statement) ))"
(*for now i removed the gammakeep*)
(*
     (λx. ((Γ x ∧ (GammaKeep statement x)) ∨ (GammaAdd statement x) ∨ (x = MapDone statement)) )"
*)
(*
problems with GammaKeep:
 instead of using GammaKeep here i can check for consistency when PreCond is applied
*)

fun
  L_GammaUpdate::"FatioL ⇒ (σ list) ⇒ (σ list)" 
  where
    "(L_GammaUpdate statement Γ) = (MapDone statement) # (L_GammaAdd statement Γ)"



term "GammaAdd assert[a,(p⇧a)]"
lemma "GammaAdd assert[a,(p⇧a)] = (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p))"
  by simp

term "L_GammaAdd assert[a,(p⇧a)]"
lemma "¬(L_GammaAdd assert[a,(p⇧a)] [] = [])"
  apply simp
  by (simp add: member_rec(2))

lemma "L_GammaAdd assert[a,(p⇧a)] [ ❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p] = [ ❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p]"
  apply simp
  (* Nitpick found a counterexample *)
  oops


lemma "List.member  ( L_GammaAdd (assert[a,(p⇧a)]) [mkHOMMLatom p]) ( mkHOMMLatom p)"
  oops

lemma "∃ l. ¬(l=[]) ∧( L_GammaAdd assert[a,(p⇧a)] [mkHOMMLatom p]) = l"
  by simp 

(*  here test GammaKeep *)

term "GammaKeep assert[a,(p⇧a)] (Map1 p⇧a)"
lemma "GammaKeep assert[a,(p⇧a)] = (λx. ∀k j. k ≠ a ∧ j ≠ a ⟶ x ≠ ❙¬❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p)"
  by simp

lemma "GammaKeep assert[a,(p⇧a)] (Map1 p⇧a)"
  apply simp
  nitpick nitpick[satisfy] oops
    (* todo extensionality problem
i want something more syntactic for Γ, but list would still have a problem because it's a list of σ *)

lemma "GammaKeep assert[a,(p⇧a)] (Map1 (¬(p⇧a)))"
  apply simp
  nitpick oops

lemma "¬ (GammaKeep assert[a,(p⇧a)]  (❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p))"
  apply simp
  by auto
    (* good, it gets removed *)


(* test GammaUpdate on one step, outside of FatioCheck *)
term "GammaUpdate assert[a,(p⇧a → q⇧a)] {}"
lemma "¬((GammaUpdate assert[a,(p⇧a)] {}) = {})"
  apply simp
  nitpick[satisfy]
  by metis


lemma "((GammaUpdate assert[a,(p⇧a)] {}) = (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p) ∨ x = MapDone assert[a,p⇧a]))"
  by simp

(* one part is missing *)
lemma "((GammaUpdate assert[a,(p⇧a)] {}) = (λx. (∀k j. (¬(k = i) ∧ ¬(j = i)) ⟶ (x =  ❙B⇩k❙D⇩i❙B⇩j❙B⇩i {p⇧a}))))"
  apply simp
  nitpick
  oops

(* with an actual Γ *)
  term "(GammaUpdate assert[a,(p⇧a)] (λx. x = (Map1 p⇧a)))"


lemma "((GammaUpdate assert[a,(p⇧a)] ( λx. x = (Map1 p⇧a)) ) = (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p) ∨ x = MapDone assert[a,p⇧a]))"
  apply simp
  nitpick oops

lemma "((GammaUpdate assert[a,(p⇧a)] ( λx. x = (Map1 p⇧a)) ) = (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p) ∨ x = MapDone assert[a,p⇧a] ∨ x=(Map1 p⇧a)))"
  apply simp
  oops
    (*todo here, check that the conjunction negation is actually what we want
check one direction at a time
might be the extensionality problem again
 *)
    (*
lemma "((GammaUpdate assert[a,(p⇧a)] ( λx. x = (Map1 p⇧a)) ) ⟶ (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p⇧a) ∨ x = MapDone assert[a,p⇧a] ∨ x=(Map1 p⇧a)))"
  apply simp
*)

(* can we also remove? (tests on GammaKeep ) *)
(*
lemma "((GammaUpdate assert[a,(p⇧a)] (λx. x = ❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p)) = (λx. (∀k j. k ≠ a ∧ j ≠ a ⟶ x = ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p) ∨ x = MapDone assert[a,p⇧a]))"
  apply simp
  by auto

lemma "((GammaUpdate assert[a,(p⇧a)] (λx. x = ❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p)) = (GammaUpdate assert[a,(p⇧a)] {}))"
  apply simp
  by auto

lemma "((GammaUpdate assert[a,(p⇧a)] {}) = (GammaUpdate assert[a,(p⇧a)] (λx. x = ❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p)))"
  apply simp
  by auto

lemma "∀ el. ((GammaUpdate assert[a,(p⇧a)] {}) el = (GammaUpdate assert[a,(p⇧a)] (λx. x = ❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p)) el)"
  apply simp
  by auto
*)

lemma "¬ ((GammaUpdate assert[a,(p⇧a)] (λx. x = ❙¬❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p)) = (GammaUpdate assert[a,(p⇧a)] (λx. x = mkHOMMLatom p) ))"
  apply simp
  nitpick
  oops
    (* maybe this fails when the preconditions are not satisfied *)


(* testing L_GammaUpdate *)

lemma "¬((L_GammaUpdate assert[a,(p⇧a)] []) = [])"
  by simp

lemma " (List.member (L_GammaUpdate assert[a,(p⇧a)] [])  ( ❙B⇩b ❙D⇩a ❙B⇩b ❙B⇩a mkHOMMLatom p))"
  oops

lemma "∀k j. k ≠ a ∧ j ≠ a ⟶ (List.member (L_GammaUpdate assert[a,(p⇧a)] [])  ( ❙B⇩k ❙D⇩a ❙B⇩j ❙B⇩a mkHOMMLatom p))"
  oops (* takes a lot of time *)


(* examples: how does Γ look like? *)
  term "(λx. x = (p⇧a))"
  value "(λx. x = (p⇧a))(q⇧a)"
  term "(λx. (x = Map1 p⇧a ))" (* use map instead of  {r⇧a} to avoid ambiguity *)
  term "❙B⇩a (Map1 r⇧a)"
  term "Map1 (p⇧a → q⇧a)"

lemma "PreCond assert[a,(p⇧a → q⇧a)] [] {}"
  apply simp
  oops

lemma "PreCond assert[a,(p⇧a → q⇧a)] [] (λx. x = (Map1 p⇧a))"
  apply simp
  oops

lemma "PreCond assert[a,(p⇧a → q⇧a)] [] (λx. x = (Map1 (p⇧a → q⇧a)))"
  apply simp
  oops

lemma "PreCond assert[a,(p⇧a → q⇧a)] [] (λx. x = ❙D⇩a❙B⇩b❙B⇩a (Map1 (p⇧a → q⇧a)) ∨ x = ❙D⇩a❙B⇩c❙B⇩a (Map1 (p⇧a → q⇧a)))"
  apply simp
  unfolding global_consequence_def
  apply simp
  by (metis Speaker.exhaust member_rec(2))



(*
datatype FatioState = state FatioDialogue "DOS list" ("<_,_>")
print_theorems (* to check if i have a function to access the 2nd element*) 
*)
(*
type_synonym FatioState = "FatioDialogue×DOS list"
*)
(* add here other stuff? like precond, postcond *)

type_synonym FatioState = "(FatioL list)×(DOS list)×(σ ⇒ bool)"

type_synonym L_FatioState = "(FatioL list)×(DOS list)×(σ list)"

fun dosFromState::"FatioState ⇒ DOS list" where
  "dosFromState (_,dos,_) = dos"

fun GammaFromState::"FatioState ⇒ (σ ⇒ bool)" where
  "GammaFromState (_,_,Γ) = Γ"

(* consistency check: 
if i add a formula, there is no empty intersection with whats already ∈Γ
check intersection is not empty
∃w. w is ∈all the formulas *)
fun GammaConsistent::"(σ ⇒ bool) ⇒ bool" where
  "GammaConsistent Γ = (∃w. ∀s. (Γ s ⟶ s w))"

term "GammaConsistent (λx. x=(Map1 (Atom p)) ∨ x=(Map1 (Neg (Atom p)))) "
(* "GammaConsistent (λx. x=(Map1 (Atom p)) ∨ x=(Map1 (Atom q))) " *)
lemma "¬ GammaConsistent (λx. x=(Map1 (Atom p)) ∨ x=(Map1 (Neg (Atom p)))) "
  apply simp
  using mneg_def by auto

term "GammaConsistent ( λx. ( x=(Map1 ((Atom p) → (Atom q)))) ∨ (x=(Map1 (Atom p))) ∨ (x=(Map1(Neg (Atom q))))  )"
lemma "¬ GammaConsistent ( λx. ( x=(Map1 ((Atom p) → (Atom q)))) ∨ (x=(Map1 (Atom p))) ∨ (x=(Map1(Neg (Atom q))))  )"
  apply simp
  by (metis mimp_def mneg_def)

(* FatioCheck: the function to apply stepwise
consistency check GammaConsistent  added
 *)
(*
([],dos,Γ)                  → success
([],[], (λx. False)) )      → failure
*)
fun FatioCheck::"FatioState ⇒ FatioState" where
  "FatioCheck ([],dos,Γ) = ([],dos,Γ)"
|"FatioCheck ((FL # FList), dos, Γ) = 
    (if (PreCond FL dos Γ)
      then (FList, (DOSUpdate FL dos), (GammaUpdate FL Γ) )
      else ([],[], (λx. False)) )"
(*    (if ((PreCond FL dos Γ) ∧ (GammaConsistent Γ))
      then (FList, (DOSUpdate FL dos), (GammaUpdate FL Γ) )
      else ([],[], (λx. False)) )"
*)

fun L_FatioCheck::"L_FatioState ⇒ L_FatioState" where
  "L_FatioCheck ([],dos,Γ) = ([],dos,Γ)"
|"L_FatioCheck ((FL # FList), dos, Γ) = 
    (if (L_PreCond FL dos Γ)
      then (FList, (DOSUpdate FL dos), (L_GammaUpdate FL Γ) )
      else ([],[], []) )"

term "L_FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], [] )"

term "FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], {} )"

lemma "FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], {} ) = ([], [], {})"
  apply simp
  oops

lemma "¬ FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], {} ) = ([], [], {})"
  apply simp
  oops

lemma "¬ FatioCheck ( ([assert[a,r⇧a]]), [], {} ) = ([], [], {})"
  apply simp
  oops  

lemma "(FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], {} ) = ([], [], {})) ⟷ (FatioCheck ( [assert[a,r⇧a]], [], {} ) = ([], [], {}))"
  apply simp
  by auto
    (* since FatioCheck only does 1 step, the computation finishes inthe same way *)

lemma "(L_FatioCheck ( ([assert[a,r⇧a], challenge[b,a,r⇧a]]), [], [] ) = ([], [], [])) ⟷ (L_FatioCheck ( [assert[a,r⇧a]], [], []) = ([], [], []))"
  apply simp
  by auto

(*what about persistence of the states? are we keeping track of the changes inthe modal logic? 
i made the theory a parameter 
*)

(* check accumulators, reduce function *)



(* todo maybe here orin FatioCheck I can also check that Γ is consistent after the PostCond *)
fun successfulResult::"FatioState ⇒ bool" where
  "successfulResult ([],dos,Γ) = 
(if (dos=[] ∧ Γ={}) then False else True)"   (* (¬ Γ={}) *) 
|"successfulResult (_,_,_) = True"

fun L_successfulResult::"L_FatioState ⇒ bool" where
  "L_successfulResult ([],dos,Γ) = 
(if (dos=[] ∧ Γ=[]) then False else True)" 
|"L_successfulResult (_,_,_) = True"

lemma "¬ successfulResult ([],[],{})"
  by  simp

lemma "¬ L_successfulResult ([],[],[])"
  by  simp

fun endResult::"FatioState ⇒ bool" where
  "endResult ([],_,_) = True"
|"endResult ((FL # FList),_,_) = False"

lemma "endResult ([],[],{})"
  by simp



(* some lemmas *)
lemma h1:
  assumes a1: "Γ ⊨ ❙D⇩a❙B⇩b❙B⇩a {r⇧a}" and
    a2: "Γ ⊨ ❙D⇩a❙B⇩c❙B⇩a {r⇧a}"
    (*  assumes a1: "∀x. Γ ⊨ ❙D⇩a❙B⇩x❙B⇩a {r⇧a}" *)
  shows "successfulResult (FatioCheck ( ([assert[a,r⇧a]]), [], Γ ))"
  apply simp
  (* Nitpick found a counterexample id there is consistency check on Gamma *)
  (* by (metis Map1.simps(1) Speaker.exhaust a1 a2 member_rec(2)) *)
  oops

lemma 
  assumes a1: "Γ ⊨ ❙D⇩a❙B⇩b❙B⇩a {r⇧a}" and
    a2: "Γ ⊨ ❙D⇩a❙B⇩c❙B⇩a {r⇧a}"
  shows  "PreCond assert[a,r⇧a] [] Γ"
  apply simp
  by (metis Map1.simps(1) Speaker.exhaust a1 a2 member_rec(2))

lemma h2:
  assumes a1: "PreCond assert[a,r⇧a] [] Γ"
  shows "(Γ ⊨ ❙D⇩a❙B⇩b❙B⇩a {r⇧a}) ∧ (Γ ⊨ ❙D⇩a❙B⇩c❙B⇩a {r⇧a})"
  apply simp
  using assms by auto

lemma  "((Γ ⊨ ❙D⇩a❙B⇩b❙B⇩a {r⇧a}) ∧ (Γ ⊨ ❙D⇩a❙B⇩c❙B⇩a {r⇧a})) ⟷ PreCond assert[a,r⇧a] [] Γ"
  apply simp
  by (metis Speaker.distinct(1) Speaker.distinct(3) Speaker.exhaust member_rec(2))

lemma 
  assumes a1: "PreCond assert[a,r⇧a] [] Γ"
  shows "successfulResult (FatioCheck ( [assert[a,r⇧a]], [], Γ ))"
  apply simp 
  (* using assms by auto *)
  oops

(* todo check this, it doesnt work *)
lemma
  assumes a1: "Γ ⊨ ❙D⇩a❙B⇩b❙B⇩a {r⇧a}" and
    a2: "Γ ⊨ ❙D⇩a❙B⇩c❙B⇩a {r⇧a}" and
    a3: "(∀k. ¬(k = b) ⟶ ((Γ ⊨ ❙D⇩b❙B⇩k ❙¬❙B⇩b {r⇧a}) ∧ (Γ ⊨ ❙D⇩b❙B⇩k❙D⇩b (❙∃Δ.(MapDone justify[a, Δ ⊢⇧+ r⇧a ])))))"
  shows "successfulResult (FatioCheck (FatioCheck ([assert[a,r⇧a], challenge[b,a,r⇧a]], [], Γ )))"
  apply simp
  oops

(* FatioCheckRec: evaluates recursively an entire dialogue *)
fun FatioCheckRec::"FatioState ⇒ bool" where
  "FatioCheckRec ([],dos,Γ) = successfulResult ([],dos,Γ)"
|"FatioCheckRec ((FL # FList), dos, Γ) = 
FatioCheckRec (FatioCheck ((FL # FList), dos, Γ))"

fun L_FatioCheckRec::"L_FatioState ⇒ bool" where
  "L_FatioCheckRec ([],dos,Γ) = L_successfulResult ([],dos,Γ)"
|"L_FatioCheckRec ((FL # FList), dos, Γ) = 
L_FatioCheckRec (L_FatioCheck ((FL # FList), dos, Γ))"




end
