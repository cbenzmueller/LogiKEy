section \<open>Introduction to Isabelle\<close>
(*<*)
theory Introduction
imports Main

begin
(*>*)

subsection \<open>Basics\<close>


text \<open>Text blocks for in-line documentation (in a way related to literal programming)
are started with the @{command "text"} command, followed by the text to write
in the @{text "\<open> ... \<close>"} brackets. You can also structure the document using
commands such as @{command "section"} or @{command "subsection"} etc., just
like in Latex.\<close>

text \<open>Comments (like in programming languages) are written in Isabelle between (* and *).
As an example, the following comment will not be interpreted by Isabelle in any sense:\<close>

(* i am a comment, ignore me. or not. whatever *)

text \<open>See? Probably you did not see anything, since comments are also not processed by the
PDF generation. Visible in-line comments can be written using the comment symbol @{text "\<comment>"} after
some term or formula (in the same line), like this:\<close>

term "a" \<comment> \<open>Some atomic term variable\<close>

text \<open>We just wrote down a term symbol @{term "a"} and put an in-line
comment right after it.\<close>


text \<open>Speaking of terms, we will now introduce terms, formulas, types, etc. 
that you will need for using Isabelle.\<close>

paragraph \<open>Terms\<close>
text \<open>
  We can write logical formulae and terms in the usual notation.
  Connectives such as @{text "\<not>"}, @{text "\<or>"}, @{text "\<and>"} etc. can be typed using the backslash
  @{text "\\"} followed by the name of the sign. I.e. @{text "\\not"} for @{text "\<not>"}.
  Note that during typing @{text "\\not"} at some point there will be a pop-up menu
  offering you certain auto completion suggestions that you can accept by
  pressing the tab key.
\<close>

text \<open>Some examples:\<close>

term "a" \<comment> \<open>atomic term as above\<close>
term "a \<and> b" \<comment> \<open>conjunction\<close>
term "a \<longrightarrow> b" \<comment> \<open>material implication\<close>
term "\<forall>x. p x" \<comment> \<open>universal quantification\<close>

text \<open>In higher-order logic, formulas are just terms of a specific type,
called @{type "bool"} in Isabelle. Every term above can also be seens as a
formula:\<close>

prop "a" \<comment> \<open>atomic formula\<close> 
prop "a \<and> b" \<comment> \<open>conjunction\<close>
prop "a \<longrightarrow> b" \<comment> \<open>material implication\<close>
prop "\<forall>x. p x" \<comment> \<open>universal quantification\<close>
text \<open>By using the @{command "prop"} command, we can tell Isabelle to interpret
the input as a formula instead of any term. In the case of the last three terms,
this does not make any difference since we use Boolean connectives. So Isabelle
will figure itself out, that the symbols @{term "a"}, @{term "b"} are actually
atomic formulas. However, this is not necessarily true for the first example. The
symbol @{term "a"} could be of any type. So Isabelle will not fix its type,
but instead give it a type placeholder (referred to as "type variables").\<close>

paragraph \<open>Types\<close>
text \<open>
  All terms (and also constant symbols, variables etc.) are associated
  a type. The type @{type "bool"} is the type of all Boolean-values objects
  (e.g. truth values and formulas). There are many pre-defined types in 
  Isabelle, e.g. for sets, functions, numbers, etc. We will mainly
  focus on formulas and possibly individuals
  (objects from the universe of discourse).
  A type for individuals, often denoted @{text "i"}, does not exist
  in Isabelle yet.
  New types can be inserted at will using the @{command "typedecl"} command:
\<close>

typedecl "i" \<comment> \<open>Create a new type i for the type of individuals\<close>

text \<open>
  We can now play a bit around with types. The @{command "typ"} command
allows us to write down types, just to try it out (as for @{command "term"},
writing down types does not change the state of the document. It is just
a more sophisticated way of writing text for now).
Function types are written using the function type constructor @{text "\<Rightarrow>"}.
\<close>

typ "i \<Rightarrow> i" \<comment> \<open>The type of functions from objects of type i to objects
                 of type i\<close>

typ "i \<Rightarrow> bool" \<comment> \<open>The type of a predicate on objects of type i\<close>

text \<open>
  Terms can be assigned a specific type by the user. This is done using
  the @{text "::"} command, written is postfix notation. This can be useful
  if you want to restrict the type of a term, a constant symbol or a variable
  and hence forbid Isabelle to figure the most general type on its own.
\<close>

term "a" \<comment> \<open>a is a variable of some type\<close>
term "a :: i" \<comment> \<open>a is a variable of type i\<close>
term "p :: i \<Rightarrow> bool" \<comment> \<open>p is a predicate\<close>


paragraph \<open>Constants\<close>
text \<open>
  New atomic symbols can be defined using the @{command "consts"} keyword.
  You need to specify the type of the constant explicitly, using the
  @{text "::"} operator, just like above:
\<close>

consts "a" :: "bool"
       "b" :: "bool"

text \<open>
  You can list as many constant symbols as you want.
  Note that this will change the state of the system (unlike commands
  such as @{command "typ"}, @{command "term"} and @{command "prop"}
  that just allowed us to scribble a little bit around.

  From now on, there exist
  atomic symbols (atomic propositions) @{const "a"} and @{const "b"}.
\<close>

text \<open>
  Using the constants above, we can write down more complex formulas:
\<close>

prop "a \<and> b"
prop "(a \<and> b) \<longleftrightarrow> (\<not>(\<not>a \<or> \<not>b))"
prop "\<not>\<not>a"

subsection \<open>Exercises\<close>

paragraph \<open>Exercise 1.\<close>
text \<open>Before we start proving logical formulae, we become acquainted with the basic logical connectives, the quanti-
fiers and the remaining components of a logical formula. To that end, please give
appropriate formalizations of the following expressions stated in natural language.
You may freely choose appropriate names for variables and further identifiers.\<close>

text \<open>
  \<^item> ”The ship is huge and it is blue.”
  \<^item> ”I’m sad if the sun does not shine.”
  \<^item> ”Either it’s raining or it is not.”
  \<^item> ”I’m only going if she is going!”
  \<^item> ”Everyone loves chocolate or ice cream.”
  \<^item> ”There is somebody who loves ice cream and loves chocolate as well.”
  \<^item> ”Everyone has got someone to play with.”
  \<^item> ”Nobody has somebody to play with if they are all mean.”
  \<^item> ”Cats have the same annoying properties as dogs.”
\<close>

subparagraph \<open>Solutions to Ex. 1\<close>
text \<open>\<close>

text \<open>
  \<^item> ”The ship is huge and it is blue.”\<close>
text \<open>Introduce constants for ship, huge and blue of appropriate type:\<close>

consts ship :: i
       huge :: "i \<Rightarrow> bool"
       blue :: "i \<Rightarrow> bool"

text \<open>Now we can express the sentence as \<close>
prop \<open>huge ship \<and> blue ship\<close>

text \<open>
  \<^item> ...
\<close>



(*<*)
end
(*>*)