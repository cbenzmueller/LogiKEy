(*<*)
theory Introduction
imports Main
begin
(*>*)
text\<open>
\section{Introduction}
\label{sec:Intro}

This thesis aims at modelling parts of the US Constitution with higher order logic (HOL) in theorem prover \textsc{Isabelle/HOL}
in order to verify the possibility of a legal dictatorship in the USA.
The basis for the argument is a notorious anecdote on how, at his US citizenship hearing, logician Kurt Gödel informed the judge that the US Constitution was in fact
faulty and allowed for the erection of a constitutional dictatorship.
We shall explore both the argument Gödel might have had in mind when saying this and a verified version of the supposed argument, modelled on the computer.

Before delving into the argument, we give a short \hyperref[sec:Framework]{overview} on the tools used, including an introduction to Isabelle/HOL and the 
manner in which we are going to use it.

The ensuing  \hyperref[sec:Arg]{section} of this work is concerned with Gödel's supposed argument on the 
Constitution's shortcomings. This also encompasses a quick overview of the Constitution and a more detailed consideration of the articles
most relevant to the argument.

After having laid a theoretical foundation, we will devise and implement a HOL model for the argument in the  \hyperref[sec:Model]{main} part
 of this work.
Being mindful of the technical restrictions, we shall choose a suitable logic embedded into Isabelle's HOL-language and map the relevant parts of the Constitution to
their equivalents in the proposed logic.
Having succeeded in this, we shall prove that it is possible to build a dictatorship without violating the Constitution, thus verifying Gödel's argument.
The main part concludes with a few remarks on what to avoid when modelling a concept with Isabelle/HOL.
 
The \hyperref[sec:Outlook]{last section} will present a few further problematic properties of the US Constitution in addition to the one modelled in the main part.
We then name a few questions not yet addressed and conclude the thesis.

For convenience, the terms ``US Constitution" and ``(the) Constitution" shall be used interchangeably.



\<close>
(*<*)
end
(*>*)