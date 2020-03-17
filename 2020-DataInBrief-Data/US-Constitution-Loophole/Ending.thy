(*<*)
theory Ending
imports Main
begin
(*>*)
section \<open>{Outlook \label{sec:Outlook}}\<close>
text\<open>
This section aims at providing an outlook on which questions might be studied next as well as presenting the limits of this work
by addressing unanswered questions.

The first point to mention here is that no records were found that attest to the argument Gödel himself devised.
It seems that there simply are no first-hand records on Gödel's reservations concerning the Constitution. Nonetheless, the author
has not exhausted all sources due to a lack of availability of some of them in Berlin. Most notably, there are the ``Kurt Gödel Papers"%
\footnote{S. \cite{various1985papers}}
 and
the ``Kurt Gödel Papers on microfilm"%
\footnote{S. \cite{brill}} 
respectively. The latter are a selection of the former but more widely available since they can be accessed wherever the
microfilm is available. The full collection is only available at the Princeton University Library.
They contain personal notes amongst other documents. These might help in retracing Gödel's thoughts.
It should be noted that fellow scientists with access to the microfilms could not find a sketch of the argument. However, the collection 
at the Princeton University Library also contains his correspondence with Morgenstern and as we have seen in \ref{subsec:ArgGodel} Gödel would turn to Morgenstern with
questions concerning the hearing%
\footnote{S. \cite{morgenstern1971oskar}}.
 Since their correspondence was not published in ``Kurt Gödel - Collected Works"%
\footnote{This is a collection of Gödel's scientific work in five volumes, the fifth containing his correspondence with persons
of surnames starting with H-Z, see \cite{godel2003collected}.}
one would have to turn to the collection in Princeton to examine those.


In addition to faults that Gödel himself might have found with the Constitution, it would be interesting to study and potentially formalize 
other problems of the Constitution from a logician's perspective. There seem to be both logical problems\footnote{S. \cite{belenky2004}}
and problems with respect to content, for example when it comes to ensuring a balanced distribution of powers%
\footnote{S. \cite{guerra2013godel}, IV.}. In terms of logical problems, the above mentioned formalization of \emph{lex posterior} would
be of particular interest, given that it is a widely used principal in law.

With respect to the argument formalized in this work and its connection to the Frame Problem, we chose to enlist all necessary axioms
on effects and non-effects.  Formalizing the argument with the currently available solutions for the Frame Problem\footnote{S. \cite{sep-frame-problem}, 
``5.The Frame Problem Today"} remains to be done as it might lead to new insights.

This work only dealt with the contents of the Constitution relevant to the argument formalized. Analysing and representing more of its contents
will be the next step in meeting growing demands in automated legal reasoning.

When it comes to formalizing legal concepts in general the collaboration of logicians and legal scholars is essential
to achieve better results. Given that the problems presented above
 are in nature interdisciplinary they should also be solved in an interdisciplinary context.

\<close>


section \<open>{Conclusion \label{sec:Conclusion}}\<close>

text\<open>
In the course of this work we delved into an argument on how a legal dictatorship could be instantiated
on the basis of the US Constitution.

The starting point was an anecdote on how Gödel tried to teach his examiner at the citizenship hearing about the potential
for a dictatorship in the USA based on a fault of the Constitution.

Not being able to locate a document on Gödel's own thoughts concerning this flaw, we concentrated on an argument by Guerra-Pujol%
\footnote{S. \cite{guerra2013godel}}. The basic idea is to amend Art. V which entrenches some parts of the Constitution to enable the introduction
of another amendment that dissolves the separation of powers and installs a dictator.

This argument was then formalized with Isabelle/HOL using a simple temporal logic with different instances of time to represent the 
stages the Constitution passes through until it allows for a dictatorship.

Having successfully verified the validity of the argument, we turned to lessons learned throughout the process. Among these, there were some
directly connected to Isabelle and its weaknesses and thus of a technical nature, but also some that were of theoretical nature
and in part warrant further research.

The author was a little sad to not have found Gödel's original argument but greatly enjoyed looking for it in letters and diary entries
and definitely learned a lot throughout the process of modelling and verifying the argument.
\<close>

(*<*)
end
(*>*)
