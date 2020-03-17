(*<*)
theory SimulationIdea
imports Main
begin
(*>*)
text\<open>
\section{Modelling the argument}
\label{sec:Model}

This section comprises the actual modelling and simulation of the theoretical argument presented above.


We shall first look at how to best map the relevant concepts to higher order logic, i.e. answer questions
as to which kind of logic(s) to use, how to represent dictatorship and non-dictatorship, which axioms to use and so forth.

After having answered these questions, we will simulate the institution of dictatorship starting with
a rough model of the Constitution as set out in 1947 and transitioning to a model that allows for 
dictatorship without creating inconsistencies along the way. This will be done in \hyperref[subsec:HOTL]{HOTL} and \hyperref[subsec:Simulation]{Simulation}.
HOTL (higher order temporal logic) contains basic definitions of the logical framework used. Simulation holds
the actual content on the Constitution.

The section closes with a few remarks on what to avoid when modelling a concept in Isabelle/HOL.
Throughout the process of this work many ideas had to be discarded and providing some insight on the difficulties involved,
especially when it comes to weaknesses of Isabelle, might help others with similar tasks.


\subsection{Finding a suitable theoretical model}
\label{subsec:ModelGP}

\subsubsection{On representing dictatorship}
\label{subsubsec:dictatorship}

As mentioned above, once Art. V has been adequately changed, we want to introduce an amendment that implements a dictatorship.
In order to do this, it is necessary to first determine what is meant by dictatorship.

Depending on the angle you consider this question from, the answer may turn out quite differently.
In this context we are not interested in the negative connotation of despotism that comes with the term ``dictatorship" but rather
in the technical question of how a government has to be structured in order to be called a dictatorship.

According to Levinson and Balkin in a dictatorship the dictator ``combines elements of judicial,
 legislative, and executive power" with dictators being individuals or institutions%
\footnote{S.  \cite{levinson2009constitutional}, p.1805}.

Note that this definition does not require the dictator to consolidate all power but only some in each branch. There could, in fact, 
be several dictators of different types. The authors call this ``special-purpose dictatorships" and name dictatorship with respect to
war as one such type where the dictator might have the ``power to initiate war, commandeer funds and resources for war, and conduct
war at any time for any reason in any manner he pleases"%
\footnote{S.  \cite{levinson2009constitutional}, p.1806}.

For convenience, dictatorship in our case shall be simplified to be an ``all-purpose dictatorship" where a dictator is required to
have all judicial, legislative, and executive power. If a person or institution does not combine all of them, they are not a dictator.

Note that we have only considered a horizontal distribution of power. Being a federal union of states, the USA also implements a vertical 
distribution of power. The fact that at least 75\% of state legislatures have to support ratification for it to be successful is an example
of this%
\footnote{S. \ref{subsec:ArgGP}}.

Since federalism shall not play a big part in our model, we choose to distinguish between horizontal and vertical distribution
of power and define dictatorship to be the consolidation of all power on a national level, disregarding any lower levels such as states,
counties or cities.

\subsubsection{On representing time}
\label{subsubsec:time}
Since the basic idea of the argument is to introduce amendments to change the Constitution, we have to be able to 
express the notion of change.

We choose to do this via temporal logic and more specifically with an instant-based model of time as opposed to an interval-based one.
That is, we introduce different points in time and an operator
to connect those. Since we are not interested in the concept of duration, the discrete approach is enough.

Now, generally, this kind of logic would be expressed by a set $T$ of instances of time and a precedence relation $\prec$ on
$T \times T$, such that $\prec$ is both irreflexive and transitive%
\footnote{S. \cite{sep-logic-temporal},``2.1 Instant-based models of the flow of time"}.

We shall not require a relation to be transitive, however. Neither will we use modal operators to express that certain events 
will \emph{always} occur in the future or that an event will occur \emph{at some point} in the
future. The same goes for events in the past. We only require an operator @{text "\<^bold>X"} that refers to the immediate successor of an instance 
of time. The operator is denoted by @{text "\<^bold>X"} for the ``x" in ``next".

To understand why this is sensible in our case, consider the following outline of what we would like to express. Assume that 
$T=\{t_1,t_2,t_3\}$ and $t_1 \prec t_2$,$t_2 \prec t_3$ and $t_i \not \prec t_j$ for all other combinations
of $t_i$ and $t_j$ in T :

\begin{enumerate}
\item[$t_1$:]
  \begin{itemize}
  \item The Constitution from 1947 is valid.
  \item There is a division of powers and thus no dictatorship.
  \item An amendment to change Art. V (@{term "amd1"}) is proposed, but not yet ratified.\\
        Content of @{term "amd1"}: Remove the condition that only amendments can be proposed that do not alter a state's suffrage.
  \end{itemize} 
\item[$t_2$:]  
 \begin{itemize}
  \item @{term "amd1"} is ratified and therefore valid.
  \item The Constitution from 1947 is valid, except for Art. V.
  \item There is a division of powers and thus no dictatorship.
  \item Art. V does not require proposed amendments to leave states' voting rights untouched.
  \item An amendment to introduce dictatorship (@{term "amd2"}) is proposed, but not yet ratified.\\
        Content of @{term "amd2"}: Give all rights of Congress and the Courts to the President.
  \end{itemize} 
\item[$t_3$:] 
 \begin{itemize}
  \item  @{term "amd2"} is ratified and therefore valid.
  \item All power is with the President. With the abolished division of powers there is a dictatorship.
  \end{itemize} 
\end{enumerate}

\noindent The basis for changes in $t_2$ is set out with @{term "amd1"} at $t_1$. Likewise the basis for changes in $t_3$ is set out with @{term "amd2"} at $t_2$.
At each $t_i \in T$ the furthest we look into the future is the immediate successor, thus we do not need $\prec$ to be transitive.

In addition to it not being necessary, there is another reason to omit transitivity as requirement for the precedence relation.
For a formula @{text "\<phi>"}, we would like @{text "\<^bold>X\<phi>"} to be valid at some point of time $t$ iff for any $t'$, s.t. $t \prec t'$, holds:
@{text "\<phi>"} is valid at $t'$.\\
If $\prec$ were transitive, then @{text "\<^bold>X\<phi>"} would not mean ``@{text "\<phi>"} is valid at the next instance after $t$", but
 ``@{text "\<phi>"} is valid at all instances after $t$". If not used very carefully, this could easily lead to inconsistencies. After all,
amendments do not necessarily stay valid once ratified%
\footnote{S. \cite{usconst2017}: Amend.XVII, the prohibition of intoxicating liquors, was repealed by Amend. XXI, \S.1}.
Since we do not need a transitive relation $\prec$, it is advisable to avoid it altogether.

\subsubsection{On representing Art. V}
\label{subsubsec:art5}

The concepts actually mapped onto HOL are only a fraction of what is written in the Constitution.
This is because representing everything would go beyond the scope of this work. Since Art. V is of particular importance to the argument,
it will not be omitted but we shall concentrate on the relevant bits.

\noindent Recall that the three concepts addressed are:

\begin{enumerate}
\item \textbf{proposition of amendments} \\
  with support of
  \begin{enumerate}[label*=\arabic*.]
  \item two thirds of both houses of Congress
  \item \textg{two thirds of State Legislatures requesting a Convention}
  \end{enumerate}
\item \textbf{ratification of amendments}   \\
  with support of
  \begin{enumerate}[label*=\arabic*.]
  \item \textg{three fourths of State Legislatures}
  \item \textg{three fourths of State Conventions}
  \end{enumerate} 
\item \textbf{entrenchment}\\
  protecting
  \begin{enumerate}[label*=\arabic*.]
  \item \textg{until 1808: Art. I, \S9, cl.1 3 , cl.4}
  \item Art. I,\S3, cl.1, Amend. XXVII, cl.1
  \end{enumerate}
\end{enumerate}

\noindent We shall not represent 1.2.,2.1.,2.2., or 3.1. for the following reasons:
\begin{itemize}
\item  1.2.,2.1.,2.2. are part of the federal system which is not essential to the argument. 
\item 3.1. may be ignored since 1808 had long since passed when Gödel studied the Constitution.
\end{itemize}


\noindent The remaining points will be represented as follows:
\begin{itemize}
\item  For 1. and 1.1. there will be a predicate
@{term "is_prop"} for potential amendments that will only be true if the amendments have the support of Congress to be proposed.
\item In analogy to @{text "is_prop"}, there will by a predicate @{term "is_rat"} that can only be true if the amendments have support to be ratified.
What this support looks like shall not be specified further. Predicate @{term "is_rat"} will serve to express 2.
\item To express 3. and 3.2. there will be a predicate @{term "maint_suf"} for amendments which shall be true
iff the amendments would maintain equal suffrage in Senate for each state.
\end{itemize}

\<close>
(*<*)
end
(*>*)