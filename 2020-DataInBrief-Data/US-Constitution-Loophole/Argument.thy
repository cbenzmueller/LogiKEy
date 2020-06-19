(*<*)
theory Argument
imports Main
begin
(*>*)
text\<open>
\section{On the argument used}
\label{sec:Arg}


\subsection{Finding G\"odel's argument}
\label{subsec:ArgGodel}
Following his permanent employment at the \textit{Institute for Advanced Study} (IAS) in Princeton, Gödel applied 
for US citizenship in 1947\footnote{See \cite{dawson1997logical}, p.159 a. p.179f}.

As part of his naturalization process he had to attend a hearing during which a judge would ask questions on topics such as the governmental
 system or the history of the United States.
Gödel was accompanied by two fellow scientists at the IAS: economist Oskar Morgenstern and physicist Albert Einstein. The two served as character 
witnesses.

There are different accounts of this event. Biographers Dawson, Wang and Yourgrau all present the anecdote, albeit somewhat differently
\footnote{See \cite{dawson1997logical},p.179f and \cite{wang1987reflections}, p.115f and \cite{yourgrau2006world}, p.98f }.
 Dawson refers to an interview with Morgenstern's wife and a diary entry, but also mentions that he hoped to refer to an account by Morgenstern
himself but that he couldn't locate it\footnote{S. \cite{dawson1997logical}, p.300}.
Wang refers to an obituary by Zemanek\footnote{S. \cite{wang1987reflections}, p.115}
and Yourgrau refers to Dawson\footnote{S. \cite{yourgrau2006world}, p.190}.

Gödel himself mentions the hearing in letters to his mother
but doesn't go into much detail\footnote{S. \cite{godel1947briefe}, \emph{Dec 9 1947}: Gödel mentions that he will soon be US citizen.\emph{
Jan 11 1948}: Gödel mentions the hearing and explains shortly who was there and why.
\emph{16 Mar 1948}: Gödel mentions that he hasn't gotten a 
response concerning his application yet.
\emph{May 10 1948}: Gödel describes his citizenship oath. This is more detailed than the information on
the preceding hearing}.

Morgenstern's account has since been published by the IAS.
The following will recount the incident according to Morgenstern since, unlike Dawson, Morgenstern attended the hearing himself%
\footnote{The following paragraphs on the hearing all refer to \cite{morgenstern1971oskar} unless clearly stated otherwise}.

Being a very thorough person, Gödel prepared for his citizenship hearing months in advance. He studied US history and law from the first settlers 
and Native American tribes to the exact border between Princeton Borough and Princeton Township to the US Constitution. Apparently Gödel would 
address several of his questions to Morgenstern and the two of them would discuss these matters together.

Morgenstern also mentions conversations about these topics in his diaries from 1947%
\footnote{S. \cite{morgenstern2016tagebuch},  \emph{Feb 26 1947},  \emph{Mar 3 1947} and  \emph{Dec 7 1947} }, 
unfortunately without going into much
detail. For example, in his entry from February 26 he says he would be with the Gödels the following day and that most certainly Gödel
would have his notebook and a lot of questions waiting. The next diary entry from March 3 tells us that Morgenstern had in fact been with the 
Gödels twice
but only mentions conversations about other topics, nothing about the pending hearing.

Eventually Gödel seemed to have found a fault with the Constitution, a fault that would allow for the erection of a fascist regime. He was most 
distressed and could not be calmed by either Morgenstern or Einstein. They told him that questions asked would not require an in-depth analysis 
of the Constitution and tried to dissuade him from mentioning the matter altogether.

At the hearing the judge first asked Einstein and Morgenstern whether they considered Gödel to be a good potential citizen. Being his character 
witnesses they confirmed.
The judge then turned to Gödel and the following dialogue unfolded%
\footnote{This direct quote from \cite{morgenstern1971oskar} contains some misspellings. For better readability they are listed here: 
\emph{Godel}-\emph{Gödel},\emph{examinor}-\emph{examiner}}:
\begin{quote}
\setlist[description]{font=\normalfont}
\begin{description}%{The Examinor}
\item[The Examinor]: ``Now, Mr. Godel, where do you come from?"
\item[Gödel]: ``Where I come from? Austria."
\item[The Examinor]: ``What kind of government do you have in Austria?"
\item[Gödel]: ``It was a republic, but the constitution was such that it finally was changed into a dictatorship."
\item[The Examinor]: ``Oh! This is very bad. This could not happen in this country."
\item[Gödel]: ``Oh, yes, I can prove it."\\
 $[\ldots]$
\item[[The Examinor]: ]``Oh God, let's not go into this."
\end{description}
\end{quote}
%TODO: quoting like this ok? I.e. should I change anything from original version. Also: currently quote not recognisable as quote in PDF.

\noindent Evidently, the examining judge was not interested in hearing Gödel's reasoning behind such a statement. What was probably good for
 Gödel's successful
naturalization is rather inconvenient for us since it leaves us without a record of Gödel's argument.

As mentioned above, while Morgenstern does write about conversations with Gödel in his diaries of 1947, the topics he mentions do not expand to 
Gödel's reservations about the Constitution.\\
Furthermore none of the biographers seem to have found a record of the argument. We are thus forced to speculate on what it might have been.

%TODO: description legal scholar ok here?
We shall use an argument provided by legal scholar Enrique Guerra-Pujol as basis for our further reasoning. In his article
 ``Gödel's Loophole" \footnote{S. \cite{guerra2013godel}} he names a few problems with the US Constitution 
and goes into detail on one of them that is concerned
with self-referentiality.\\
Considering that self-referentiality was at the very heart of the proof for the Incompleteness Theorem%
\footnote{S. \cite{smullyan1992godel}, chapter ``I The General Idea Behind Gödel's Proof"} Guerra-Pujol's argument
shares at least one feature with Gödel's work even if it is not what Gödel himself had in mind.

\label{unlikely}Also, as will be shown below, the argument requires very unlikely conditions to be fulfilled which might be what Morgenstern%
\footnote{S. \cite{morgenstern1971oskar}}
is referring to when he writes
\begin{quote}
I told him that it was most unlikely that such events would ever occur, even assuming that he was right[...].
\end{quote}

\noindent With this in mind, we choose to work with Guerra-Pujol's argument. Having decided on a basis for the Consitution's model,
 we shall now take a closer look at that argument.


\subsection{Argument according to Guerra-Pujol}
\label{subsec:ArgGP}

To understand Guerra-Pujol's reasoning, let us first consider the US Constitution and its structure.

The Constitution is made up of seven original articles written in 1787 and 27 amendments that followed later. Note that at the time of Gödel's
hearing in 1947 there were only 21 amendments with the twenty-second having been proposed but not yet ratified\footnote{S. \cite{usconst2017} for
 a list of all articles and amendments, as well as notes on which articles were affected by which amendments. }.
Here is a broad overview on the original articles' contents:

\begin{center}
\begin{tabularx}{0.8\textwidth}{c|X}
 Article & Content \\
\hline
\rcolor
I & Legislative \\
II & Executive \\
\rcolor
III & Judiciary \\
IV & States' relations\\
\rcolor
V & Amendments\\
VI & Prior Debts and National Supremacy \\
\rcolor
VII & Ratification of the Constitution
\end{tabularx} 
\end{center}

\noindent\textbf{Articles I-III} specifiy the rights of the governmental branches, by which institutions they are represented, how elections are to 
be held and so forth.

\noindent\textbf{Article IV} sets up the federalistic system by which each state has legislative sovereignty over its own affairs, but also manages
interstate relations. In this context, state is to mean a member of the United States of America.

\noindent\textbf{Article V} describes the process of changing or  amending the Constitution. This article is of particular importance to the
 argument. It will therefore be considered in more detail later.

\noindent\textbf{Article VI} determines that any state's debts are not changed by the ratification of the Constitution. Furthermore, it states 
that the Constitution shall be the ``supreme Law of the Land" and any official representative has to swear an oath of support.

\noindent\textbf{Article VII} finally stipulates that the Constitution will be ratified through the ratification of nine states. The ratification 
by all thirteen original states is not necessary for the Constitution to take effect.
\\

\noindent Here is the outline of the actual argument:\\
As it is, the Constitution does not allow for a dictatorship under one dictator since there is a division of powers into legislative, executive
and judiciary, all of which have unique rights and responsibilities.

This means that in order to set up a dictatorship the Constitution needs to be amended first. How can this be done? To answer this
question one needs to consider Article V\footnote{This is a literal quote, including dated spelling. The arrangement in separte
 paragraphs was added for better readibilty. The original is one paragraph.}:

\begin{enumerate}[label=(\arabic*)]
\item The Congress, whenever two thirds of both Houses shall deem it necessary, shall propose Amendments
 to this Constitution,
\item  or,
on the Application of the Legislatures of two thirds of the several States, shall call a Convention for proposing Amendments, 
\item which, in either Case, shall be valid to all Intents and Purposes,
as Part of this Constitution, when ratified by the Legislatures of three fourths of the several States, 
\item or by Conventions in three fourths thereof, as the one or the other Mode of Ratification may be proposed by the Congress;
\item Provided that no Amendment which may be made prior to the Year One thousand eight hundred and eight shall in any
Manner affect the first and fourth Clauses in the Ninth Section of the first Article;
\item  and that no State, without its
Consent, shall be deprived of its equal Suffrage in the Senate.
\end{enumerate}

\noindent There are three concepts addressed in this article:
\begin{itemize}
\item The \textbf{proposition} of amendments (paragraphs 1 and 2)
\item The  \textbf{ratification} of amendments (paragraphs 3 and 4)
\item \textbf{Entrenchments} 
of other parts of the Constitution (paragraphs 5 and 6)
\end{itemize}

\noindent An amendment may be proposed either by Congress or by a specifically held Convention. In the first case at least two thirds of both 
houses of the Congress, i.e. the House of Representatives and the Senate, need to support the proposition. In the second case, at least two 
thirds of all states' legislatures need to request such a Convention. 

As to the ratification, the conditions for ratification are similar to but not quite the same as for proposition. There are two possible methods
and Congress decides which method shall be used. Either a proposed amendment is ratified by at least three fourths of all states' legislatures or
special State Conventions are held for each state, three fourths of which need to ratify the amendment.

With regard to ``entrenchments", let us first clarify what is meant by the term. There are different definitions of what ``entrenchment"
 of a rule means. In the broadest sense an entrenched rule is ``any rule that is difficult
 to alter"\footnote{S. \cite{barber2016we}, p.327}. Therefore an ``entrenchment rule" is a rule causing some rule to be entrenched.
 Art. V is thus an entrenchment both of Art. I, \S  9, cl.1, cl.4
and of the article regulating states' votes in Senate, namely Art. I, \S 3, cl.1%
\footnote{\usc{I}{3}{1}:``The Senate of the United States shall be composed of two Senators from each State, chosen by the 
Legislature thereof, for six Years; and each Senator shall have one Vote."}.

The first two clauses regulate slavery%
\footnote{\usc{I}{9}{1}:``The Migration or Importation of such Persons as any of the States now existing shall think proper to admit,
 shall not be 
prohibited by the Congress prior to the Year one thousand eight hundred and eight, but a Tax or duty may be 
imposed on such Importation, not exceeding ten dollars for each Person."}%
 and how taxes are raised%
\footnote{\usc{I}{9}{4}:``No Capitation, or other direct, Tax shall be laid, unless in Proportion to the Census or 
Enumeration herein before directed to be taken."}
 but shall not concern us since they were only entrenched up until 1808. We are interested in the Constitution Gödel was working with
and that is the Constitution from 1947. Hence the entrenchments concerning these clauses were not valid anymore.

Art. I, \S 3, cl.1 was amended by Amend. XXVII%
\footnote{\uscx{XXVII}{1}{}:``The Senate of the United States shall be composed of two Senators from each State, elected by the
 people thereof, for six years; and each Senator shall have one vote. The electors in each State shall have the qualifications
 requisite for electors of the most numerous branch of the State legislatures"}
, ratified in 1913, which is thus relevant for us as well. The articles determine
that each State shall have two representatives
in Senate, each having one vote. So, according to Art. V, an amendment may not change either of these clauses.\\

\noindent In summary, Art V. gives instructions on how to propose and ratify an amendment with the additional
condition of an amendment not infringing on a state's votes in Senate.

This means that Art. V poses an obstacle on the path to legal dictatorship via amendments. Luckily, 
Art. V does not protect itself from amendment.\\
One could thus institute a dictatorship by following these steps:
\begin{enumerate}
\item Propose an amendment to remove the entrenchment clause from Art. V.
\item Ratify this amendment.
\item Propose an amendment to institute a dictatorship, e.g. by depriving Congress and all courts of their rights and
 granting those rights to the President.
\item Ratify this amendment and behold the marvellous institution that is presidential dictatorship created at your hands.
\end{enumerate}

\noindent Now, while this sounds rather simple, there are a few remarks that should be made at this point.

Firstly, both proposition and ratification require large majorities in Con-gress and states' legislatures.
It his highly unlikely that any state legislature would ratify an amendment depriving Art. V of its
entrenchment clause. After all, it protects all states' suffrage in Senate.
So, while this is, in theory, a feasible method of setting up a dictatorship, it would most likely
not come to pass. This is the improbable condition mentioned above in \ref{subsec:ArgGodel}, which Morgenstern may have 
been referring to in his account of the hearing.

Secondly, if we assume that a majority of Congress and state legislatures do support the anti-entrenchment
amendment, then the amendment is actually unnecessary. This is because Art. V only prohibits the decrease of a state's
suffrage when said state does not give its consent. Assuming that all states support the anti-entrenchment
amendment, they would probably also support an amendment that attacks their suffrage directly.

Having made these remarks, we do choose to work with the argument presented above. Albeit very unlikely,
it provides a possible path to constitutional dictatorship. Also it makes use of the fact that Art. V. 
does not refer to itself which is a neat feature in an argument supposed to mimic one by Gödel whose
most famous work has self-referentiality at its heart%
\footnote{S. \cite{smullyan1992godel}, chapter ``I The General Idea Behind Gödel's Proof"}.

\<close>
(*<*)
end
(*>*)