# Universal Logical Reasoning
This course is part of the overall lecture course "Logic in AI" at Zhejiang University, 2020; for more information see the overall lecture course [website](https://www.xixilogic.org/events/2020/08/course-logic-in-ai/).

### Abstract
Knowledge representation and reasoning applications in computer science, AI, philosophy and math typically employ very different logic formalisms. Instead of a \single logic that serves it all” (as envisioned already by Leibniz) an entire \logic zoo” has been developed, in particular, during the last century. Logics in this zoo, e.g., include modal logics, conditional logics, deontic logics, multi-valued logics, temporal logics, dynamic logics, hybrid logics, etc. In this lecture course I will introduce, discuss and demonstrate a recent attempt at a meta logical approach to universal logical reasoning that addresses this logical pluralism. The core message is this: While it might not be possible to come up with a universal object logic as envisioned by Leibniz, it might in fact be possible to have a universal meta logic in which we can semantically model, analyze and apply various species from the logic zoo. I will argue and demonstrate that classical higher order logic (HOL) [3] is particularly suited to serve as such a universal meta logic, and that existing reasoning tools for HOL can fruitfully be reused and applied in this context.

The lecture course will introduce HOL and the SSE technique, provide some hands-on introduction to Isabelle/HOL, study and demonstrate some concrete semantical embeddings of non-classical in HOL, and conduct practical exercises regarding the application of the SSE technique in philosophy, mathematics and artificial intelligence, including, normative reasoning and machine ethics. As far as time permits, the course will also explain and train the application of the LogiKEy methodology for designing normative theories of ethical and legal reasoning.

## Course Material
- [Presentation Slides](slides); this directory will be updated
- [Isabelle/HOL system](https://isabelle.in.tum.de); please install this system prior to the first course (see also this [Isabelle/HOL tutorial](https://isabelle.in.tum.de/dist/Isabelle2020/doc/tutorial.pdf) and further relevant documents at this [website](https://isabelle.in.tum.de/documentation.html))

## Data Sets
- [LogiKEy Workbench](www.logikey.org): Deontic Logics, Logic Combinations and Expressive Ethical and Legal Reasoning (Isabelle/HOL Dataset) (Christoph Benzmüller, Ali Farjami, David Fuenmayor, Paul Meder, Xavier Parent, Alexander Steen, Leendert van der Torre, Valeria Zahoransky), In Data in brief, Elsevier, number 106409, pp. 1-15, 2020. [doi](https://www.sciencedirect.com/science/article/pii/S2352340920312919) [url]

## Reading Material

### LogiKEy Workbench (dataset of formalized knowledge): 

Flexible, Pluralistic Foundations for Legal and Ethical Reasoning, Metaphysics and Maths

For further information on LogiKEy see the 
- related [scientific article](https://arxiv.org/abs/1903.10187) in "Artificial Intelligence" [(doi)](https://doi.org/10.1016/j.artint.2020.103348), and the 
- related [data article](https://www.sciencedirect.com/science/article/pii/S2352340920312919) in "Data in brief".

The LogiKEy Workbench also maintains selected datasets in 
- [Computational Metaphics](Computational-Metaphysics) and
- [Foundations of Maths](Maths-Foundations)

All these datasets utilize the universal meta-logical reasoning approach in which various object logics (and their combinations) are shallowly embedded in classical higher-order logic.
