# Categorical Combinators


### Who cares about Categorical Combinators?

Historically, there seem to be have been three main reasons to study categorical combinators:

1) Target language for implementation

   > ...roughly λ-calculus is well-suited for programming, and combinators (of Curry, or those introduced here) allow for implementations getting rid of some difficulties in the scope of variables. Indeed we intend to develop implementations of functional programming languages based on categorical combinators, which we introduce now, letting them arise from the known principle that a formal semantic description yields a compilation. Our syntactic equivalences induce equivalences at the model level. The paper is intended as a mathematical foundation
   for developing implementations of functional programming languages based on a "categorical abstract machine," as developed in a companion paper...
   >
   > *—P.-L. Curien ([1985, Typed Categorical Combinatory Logic](https://link.springer.com/chapter/10.1007/3-540-15198-2_10))*

2) Intermediary calculus between λ-calculus and CCCs

   > Our main aim is to present the connection between λ-calculus and Cartesian
   > closed categories both in an untyped and purely syntactic setting. More specifically
   > we establish a syntactic equivalence theorem between what we call categorical combinatory
   > logic and λ-calculus with explicit products and projections, with β and
   > η-rules as well as with surjective pairing. "Combinatory logic" is of course inspired
   > by Curry's combinatory logic, based on the well-known S, K, I. Our combinatory
   > logic is "categorical" because its combinators and rules are obtained by extracting
   > untyped information from Cartesian closed categories (looking at arrows only, thus
   > forgetting about objects). Compiling λ-calculus into these combinators happens to
   > be natural and provokes only n log n code expansion. Moreover categorical combinatory
   > logic is entirely faithful to β-reduction where combinatory logic needs
   > additional rather complex and unnatural axioms to be. The connection easily
   > extends to the corresponding typed calculi, where typed categorical combinatory
   > logic is a free Cartesian closed category where the notion of terminal object is
   > replaced by the explicit manipulation of applying (a function to its argument) and
   > coupling (arguments to build datas in products).
   >
   > *—P.-L. Curien (1986, Categorical Combinators)*

3) λ-calculus-lookalike that internalizes substitution

   > The theories of classical combinators and λ-calculus both have the
   > same purpose: to describe some of the most primitive and general properties of
   > operations and of their combinations. They are in fact abstract programming
   > languages: higher-order level functional languages can be translated in these theories
   > in order to study strategies, parameter passing problems,...the pure λ-calculus,
   > λ(V), is a formal system built with a set V of variables and two operations: the
   > abstraction of a variable in a term which constructs a new function “of this variable”,
   > and the application which applies a function to an argument. The meaning of its
   > operational rule, called β-reduction, is that the value of a function applied to an
   > effective parameter is obtained by replacing, in the body of this function, all the
   > occurrences of the formal parameter by copies of this effective argument.
   >
   > This substitution of variables by terms, which is only described in the metalanguage,
   > is not straightforward: it has to avoid variable name conflicts. This is the
   > main problem in λ-calculus implementations.
   >
   > λ(V) is also endowed with one other rule: the η-rule which says, roughly speaking,
   > that two functions which have the same value for any argument, are equal.
   > CL, the Combinatory Logic, is a way of doing computations without using bound
   > variables. Functions are built up from some primitive ones (classically, the
   > combinators S and K) and the application operation. Therefore complications of
   > the λ-calculus’ substitution are avoided but the intuitive clarity of λ-notation is
   > completely lost. Furthermore, CL-calculus is weaker than λ(V)-calculus: if their bodies
   > are equal, then functions are equal in λ(V), not in CL.
   >
   > So how can we keep this intuitive simplicity of λ-calculus and avoid these name
   > clashes? Here are two ways. One may use De Bruijn’s notation for λ-terms which
   > replaces bound variable names by integers pointing out the abstractor ofthc variable.
   > This calculus is denoted by Λ. The substitution operation still belongs to the
   > metalanguage. It has to do calculations on De Bruijn’s numbers to operate exact
   > reallocations when passing an effective argument.
   >
   > We are concerned with the second way: the Strong Categorical Combinatory
   > Logic, CCL. It is a first-order theory developed by Curien. Its presentation,
   > named CCLβηSP, is directly coming from the definition of Cartesian Closed
   > Categories.
   >
   > *—Thérèse Hardin (1989, Confluence results for the pure strong categorical logic CCL. λ-calculi as subsystems of CCL)*
