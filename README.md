# Lean Soundness

This project implements a soundness proof of classical first order predicate logic, and we hope in time we can turn it into a library for working with a multiplicity of logical calculi, and proving meta-theorems about them.

The code is currently divided into [syntax](src/syntax.lean) and [semantics](src/semantics.lean) modules. The first contains the definition of a first-order signature, of terms and formulas defined for the language of the signature and also the inductive definition of a natural deduction proof system for the formulas. The second contains the definition of a structure for the signature, the semantics of formulas, and soundness proof itself, along with the auxiliary lemmas required to prove it.

There is also a summary [paper](docs/paper.pdf) describing the code, and a [slideshow](docs/html/slides.html) presentation.