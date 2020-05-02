<style>
    body{
        text-align: justify;
        font-family: Times;
        font-size: 12pt;
        padding-top: 3.5cm;
        padding-bottom: 2.5cm;
        padding-right: 3cm;
        padding-left: 3cm;
        width: 210mm;
        height: 297mm;
    }
    #title {
        text-align: center;
        font-size: 16pt;
        font-weight: bold;
        padding-top: 12pt;
    }
    h2, h3 {
        text-align: left;
        font-weight: bold;
        font-size: 12pt;
    }
    h2 {
        font-size: 13pt;
        padding-top: 12pt;
    }
    #author{
        text-align: center;
        font-weight: bold;
        padding-top: 12pt;

    }
    #address{
        text-align: center;
        padding-top: 12pt;
    }
    #email{
        text-align: center;
        font-size: 10pt;
        font-family: 'Courier New', Courier monospace;
        padding-top: 6pt;
        padding-bottom: 6pt;
    }
    #abstract {
        margin-right: 0.8cm;
        margin-left: 0.8cm;
        font-style: italic;
    }
    p {
      padding-top: 6pt;
    }
    @page{
            size: A4 portrait;
    }

    code {
        font-size: 12pt;
    }

    pre {
        page-break-inside: avoid;
    }
    
</style>

<div id=title>Proving the consistency of Logic in Lean.</div>

<div id=author>Luiz Carlos R. Viana</div>
<div id=address>Departamento de Informática – Pontifícia Universidade Católica do Rio de Janeiro (PUC-RJ) 
– <br/> Rio de Janeiro, RJ,  Brazil</div>
<div id=email>luizcarlosrvn424@gmail.com</div>

<div id=abstract> <b>Abstract.</b> We implement classical first-order logic with equality in the Lean Interactive Theorem Prover (ITP), and prove its soundness relative to the usual semantics. As a corollary, we prove the consistency of the calculus.
</div>

## **Introduction**

The advent of intuitionistic dependent type theories allowed the development of proof assistants for the formalization and computer-aided verification of mathematical proofs. These interactive proof systems allow the experienced user to prove just about any true theorem of mathematics which is at least already suspected in the literature to be true.

&emsp; &emsp; As explained in Martin-Löf's paper [1], by applying the Curry-Howard isomorphism between proofs in intuitionistic logic and terms in a typed lambda calculus, we can see any flavour of intuitionistic type theory to be a programming language whose programs are mathematical proofs. The Lean ITP, developed by Leonardo de Moura at Microsoft Research, is such a programming language: implementing intuitionistic type theory and the calculus of inductive constructions, Lean allows for the development of complex proofs in all areas of mathematics in a way that resembles the more familiar forms of software production. By default, Lean allows for the construction of proofs in intuitionistic logic, but by the declaration of (the non-intuitionistic version of) the axiom of choice as an extra axiom of the theory, it also allows for classical reasoning to take place. Since intuitionistic type theory with the axiom of choice is at least as expressive as classical ZFC set theory, it is very much well suited for use as a meta-language for the development of semantics for logical calculi. In fact the community-developed standard library [2] for the Lean prover already implements an internal model of ZFC within Lean:

```haskell
-- The ZFC universe of sets consists of the type of pre-sets,
-- quotiented by extensional equivalence.
def Set : Type (u+1) := quotient pSet.setoid.{u}
```

&emsp; &emsp; This goes to show not only that Lean is at least as expressive as ZFC, but also the consistency of ZFC relative to Lean. In this paper we implemented first-order logic as an internal embedded language of Lean and used Lean structures to give model-theoretic semantics to the logical calculus. This allowed us to derive the consistency of the calculus, and opens up the way for future work in this area.

<!-- We can then use types in Lean in a manner similar as to how we use sets in ZFC to provide semantics for formal languages. -->

<!-- - Talk about Martin-lof intuitionistic dependent type theory and how the Lean prover uses it.
- Talk about the possibility of specifying internal languages as well as models of these languages, turning the theorem prover into a powerful meta-language. Mention that the implemented type theory is at least as powerful as set theory, by showing that there is a model of ZFC defined in mathlib. Use code references to mathlib. -->

## **Motivation of our Work**

One general motivation for the development of interactive theorem provers is the formal verification of mathematical proofs such as Jordan's curve theorem and Fermat's last theorem, which are so large and complex that even expert mathematicians may have trouble understanding them, and for this reason may suspect them to be wrong. However, for simpler results, such as that of the soundness of first-order logic, even though a verification might provide greater security to some, there is already virtually no suspicion in the mathematical community that their canonical, more well-known, proofs might be wrong. So this reason would be very weak to motivate our research.

&emsp; &emsp; On the other hand, in the spirit of literate programming, we can set out to investigate the usability of these provers for teaching logic to students by providing a formalized reference of the subject and of its proofs, as a practical tool for the solution of mathematical exercises, and also as a means of teaching the formal verification of computer programs and their semantics. Already some courses of logic using Lean exist, such as the online book *Logic and Proof* [4], but we know of no logic course which teaches the soundness theorem by means of a deep embedding of the syntax of first-order logic within Lean, even though there are certainly papers [5] mentioning this construction has been achieved before. 

<!-- We believe that presenting mathematical proofs as code makes the whole subject of mathematical proofs much more practical and concrete, just as an implementation of an algorithm expressed in pseudo-code   might make them clearer, at least to some people, which justifies the such attempts at teaching logic via Lean. -->

&emsp; &emsp; With respect to exercises, a teacher in any area of mathematics can already write a class assignment in a proof assistant as a list of theorem declarations. A solution to the assignment consists in a proof of each theorem, which is then automatically checked by the software for correctness, requiring no further correction by a human being. An assignment can even be provided in a game-like format [8] and integrated with the theorem prover. The usage of proof assistants in mathematics is sure to save many teachers much time; furthermore, such usage is sure to spread the knowledge of formal methods and of logic itself to many people who might otherwise not have learnt it.

&emsp; &emsp; Our implementation gives a basis for the creation of specialized exercise lists involving meta-theorems of first-order logic. The code can be reused as the basis of a book on meta-logic, or for the development of a general-purpose library for dealing with different logical formalisms as embedded languages of the prover; in particular Hoare logic [6], which is relevant for applications of Lean in software verification. It could also be used to prove the consistency of particular first-order theories via the soundness meta-theorem, by constructing models for them.

<!-- - Teaching logic using interactive theorem provers
- Solving math exercises in a prover allows for automatic correction.
- Teaching formal semantics of languages using interactive theorem provers.
- Implementing Hoare logic for program verification
- Developing a general purpose library that can be reused when developing different logical calculi as internal languages of the prover, or used in arguments about first-order logic.
- Developing a general purpose library for proving the consistency of theories in first-order logic (contrast with theories expressed in the language of the prover itself, which are hard to constrain on being "first order") -->
<!-- <div style="page-break-before: always;"> -->
## **Implementation**

We implemented the different aspects of first order logic, dividing definitions and proofs into syntactical and semantical sections. We present a short summary of our implementation below.

### **Syntactic Definitions**

In our implementation, we assumed the existence of a type of functional symbols and a type of relational symbols as parameters, both accompanied by their respective arity functions:

```haskell
parameter {functional_symbol : Type u}
parameter {relational_symbol : Type u}
parameter {arity : functional_symbol → ℕ}
parameter {rarity : relational_symbol → ℕ}
```

<!-- We used this approach rather than defining a first-order signature as a Lean structure essentially for programming convenience. We could still refactor our code to follow this approach:

```haskell
structure signature :=
    (functional_symbol : Type u)
    (relational_symbol : Type u)
    (arity : functional_symbol → ℕ)
    (rarity : relational_symbol → ℕ)

parameter σ : signature
```

One inconvenience of this is that the signature does not fit into the universe `u`. So our approach is a little bit simpler in this regard. Another parameter we had been experimenting with was to add the restriction that the equality of functional and relational symbols should be algorithmically decidable:

```haskell
parameter [decidable_eq functional_symbol]
parameter [decidable_eq relational_symbol]
```

This makes sense if these types are to represent symbols, for we would expect to be able to decide whether any two given symbols are equal. We were able to define some functions that could not otherwise be defined by means of these assumptions, but since these functions were not very useful in our other definitions, or to prove meta-theorems, and because keeping them around in the tactic contexts caused some minor inconveniences, we removed them. So even though the assumptions are correct, our implementation does not depend on them. -->

&emsp; &emsp; The basic definitions of terms and formulas are given below:

```haskell
-- terms in the language
inductive term
| var : ℕ → term
| app  {n : ℕ} (f : nary n) (v : fin n → term) :  term

-- constant terms.
def nary.term : const → term
| c := term.app c fin_zero_elim

-- formulas
inductive formula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : formula
| false : formula
| for_all :  ℕ → formula → formula
| if_then : formula → formula → formula
| equation (t₁ t₂ : term) : formula
```

&emsp; &emsp; As can be seen, we use the {$\forall, \to,\bot$} functionally complete fragment of first-order logic in the definition of formulas. For the `if_then` constructor we set up a specific notation, since Lean will allow us to do that:

```haskell
reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

instance formula.has_exp : has_exp formula := ⟨formula.if_then⟩
```

&emsp; &emsp; And now we can write `φ ⇒ ψ` instead of `formula.if_then φ ψ`. We also defined the other connectives:

```haskell
def formula.not (φ : formula)   := φ ⇒ formula.false
def formula.or  (φ ψ : formula) := φ.not ⇒ ψ
def formula.and (φ ψ : formula) := (φ.not.or ψ.not).not
def formula.iff (φ ψ : formula) := (φ ⇒ ψ).and (ψ ⇒ φ)
```
<!-- <div style="page-break-before: always;"> -->
&emsp; &emsp; The proof system was implemented inductively using natural deduction rules according to the following definition:
<!-- </div> -->

```haskell
-- deductive consequence of formulas: Γ ⊢ φ
inductive entails : set formula → formula → Prop
| reflexivity (Γ : set formula) (φ : formula)(h : φ ∈ Γ) : entails Γ φ
| transitivity (Γ Δ : set formula) (φ : formula)
               (h₁ : ∀ ψ ∈ Δ, entails Γ ψ)
               (h₂ : entails Δ φ) :  entails Γ φ
| modus_ponens
            (φ ψ : formula) (Γ : set formula)
            (h₁ : entails Γ (φ ⇒ ψ))
            (h₂ : entails Γ φ)
             : entails Γ ψ
| intro
            (φ ψ : formula) (Γ : set formula)
            (h : entails (Γ ∪ {φ}) ψ)
             : entails Γ (φ ⇒ ψ)
| for_all_intro
            (Γ : set formula) (φ : formula)
            (x : ℕ) (xf : x ∈ φ.free)
            (abs : abstract_in x Γ)
            (h : entails Γ φ)
             : entails Γ (formula.for_all x φ)
| for_all_elim
            (Γ : set formula) (φ : formula)
            (x : ℕ) (t : term)
            (sub : φ.substitutable x t)
            (h : entails Γ (formula.for_all x φ))
             : entails Γ (φ.rw x t)
| exfalso (Γ : set formula) (φ : formula)
          (h : entails Γ formula.false)
          : entails Γ φ
| by_contradiction (Γ : set formula) (φ : formula)
                   (h : entails Γ φ.not.not)
                   : entails Γ φ
| identity_intro
            (Γ : set formula) (t : term)
             : entails Γ (formula.equation t t)
| identity_elim 
            (Γ : set formula) (φ : formula)
            (x : ℕ) (xf : x ∈ φ.free)
            (t₁ t₂: term)
            (sub₁ : φ.substitutable x t₁)
            (sub₂ : φ.substitutable x t₂)
            (h : entails Γ (φ.rw x t₁))
            (eq : entails Γ (formula.equation t₁ t₂))
             : entails Γ (φ.rw x t₂)

local infixr `⊢`:55 := entails
```

&emsp; &emsp; Rewriting is used in the definition (`φ.rw`) as well as the notion of a variable being substitutable by a term in a formula. We also require defining the notion of a variable being free in a formula, and the notion of a variable being "abstract" in a set of formulas. We will detail the implementation of these in the following sections.

<!-- - Show basic definitions of terms, formulas, how the provability relation was inductively defined, the short example proof of $\varphi \to \varphi$ and the soundness proof.
- Ignore the actual proofs (except for the example), and the lemmas. Show only definitions and the statement of the soundness theorem. -->

### **Rewrite system**

For terms, rewriting/substituting a variable for another term is a simple procedure:

```haskell
def term.rw : term → ℕ → term → term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, term.rw (v m) x t in
    term.app f v₂
```

&emsp; &emsp; Notice that lean allows us to call this function as `t₁.rw x t₂` where `t₁` and `t₂` are terms and `x` is a variable (which we chose to represent as a natural number). And this will work the same for the rewriting of terms in formulas. For formulas, the definition is simple as well, but we must be concerned with defining also the predicate which tells whether a term is substitutable for a variable in a formula:

```haskell
def formula.rw : formula → ℕ → term → formula
| (formula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
    formula.relational r v₂
| (formula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
    formula.for_all y ψ
| (formula.if_then φ ψ) x t := (φ.rw x t) ⇒ (ψ.rw x t)
| (formula.equation t₁ t₂) x t := formula.equation (t₁.rw x t) (t₂.rw x t)
| φ _ _ := φ

def formula.substitutable  : formula → ℕ → term → Prop
| (formula.for_all y φ) x t := x ∉ (formula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| (formula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t
| _ _ _ := true -- atomic formulas
```

### **Variables**

We need to concern ourselves with defining free variables as well: 

```haskell
-- the variables present in a term
def term.vars : term → set ℕ
| (term.var a) := {a}
| (term.app f v) :=
    let v₂ := λ m, term.vars (v m) in
    ⋃ m, v₂ m

-- free variables
def formula.free : formula → set ℕ
| (formula.relational r v) := ⋃ m, (v m).vars
| (formula.for_all x φ) := φ.free - {x}
| (formula.if_then φ ψ) := φ.free ∪ ψ.free
| (formula.equation t₁ t₂) := t₁.vars ∪ t₂.vars
| formula.false := ∅
```

&emsp; &emsp; We must also define the notion of a variable being "abstract" in a set of formulas, which is to say that the variable doesn't appear free in any formula of the set:

```haskell
def abstract_in : ℕ → set formula → Prop
| x S := x ∉ (⋃ φ ∈ S, formula.free φ)
```

&emsp; &emsp; Given these definitions, all dependencies of our deductive system are defined. We can then provide some simple examples of proofs.

### **Proof examples**

We declare sets of formulas and formulas to be referenced in the context of our proofs:

```haskell
variables (Γ Δ : set formula) (φ : formula)
```

&emsp; &emsp; First we provide a simple example of how to prove that a theory proves a particular formula:

```haskell
theorem self_entailment : Γ ⊢ (φ ⇒ φ) :=
begin
    apply entails.intro,
    apply entails.reflexivity (Γ∪{φ}) φ,
    simp
end
```

&emsp; &emsp; Essentially here we apply the $\to-\text{introduction}$ rule to prove $\varphi \to \varphi$. The goal then becomes to prove $\Gamma \cup \{\varphi\} \vdash \varphi$. We can prove this by noticing that $\varphi \in \Gamma \cup \{\varphi\}$, therefore by reflexivity $\Gamma \cup \{\varphi\} \vdash \varphi$, and the proof is done. Next we provide an example of how to prove a simple syntactical meta-theorem:

```haskell
theorem monotonicity : Δ ⊆ Γ → Δ ⊢ φ → Γ ⊢ φ :=
begin
    intros H h,
    have c₁ : ∀ ψ ∈ Δ, entails Γ ψ,
        intros ψ hψ,
        apply entails.reflexivity Γ ψ,
        exact H hψ,
    apply entails.transitivity;
    assumption,
end
```

&emsp; &emsp; Here we introduce the hypothesis `H : Δ ⊆ Γ` and `h : Δ ⊢ φ`, and prove first the intermediate result ` c₁` which says that every formula of `Δ` is entailed by `Γ`. This we prove by noticing that, by `H`, every formula of `Δ` is a formula of `Γ`, and therefore is entailed by `Γ` by the reflexivity rule. It then suffices to apply the transitivity rule using `c₁` to conclude that `Γ ⊢ φ`. The assumption tactic is used here to tell Lean to look into the local proof context for whatever proofs it needs to apply the transitivity rule. Since `c₁` as well as `H` and `h` are in the local context, and are needed for the rule, they are filled in for us.

### **Semantic Definitions**

For semantics, given a type $\alpha$, which has at least one element, we define 3 types:
- The type of functions mapping functional symbols of arity $n$ to functions of type $\alpha^n \to \alpha$.
-  The type of functions mapping relational symbols of arity $n$ to n-ary relations of $\alpha$.
-  The type of functions mapping variables to elements of $\alpha$, i.e. variable assignments.
 
```haskell
parameters {α : Type u} [nonempty α]

-- functional interpretation
def fint  {n : ℕ} := nary n → (fin n → α) → α
-- relational interpretation
def rint {n : ℕ} := nrary n → (fin n → α) → Prop
-- variable assignment
def vasgn := ℕ → α
```
<!-- <div style="page-break-before: always;"> -->
&emsp; &emsp; It is then trivial to define a structure for the language, which we call a model:
<!-- </div> -->

```haskell
structure model :=
    (I₁ : Π {n}, @fint n)
    (I₂ : Π {n}, @rint n)
```

&emsp; &emsp; We then define references for terms in the language, and a way to bind a variable to a reference in a variable assignment:

```haskell
def model.reference' (M : model) : term → vasgn → α
| (term.var x) asg := asg x
| (@term.app _ _  0 f _) _ := model.I₁ M f fin_zero_elim
| (@term.app _ _  (n+1) f v) asg := let v₂ := λ k, model.reference' (v k) asg
                                    in model.I₁ M f v₂

def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y
```

&emsp; &emsp; The reference was defined differently for constant terms and for non-constant terms arising out of a function application, that is why there are two `@term.app` cases. The first maps the constant to the reference given by the interpretation, while the second first resolves the reference of every argument of the functional symbol to be applied, then interprets the functional symbol and applies the resulting function over the references of the arguments. Further, we define the relation of satisfiability of formulas in a model, both with respect to to a variable assignment and without one:

```haskell
def model.satisfies' : model → formula → vasgn → Prop
| M (formula.relational r v) asg := 
    M.I₂ r $ λm,  M.reference' (v m) asg
| M (formula.for_all x φ) ass :=
    ∀ (a : α), M.satisfies' φ (ass.bind x a)
| M (formula.if_then φ ψ) asg :=
    let x := M.satisfies' φ asg,
        y := M.satisfies' ψ asg
    in x → y
| M (formula.equation t₁ t₂) asg := 
    let x := M.reference' t₁ asg,
        y := M.reference' t₂ asg
    in x = y
| M formula.false _ := false

def model.satisfies : model → formula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

local infixr `⊨₁`:55 := model.satisfies

```

&emsp; &emsp; We have chosen to follow the pattern that the functions defined with a `'` depend on a choice of assignment, while the ones without it do not. Finally, we define the notion of a formula being a semantic consequence of a set of formulas:

```haskell
def theory.follows (Γ : set formula) (φ : formula): Prop :=
    ∀ (M : model) ass, 
    (∀ ψ ∈ Γ, M.satisfies' ψ ass) →
    M.satisfies' φ ass

local infixr `⊨`:55 := theory.follows
```

### **The Proof**

Given the introduction of notation in Lean, the statement of the the proof itself can be succinctly introduced in the same format it would be on any reference textbook:

```haskell
-- So pretty.
theorem soundness : Γ ⊢ φ → Γ ⊨ φ := ...
```
<!-- <div style="page-break-before: always;"> -->
&emsp; &emsp; In order to prove it, we first needed to prove the following lemmas about binding in assignments and the semantics of rewriting variables for terms:
<!-- </div> -->
    
```haskell
lemma bind_symm : ∀ {ass : vasgn} {x y : ℕ} {a b},
                  x ≠ y →
                 (ass.bind x a).bind y b = (ass.bind y b).bind x a 
                 := ...

lemma bind₁ : ∀ {ass : vasgn} {x : ℕ}, ass.bind x (ass x) = ass := ...
lemma bind₂ : ∀ {ass : vasgn} {x : ℕ} {a b},
              (ass.bind x a).bind x b = ass.bind x b := ...

lemma bind₃ : ∀ {M:model} {φ:formula}{ass : vasgn}{x : ℕ}{a},
              x ∉ φ.free →
              (M.satisfies' φ (ass.bind x a) ↔
              M.satisfies' φ ass)
              := ...

lemma fundamental : ∀ y x (M : model) ass, abstract_in y Γ → 
            (∀ φ ∈ Γ, M.satisfies' φ ass) →
            ( ∀φ ∈ Γ, M.satisfies' φ (ass.bind y x))
            := ...

lemma rw_semantics : ∀ {M:model} {ass:vasgn} {x t} {φ:formula},
                     φ.substitutable x t →
                     M.satisfies' (φ.rw x t) ass ↔
                     M.satisfies' φ (ass.bind x (M.reference' t ass)) 
                     := ...
```

&emsp; &emsp; We will not reproduce the proof here for lack of space. Furthermore, many references [7] already exist for an outline of how this sort of proof works. Suffices to say that the proof proceeds by induction on all possible ways that the set of formulas $\Gamma$ could prove the formula $\varphi$, by showing essentially that all logical rules preserve the validity of formulas. As a corollary we can conclude that the empty set of formulas is consistent:

```haskell
theorem consistency : consistent ∅ := ...
```

&emsp; &emsp; The proof works by constructing some model $M$, which is trivial to do, and then this will be a model of the empty set. It follows by soundness that if `formula.false` could be proven from $\empty$, then $M$ would satisfy `formula.false`, but since no model can do that, we have that $\empty$ does not prove `formula.false`.

<!-- ### **The Logic of the Proof.**
- Talk about how the soundness proof uses the lemmas. Give the statement of the lemmas and discuss in outline how they are used in the proof, but do not show proof the proof itself of either the lemmas nor of soundness. -->

## **Conclusion**

We have summarized our implementation of the soundness proof, many more details could still be given about how the proofs were constructed, and the difficulties which lied therein. Our work still gives many opportunities for expansion. Another simple corollary we could derive would be the consistency of arithmetic, by showing that the natural numbers are a model of the Peano axioms. Another more laborious extension would be the completeness proof of classical predicate logic. For more practical utility, we could extend the syntax of the system to include Hoare triples and exemplify the application of Hoare logic to the formal verification of a particular algorithm in Lean. There is still much in store for the future.

<!-- - Talk about how this work immediately opens up the possibility of proving the consistency of arithmetic by using the natural numbers as a model, and also of proving completeness.
- Talk about a future internalized (deep embedding) implementation of Hoare logic and how it could be used for program verification. -->

## **References**

[1] 1982, “Constructive mathematics and computer programming”, in Logic, methodology and philosophy of science VI,
&emsp; &emsp; Proceedings of the 1979 international congress at Hannover, Germany, L.J. Cohen, J. Los, H. Pfeiffer and  
&emsp; &emsp; K.-P. Podewski (eds). Amsterdam: North- Holland Publishing Company, pp. 153–175.

[2] 2020, "The lean mathematical library", in Proceedings of the 9th ACM SIGPLAN International Conference on  
    &emsp; &emsp; Certified Programs and Proofs, The mathlib Community, ACM.

[3] 1958, "Combinatory Logic", Curry, Haskell B. and Robert Feys, Amsterdam: North-Holland.  

[4] 2017, Logic and Proof, Jeremy Avigad, Robert Y. Lewis, and Floris van Doorn,  
    &emsp; &emsp; https://leanprover.github.io/logic_and_proof/ (accessed in 4/29/2020).

[5] 2019, "A formalization of forcing and the unprovability of the continuum hypothesis", Jesse Michael Han and   
    &emsp; &emsp; Floris van Doorn.

[6] 1969, "An Axiomatic Basis for Computer Programming", The Queen's University of Belfast,* Northen Ireland,  
    &emsp; &emsp; C.A.R. Hoare.

[7] 1972, "A Mathematical Introduction to Logic", Herbert B. Enderton.

[8] 2020, "Natural Number Game", http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/  
    &emsp; &emsp; (accessed in 4/29/2020), Kevin Buzzard, Mohammad Pedramfar.