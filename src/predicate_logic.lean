import data.set.countable tactic.find tactic.tidy tactic.ring
universe u

-- We introduce a much simplified version of
-- untyped first order (minimal) predicate logic.

-- make all propositions decidable. 
-- Allows us to freely use ifs like in Haskell
-- but then we must add noncomputable to all functions
-- local attribute [instance] classical.prop_decidable


namespace logic

open list tactic set

structure signature :=
    (functional_symbol : Type u)
    (relational_symbol : Type u)
    (arity : functional_symbol → ℕ)
    (rarity : relational_symbol → ℕ)

section formulas
variable {σ : signature}

-- arity types
def is_constant (f : σ.functional_symbol) := σ.arity f = 0
def signature.nary (σ : signature) (n : ℕ) := subtype {f : σ.functional_symbol | σ.arity f = n}
def signature.nrary (σ : signature) (n : ℕ) := subtype {r : σ.relational_symbol | σ.rarity r = n}
@[reducible]
def signature.const (σ : signature) := σ.nary 0

-- terms in the language
inductive signature.term (σ : signature)
| var : ℕ → signature.term
| app  {n : ℕ} (f : σ.nary n) (v : fin n → signature.term) :  signature.term

#check signature
#check term

-- constant terms.
def signature.nary.term : σ.const → σ.term
| c := term.app c fin_zero_elim

@[reducible]
def signature.term.rw : σ.term → ℕ → σ.term → σ.term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, signature.term.rw (v m) x t in
    term.app f v₂

def signature.term.vars  : σ.term → set ℕ
| (term.var a) := {a}
| (term.app f v) :=
    let v₂ := λ m, signature.term.vars (v m) in
    ⋃ m, v₂ m

@[reducible]
def signature.term.denotes (t : σ.term) : Prop := t.vars = (∅ : set ℕ)
@[reducible]
def signature.term.conotes (t : σ.term) := ¬ t.denotes


#check signature.term.denotes

-- a σ.term in the proper sense of the σ.term (pun intended).
def signature.pterm (σ : signature) := subtype {t : σ.term | t.denotes}-- ∧ t.concrete}
def signature.expression (σ : signature) := subtype {t : σ.term | t.conotes}-- ∧ t.concrete}
-- def cterm := subtype term.concrete

theorem rw_eq_of_not_in_vars : ∀ (t₁ t₂ : σ.term) (x : ℕ), x ∉ t₁.vars → t₁.rw x t₂ = t₁ :=
begin
    intros t₁ t₂ x,
    induction t₁;
    dunfold signature.term.vars signature.term.rw;
    simp;
    intro h,
        simp[h],
    ext y,
    specialize h y,
    exact t₁_ih y h,
end

theorem trivial_rw : ∀ (t: σ.term) (x), t.rw x (term.var x) = t :=
begin
    intros t x,
    induction t;
    dunfold signature.term.rw,
        by_cases x = t;
        simp [h],
    simp at *,
    ext y,
    exact t_ih y,
end

theorem den_rw : ∀ (t₁ t₂ : σ.term) (x : ℕ), t₁.denotes → t₁.rw x t₂ = t₁ :=
begin
    intros t₁ t₂ x den₁,
    induction t₁,
    -- case var
        replace den₁ : (term.var t₁).vars = ∅ := den₁,
        replace den₁ : {t₁} = ∅ := den₁,
        replace den₁ := eq_empty_iff_forall_not_mem.mp den₁,
        specialize den₁ t₁,
        simp at den₁,
        contradiction,
    -- case app
        replace den₁ : (term.app t₁_f t₁_v).vars = ∅ := den₁,
        let v₂ := λ m, (t₁_v m).vars,
        replace den₁ : (⋃ m, v₂ m) = ∅ := den₁,
        have c₀ : ∀ m, (v₂ m) = ∅,
            intro m,
            ext, constructor, intro h,
                simp,
                have c : x_1 ∈ (⋃ m, v₂ m), 
                    simp,
                    existsi m,
                    exact h,
                rwa den₁ at c,
            intro insanity,
            simp at insanity,
            contradiction,
        have c₁ : ∀ m, (t₁_v m).denotes := c₀,
        have c₂ : ∀ m, (t₁_v m).rw x t₂ = (t₁_v m),
            intro m,
            exact t₁_ih m (c₁ m),
        dunfold signature.term.rw, 
        simp[c₂],
end

def signature.term.subterms : σ.term → set σ.term
| (term.app f v) := 
    let v₂ := λ m, signature.term.subterms (v m) in
    (⋃ m, v₂ m) ∪ {(term.app f v)}
| t := {t}

def list.vars : list σ.term → set ℕ
| [] := ∅
| (hd :: tl) := hd.vars ∪ tl.vars

def list.subterms : list σ.term → set σ.term
| [] := ∅
| (hd :: tl) := hd.subterms ∪ tl.subterms

def list.rw : list σ.term → ℕ → σ.term → list σ.term
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rw x t) :: tl.rw x t

def subterms : set σ.term → set σ.term
| S := ⋃ x ∈ S, signature.term.subterms x

--  formulas
inductive  signature.formula (σ : signature)
| relational {n : ℕ} (r : σ.nrary n) (v : fin n → σ.term) :  signature.formula
| for_all :  ℕ →  signature.formula →  signature.formula
| if_then :  signature.formula →  signature.formula →  signature.formula
| equation (t₁ t₂ : σ.term) :  signature.formula
| false :  signature.formula

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

instance  signature.formula.has_exp : has_exp  σ.formula := ⟨ signature.formula.if_then⟩

def  signature.formula.not (φ :  σ.formula)   := φ ⇒  signature.formula.false
def  signature.formula.or  (φ ψ :  σ.formula) := φ.not ⇒ ψ
def  signature.formula.and (φ ψ :  σ.formula) := (φ.not.or ψ.not).not
def  signature.formula.iff (φ ψ :  σ.formula) := (φ ⇒ ψ).and (ψ ⇒ φ)

-- local notation `∼` :=  signature.formula.not

def  signature.formula.rw :  σ.formula → ℕ → σ.term →  σ.formula
| ( signature.formula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
     signature.formula.relational r v₂
| ( signature.formula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
     signature.formula.for_all y ψ
| ( signature.formula.if_then φ ψ) x t := (φ.rw x t) ⇒ (ψ.rw x t)
| ( signature.formula.equation t₁ t₂) x t :=  signature.formula.equation (t₁.rw x t) (t₂.rw x t)
| φ _ _ := φ

-- free variables
def  signature.formula.free :  σ.formula → set ℕ
| ( signature.formula.relational r v) := ⋃ m, (v m).vars
| ( signature.formula.for_all x φ) := φ.free - {x}
| ( signature.formula.if_then φ ψ) := φ.free ∪ ψ.free
| ( signature.formula.equation t₁ t₂) := t₁.vars ∪ t₂.vars
|  signature.formula.false := ∅

def  signature.formula.substitutable  :  σ.formula → ℕ → σ.term → Prop
| ( signature.formula.for_all y φ) x t := x ∉ ( signature.formula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| ( signature.formula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t
| _ _ _ := true

-- open and closed  σ.formulas.
def  signature.formula.closed :  σ.formula → Prop
| φ := φ.free = ∅

def  signature.formula.open :  σ.formula → Prop
| φ := ¬ φ.closed

def  signature.formula.vars :  σ.formula → set ℕ
| ( signature.formula.for_all x φ) := φ.free ∪ {x}
| ( signature.formula.if_then φ ψ) := φ.vars ∪ ψ.vars
| φ := φ.free

def  signature.formula.terms :  σ.formula → set σ.term
| ( signature.formula.relational r v) := list.subterms (of_fn v)
| ( signature.formula.for_all x φ) := φ.terms ∪ {term.var x}
| ( signature.formula.if_then φ ψ) := φ.terms ∪ ψ.terms
| _ := ∅

def term.abstract_in : σ.term → set  σ.formula → Prop
| t S := t ∉ (⋃ φ ∈ S,  signature.formula.terms φ)

@[reducible]
def abstract_in : ℕ → set  σ.formula → Prop
| x S := x ∉ (⋃ φ ∈ S,  signature.formula.free φ)

-- construct the generalization of a  σ.formula from a list of variables.
-- This is just a fold but, I like being explicit in my folds when possible.
def  signature.formula.generalize :  σ.formula → list ℕ →  σ.formula
| φ [] := φ
| φ (x::xs) :=  signature.formula.for_all x $ φ.generalize xs

theorem formula_rw : ∀ {φ :  σ.formula} {x : ℕ}, x ∉ φ.free → ∀(t : σ.term),φ.rw x t = φ :=
    begin
        intros φ x h t,
        revert h,
        induction φ;
        dunfold  signature.formula.free  signature.formula.rw;
        simp;
        intro h,
            ext y,
            specialize h y,
            revert h,
            induction φ_v y;
            dunfold signature.term.rw signature.term.vars;
            intro h;
            simp at *,
                simp[h],
            ext z,
            specialize h z,
            specialize ih z,
            exact ih h,
        classical,
        -- rename _inst_1 dont_annoy,
        by_cases eq₁ : x ∈ φ_a_1.free,
            simp [h eq₁],
        by_cases eq₂ : φ_a = x;
            simp [eq₂],
        exact φ_ih eq₁,
        all_goals{
            push_neg at h,
            obtain ⟨h₁, h₂⟩ := h,
        },  
            replace h₁ := φ_ih_a h₁,
            replace h₂ := φ_ih_a_1 h₂,
            rw [h₁, h₂],
            refl,
        constructor;
        apply rw_eq_of_not_in_vars;
        assumption,
    end

lemma trivial_formula_rw : ∀ {φ: σ.formula} {x}, φ.rw x (term.var x) = φ :=
    begin
        intros φ x,
        induction φ;
        -- tactic.unfreeze_local_instances,
        dunfold  signature.formula.rw;
        try{simp},
        -- any_goals{assumption},
            -- convert h,
            ext,
            induction (φ_v x_1);
            dunfold signature.term.rw,
            by_cases x = a;
                simp [h],
            simp,
            ext,
            exact ih x_2,
        rw φ_ih,
        simp,
            simp [φ_ih_a, φ_ih_a_1],
            refl,
        constructor;
        apply trivial_rw;
        assumption,
    end

#check σ.formula

-- deductive consequence of  σ.formulas: Γ ⊢ φ.
-- Type of proofs from Γ to φ.
inductive proof : set  σ.formula →  σ.formula → Type u_1
| reflexivity (Γ : set  σ.formula) (φ :  σ.formula)(h : φ ∈ Γ) : proof Γ φ
| transitivity (Γ Δ : set  σ.formula) (φ :  σ.formula)
               (h₁ : ∀ ψ ∈ Δ, proof Γ ψ)
               (h₂ : proof Δ φ) :  proof Γ φ
| modus_ponens
            (φ ψ :  σ.formula) (Γ : set  σ.formula)
            (h₁ : proof Γ (φ ⇒ ψ))
            (h₂ : proof Γ φ)
             : proof Γ ψ
| intro
            (φ ψ :  σ.formula) (Γ : set  σ.formula)
            (h : proof (Γ ∪ {φ}) ψ)
             : proof Γ (φ ⇒ ψ)
| for_all_intro
            (Γ : set  σ.formula) (φ :  σ.formula)
            (x : ℕ) (xf : x ∈ φ.free)
            (abs : abstract_in x Γ)
            (h : proof Γ φ)
             : proof Γ ( signature.formula.for_all x φ)
| for_all_elim
            (Γ : set  σ.formula) (φ :  σ.formula)
            (x : ℕ) --(xf : x ∈ φ.free)
            (t : σ.term) (sub : φ.substitutable x t)
            (h : proof Γ ( signature.formula.for_all x φ))
             : proof Γ (φ.rw x t)
| exfalso (Γ : set  σ.formula) (φ :  σ.formula)
          (h : proof Γ  signature.formula.false)
          : proof Γ φ
| by_contradiction (Γ : set  σ.formula) (φ :  σ.formula)
                   (h : proof Γ φ.not.not)
                   : proof Γ φ
| identity_intro
            (Γ : set  σ.formula) (t : σ.term)
             : proof Γ ( signature.formula.equation t t)
| identity_elim 
            (Γ : set  σ.formula) (φ :  σ.formula)
            (x : ℕ) (xf : x ∈ φ.free)
            (t₁ t₂: σ.term)
            (sub₁ : φ.substitutable x t₁)
            (sub₂ : φ.substitutable x t₂)
            (h : proof Γ (φ.rw x t₁))
            (eq : proof Γ ( signature.formula.equation t₁ t₂))
             : proof Γ (φ.rw x t₂)

local infixr `⊢`:55 := proof

variables (Γ Δ : set  σ.formula) (φ :  σ.formula)

theorem self_entailment : Γ ⊢ (φ ⇒ φ) :=
begin
    apply proof.intro,
    apply proof.reflexivity (Γ∪{φ}) φ,
    simp
end

theorem monotonicity : Δ ⊆ Γ → Δ ⊢ φ → Γ ⊢ φ :=
begin
    intros H h,
    have c₁ : ∀ ψ ∈ Δ, proof Γ ψ,
        intros ψ hψ,
        apply proof.reflexivity Γ ψ,
        exact H hψ,
    apply proof.transitivity;
    assumption,
end 


-- This depends on syntatical equality between  σ.formulas
-- being decidable, which in turn depends on the equality of
-- functional and relational symbols being decidable.
-- def proof.premisses : Γ ⊢ φ → list (subtype Γ) :=
--     begin
--         intros h,
--         induction h,
--         -- case reflexivity
--         exact [⟨h_φ, h_h⟩],
--         -- case transitivity
--         rename h_ih_h₁ ih₁,
--         induction h_ih_h₂,
--             exact [],
--         obtain ⟨ψ, H⟩ := h_ih_h₂_hd,
--         specialize ih₁ ψ H,
--         exact ih₁ ++ h_ih_h₂_ih,
--         -- case modus ponens
--         exact h_ih_h₁ ++ h_ih_h₂,
--         -- case intro
--         set t : set  σ.formula := h_Γ ∪ {h_φ},
--         have ct : h_φ ∈ t, simp,
--         let c : subtype t := ⟨h_φ, ct⟩,
--         all_goals{admit},
--     end



-- open finset

-- local notation `{` x `}ₙ` := finset.singleton x

-- #find ∀ _ ∈ _, ∃ _, _

-- def list.to_set : list  σ.formula → set  σ.formula
-- | [] := ∅
-- | (φ::xs) := {φ} ∪ xs.to_set

-- def proof : list  σ.formula → Prop
-- | [] := false
-- | (ψ::[]) := ψ ∈ Γ ∨ ∅ ⊢ ψ
-- | (ψ::xs) := (ψ ∈ Γ ∨ list.to_set xs ⊢ ψ) ∧ 
--              proof xs

-- def proof_of (φ) : list  σ.formula → Prop
-- | [] := false
-- | (ψ::xs) := ψ = φ ∧ proof Γ (ψ::xs)

-- theorem finite_proofs :  Γ ⊢ φ → ∃ xs : list  σ.formula, proof_of Γ φ xs :=
-- begin
--     intro h,
--     induction h,
--     -- case reflexivity
--     let xs := [h_φ], 
--     use xs,
--     simp [xs, proof_of,proof],
--     left,
--     assumption,
--     -- case transitivity
--     rename h_ih_h₁ ih,
--     obtain ⟨p, hp⟩ := h_ih_h₂,
--     -- let xs : list  σ.formula,
--     --     cases p;
--     --         simp[proof_of] at hp,
--     --         contradiction,
--     --     obtain ⟨hp₁, hp₂⟩ := hp,
--     --     revert hp₂,
--     admit,
--     -- case modus ponens
-- end

-- theorem finite_proofs :  Γ ⊢ φ → ∃ Δ : finset  σ.formula, ↑Δ ⊆ Γ ∧ ↑Δ ⊢ φ :=
-- begin
--     intro h,
--     induction h,
--     -- case reflexivity
--     existsi finset.singleton h_φ,
--     simp [proof.reflexivity],
--     assumption,
--     -- case transitivity
--     obtain ⟨Δ, HΔ, hΔ⟩ := h_ih_h₂,
--     -- have c : ∀ ψ ∈ Δ, ∃ (Δ₂ : finset  σ.formula), ↑Δ₂ ⊆ h_Γ ∧ proof ↑Δ₂ ψ,
--     --     intros ψ Hψ,
--     --     exact h_ih_h₁ ψ (HΔ Hψ),
--     -- have c := λ ψ ∈ Δ, classical.subtype_of_exists (h_ih_h₁ ψ (HΔ _)),
--     -- have c₂ : ⋃ ψ ∈ Δ, classical.some (h_ih_h₁ ψ (HΔ _)),
--     -- have d : ∀ {α} 

--     -- induction Δ using finset.induction,
--     --     admit,
--     --     use ∅,
--     --     simp,
--     --     exact hΔ,
    
--     -- classical,
--     -- by_cases ne : Δ.nonempty,
--     -- obtain ⟨ψ, Hψ⟩ := ne,
    
--     -- have ih := h_ih_h₁ ψ H,
--     -- existsi ⋃ ψ ∈ Δ, (c ψ H).val,

-- end

-- Doesn't need to be defined just for theories
def consistent (Γ : set  σ.formula) := ¬ nonempty (Γ ⊢  signature.formula.false)

-- At any rate we can define it for theories as well.
def signature.theory (σ : signature) := subtype {Γ : set  σ.formula | ∀ φ, Γ ⊢ φ → φ ∈ Γ}

def theory.consistent (Γ : σ.theory) := consistent Γ.val

section semantics

structure signature.structure (σ : signature) (α : Type u) [nonempty α] :=
    -- functional interpretation
    (I₁ : Π {n}, σ.nary n → (fin n → α) → α)
    -- relational interpretation
    (I₂ : Π {n}, σ.nrary n → (fin n → α) → Prop)

parameters {α : Type u} [nonempty α]
-- variable assignment
def vasgn := ℕ → α

-- @[reducible]
def signature.structure.reference' (M : σ.structure α) : σ.term → vasgn → α
| (term.var x) asg := asg x
| (@term.app _ 0 f _) _ := M.I₁ f fin_zero_elim
| (@term.app _  (n+1) f v) asg := let v₂ := λ k, signature.structure.reference' (v k) asg
                                    in M.I₁ f v₂

def signature.structure.reference (M : σ.structure α) : σ.pterm → α :=
    begin
        intro t,
        obtain ⟨t, den⟩ := t,
        induction t,
            simp [set_of] at den,
            revert den,
            dunfold signature.term.denotes signature.term.vars,
            intro den,
            replace den := eq_empty_iff_forall_not_mem.mp den,
            specialize den t,
            simp at den,
            contradiction,
        cases t_n,
            exact M.I₁ t_f fin_zero_elim,
        have den_v : ∀ x, (t_v x).denotes,
            intro x,
            simp [set_of] at den,
            revert den,
            dunfold signature.term.denotes signature.term.vars,
            simp,
            intro den,
            have c := set.subset_Union (signature.term.vars ∘ t_v) x,
            simp [den] at c,
            -- could have used the set lemma,
            -- but library search finished
            -- this one off.
            exact eq_bot_iff.mpr c,
        have ih := λ x, t_ih x (den_v x),
        exact M.I₁ t_f ih,
    end

def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y

def signature.structure.satisfies' : σ.structure α →  σ.formula → vasgn → Prop
| M ( signature.formula.relational r v) asg := 
          M.I₂ r $ λm,  M.reference' (v m) asg
| M ( signature.formula.for_all x φ) ass :=
    ∀ (a : α), M.satisfies' φ (ass.bind x a)
| M ( signature.formula.if_then φ ψ) asg :=
    let x := M.satisfies' φ asg,
        y := M.satisfies' ψ asg
    in x → y
| M ( signature.formula.equation t₁ t₂) asg := 
    let x := M.reference' t₁ asg,
        y := M.reference' t₂ asg
    in x = y
| M  signature.formula.false _ := false


@[reducible]
def signature.structure.satisfies : σ.structure α →  σ.formula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

local infixr `⊨₁`:55 := signature.structure.satisfies
-- local infixr `⊢`:55 := proof

lemma false_is_unsat : ¬∃ M : σ.structure α, M ⊨₁  signature.formula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    apply nonempty.elim _inst_1,
    intro x,
    exact h (λ_, x),
end

def signature.structure.for : σ.structure α → set  σ.formula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨₁ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ (M : σ.structure α) (ass : vasgn),
      (∀ ψ ∈ Γ, M.satisfies' ψ ass) → M.satisfies' φ ass

local infixr `⊨`:55 := theory.follows

lemma bind_symm : ∀ {ass : vasgn} {x y : ℕ} {a b}, x ≠ y → (ass.bind x a).bind y b = (ass.bind y b).bind x a :=
    begin
        intros ass x y a b h,
        simp [vasgn.bind],
        ext z,
        replace h := ne.symm h,
        by_cases eq : z = y;
            simp[eq, h],
    end

lemma bind₁ : ∀ {ass : vasgn} {x : ℕ}, ass.bind x (ass x) = ass :=
    begin
        intros ass x,
        simp [vasgn.bind],
        ext y,
        by_cases y = x;
        simp[h],
    end

lemma bind₂ : ∀ {ass : vasgn} {x : ℕ} {a b}, (ass.bind x a).bind x b = ass.bind x b :=
    begin
        intros ass x a b,
        simp [vasgn.bind],
        ext y,
        by_cases y = x;
        simp[h],
    end

lemma bind_term : ∀ {M : σ.structure α} {ass :vasgn} {x : ℕ} {t : σ.term} {a},
                  x ∉ t.vars →
                  M.reference' t (vasgn.bind ass x a) =
                  M.reference' t ass :=
begin
    intros M ass x t a,
    induction t;
    dunfold signature.term.vars;
    simp;
    intro h,
        dunfold signature.structure.reference' vasgn.bind,
        simp [ne.symm h],
    cases t_n;
        dunfold signature.structure.reference';
        simp,
    congr,
    ext y,
    specialize h y,
    exact t_ih y h,
end

lemma bind₃ : ∀ {M : σ.structure α} {φ: σ.formula}{ass : vasgn}{x : ℕ}{a},
              x ∉ φ.free →
              (M.satisfies' φ (ass.bind x a) ↔
              M.satisfies' φ ass)
              :=
begin
    intros M φ ass x a,
    induction φ generalizing ass;
    dunfold  signature.formula.free signature.structure.satisfies';
    simp;
    intros h₀,
    swap 3,
    replace h₀ := not_or_distrib.mp h₀,
    obtain ⟨h₀, h₁⟩ := h₀,
    constructor;
    intros h₂ h₃;
    have ih₁ := @φ_ih_a ass h₀;
    have ih₂ := @φ_ih_a_1 ass h₁,
        replace ih₁ := ih₁.2 h₃,
        apply ih₂.mp,
        exact h₂ ih₁,
    replace ih₁ := ih₁.mp h₃,
    apply ih₂.2,
    exact h₂ ih₁,
    focus {
        constructor,
        all_goals{
            intro h₁,
            convert h₁,
            ext y,
            specialize h₀ y,
            revert h₀,
            induction φ_v y;
            dunfold signature.term.vars signature.structure.reference' vasgn.bind;
            intro h₀,
                simp at h₀,
                replace h₀ := ne.symm h₀,
                simp [h₀],
            cases n;
                dunfold signature.structure.reference',
                refl,
            simp at *,
            congr,
            ext z,
            exact ih z (h₀ z),
        },
    },
    constructor;
    intro h₁;
    intro a₂;
    classical;
    -- rename _inst_1 dont_annoy,
    all_goals{
        by_cases (x ∈ φ_a_1.free),
            specialize h₁ a₂,
            revert h₁,
            rw (h₀ h),
            rw bind₂,
            intro h₁,
            exact h₁,
        by_cases eq : x = φ_a,
            specialize h₁ a₂,
            revert h₁,
            rw eq,
            rw bind₂,
            intro h₁,
            exact h₁,
        specialize h₁ a₂,
    },
        rw bind_symm eq at h₁,
        exact (φ_ih h).mp h₁,
    rw bind_symm eq,
    exact (φ_ih h).2 h₁,
        push_neg at h₀,
        obtain ⟨h₀, h₁⟩ := h₀,
        rw [bind_term h₀, bind_term h₁],
end

lemma fundamental : ∀ y x (M : σ.structure α) ass, abstract_in y Γ → 
            (∀ φ ∈ Γ, M.satisfies' φ ass) →
            ( ∀φ ∈ Γ, M.satisfies' φ (ass.bind y x))
            :=
        
begin
    intros y x M ass h₁ h₂ φ H,
    simp [abstract_in] at h₁,
    specialize h₁ φ H,
    specialize h₂ φ H,
    exact (bind₃ h₁).2 h₂,
end

lemma term_rw_semantics : ∀ {M : σ.structure α} {ass:vasgn} {x} {t₁ t₂ : σ.term},
                          M.reference' (t₁.rw x t₂) ass =
                          M.reference' t₁ (ass.bind x (M.reference' t₂ ass))
                          :=
begin
    intros M ass x t₁ t₂,
    induction t₁,
        dunfold signature.term.rw signature.structure.reference',
        by_cases x = t₁;
            simp [vasgn.bind, h],
        dunfold signature.structure.reference',
        simp [ne.symm h],
    cases t₁_n;
        dunfold signature.term.rw signature.structure.reference';
        simp,
    congr,
    ext y,
    exact t₁_ih y,
end

lemma rw_semantics : ∀ {M : σ.structure α} {ass:vasgn} {x t} {φ: σ.formula},
                     φ.substitutable x t →
                     (M.satisfies' (φ.rw x t) ass ↔
                     M.satisfies' φ (ass.bind x (M.reference' t ass))) 
                     :=
begin
    intros M ass x t φ,
    induction φ generalizing ass;
    dunfold  signature.formula.substitutable  signature.formula.rw signature.structure.satisfies';
    try{simp},
    focus {
        constructor;
        intro h,
        all_goals{
        convert h,
        ext y,
        induction φ_v y;
        dunfold signature.term.rw signature.structure.reference' vasgn.bind,
            by_cases eq : a = x;
                simp [eq],
            replace eq := ne.symm eq,
            simp [eq],
            dunfold signature.structure.reference',
            refl,
        simp,
        cases n;
            dunfold signature.structure.reference';
            simp,
        congr,
        ext z,
        exact ih z,},
    },

    focus{
        intro h,
        by_cases c : φ_a = x,
            simp [c, bind₂],
        simp [c],
        cases h,
            revert h,
            dunfold  signature.formula.free,
            simp_intros h,
            classical,
            replace h : x ∉ φ_a_1.free,
                by_contradiction H,
                replace h := eq.symm (h H),
                contradiction,
            constructor; intros hyp a;
            specialize hyp a,
                rw formula_rw h t at hyp,
                rw bind_symm (ne.symm c),
                rwa bind₃ h,
            rw formula_rw h t,
            rw bind_symm (ne.symm c) at hyp,
            rwa bind₃ h at hyp,
        obtain ⟨h₁, h₂⟩ := h,
        constructor; intros hyp a;
        specialize hyp a;
        have ih := @φ_ih (vasgn.bind ass φ_a a) h₂;
        rw bind_term h₁ at ih,
            rw bind_symm (ne.symm c),
            exact ih.mp hyp,
        rw bind_symm (ne.symm c) at hyp,
        apply ih.2,
        exact hyp,
    },
        intros sub₁ sub₂,
        constructor; intros h₁ h₂;
        have ih₁ := @φ_ih_a ass sub₁;
        have ih₂ := @φ_ih_a_1 ass sub₂,
            replace h₂ := ih₁.2 h₂,
            apply ih₂.mp,
            apply_assumption,
            exact h₂,
        replace h₂ := ih₁.mp h₂,
        apply ih₂.2,
        apply_assumption,
        exact h₂,
    simp [term_rw_semantics],
end

-- So pretty.
theorem soundness : Γ ⊢ φ → Γ ⊨ φ :=
begin
    intros proof M ass h,
    induction proof generalizing ass,
    -- case reflexivity
    exact h proof_φ proof_h,
    -- case transitivity
    apply proof_ih_h₂,
    intros ψ H,
    exact proof_ih_h₁ ψ H ass h,
    -- case modus ponens
    have c₁ := proof_ih_h₁ ass h,
    have c₂ := proof_ih_h₂ ass h,
    revert c₁,
    dunfold signature.structure.satisfies',
    simp,
    intro c₁,
    exact c₁ c₂,
    -- case intro
    intro h₂,
    have sat := proof_ih,
    apply sat,
    intros ψ H,
    cases H,
    exact h ψ H,
    simp at H,
    rwa H,
    -- case universal intro
    intro x,
    have c := fundamental proof_Γ proof_x x,
    specialize c M ass proof_abs h,
    have ih := proof_ih (ass.bind proof_x x),
    apply ih,
    exact c,
    -- case universal elim
    have ih := proof_ih ass h,
    rename proof_sub sub,
    clear proof_ih,
    revert ih,
    dunfold signature.structure.satisfies',
    intro ih,
    set ref := M.reference' proof_t ass,
    specialize ih ref,
    exact (rw_semantics sub).2 ih,
    -- case exfalso
    exfalso,
    have ih := proof_ih ass h,
    revert ih,
    dunfold signature.structure.satisfies',
    contradiction,
    -- case by contradiction
    classical,
    by_contradiction,
    have ih := proof_ih ass h,
    revert ih,
    dunfold  signature.formula.not signature.structure.satisfies',
    simp,
    intro ih,
    apply ih,
    intro insanity,
    contradiction,
    -- case identity intro
    dunfold signature.structure.satisfies',
    simp,
    -- case identity elimination
    have ih₁ := proof_ih_h ass h,
    have ih₂ := proof_ih_eq ass h,
    rename proof_sub₁ sub₁,
    rename proof_sub₂ sub₂,
    replace ih₁ := (rw_semantics sub₁).mp ih₁,
    apply (rw_semantics sub₂).2,
    convert ih₁ using 2,
    revert ih₂,
    dunfold signature.structure.satisfies',
    simp,
    intro ih₂,
    rw ←ih₂,
end


-- instance signature.structure_inh : nonempty signature.structure := sorry

-- theorem consistency : consistent ∅ :=
-- begin
--     intro h,
--     replace h := soundness ∅  signature.formula.false h,
--     have M : signature.structure := sorry,
--     have ass : vasgn := sorry,
--     specialize h M ass,
--     revert h,
--     dunfold signature.structure.satisfies',
--     simp,
-- end


end semantics

section consistency
end consistency

end formulas
end logic