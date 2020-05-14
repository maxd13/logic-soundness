import data.set.lattice tactic.find tactic.tidy tactic.ring
universe u

-- We introduce a much simplified version of
-- untyped first order predicate logic.

namespace logic

open list tactic set

structure signature : Type (u+1) :=
    (functional_symbol : Type u)
    (relational_symbol : Type u)
    (modality : Type u)
    (vars : Type u) 
    (dec_vars : decidable_eq vars)
    (arity : functional_symbol → ℕ)
    (rarity : relational_symbol → ℕ)
    (marity : modality → ℕ)

class signature.symbolic (σ : signature) :=
    (dec_fun : decidable_eq σ.functional_symbol)
    (dec_rel : decidable_eq σ.relational_symbol)


instance dec_vars  (σ : signature) : decidable_eq σ.vars := σ.dec_vars 
instance dec_fun (σ : signature) [h : σ.symbolic] : decidable_eq σ.functional_symbol := h.dec_fun
instance dec_rel (σ : signature) [h : σ.symbolic] : decidable_eq σ.relational_symbol := h.dec_rel

structure simple_signature :=
    (functional_symbol : Type u)
    (relational_symbol : Type u)
    (arity : functional_symbol → ℕ)
    (rarity : relational_symbol → ℕ)


-- will convert to a lift or coe whenever I have the need of it
def simple_signature.up (σ : simple_signature) : signature := 
{ functional_symbol := σ.functional_symbol,
  relational_symbol := σ.relational_symbol,
  modality := empty,
  vars := ℕ,
  dec_vars := by apply_instance,
  arity := σ.arity,
  rarity := σ.rarity,
  marity := λ_, 0
}

instance simple_signature_inhabited : inhabited simple_signature :=
    ⟨⟨pempty, pempty, (λ_, 0), (λ_, 0)⟩⟩

-- empty signature
instance signature_inhabited : inhabited signature :=
    ⟨(default simple_signature).up⟩


-- The signature whose formulas are propositional formulas built up
-- from taking the instances of type α as propositional variables.

def propositional_signature (α : Type u) : signature := 
{ functional_symbol := pempty,
  relational_symbol := α,
  modality := pempty,
  vars := pempty,
  dec_vars := by apply_instance,
  arity := (λ_, 0),
  rarity := (λ_, 0),
  marity := (λ_, 0)
}

variable {σ : signature}

-- arity types
def is_constant (f : σ.functional_symbol) := σ.arity f = 0
def signature.nary (σ : signature) (n : ℕ) := subtype {f : σ.functional_symbol | σ.arity f = n}
def signature.nrary (σ : signature) (n : ℕ) := subtype {r : σ.relational_symbol | σ.rarity r = n}
@[reducible]
def signature.const (σ : signature) := σ.nary 0

-- terms in the language
inductive signature.term (σ : signature)
| var : σ.vars → signature.term
| app  {n : ℕ} (f : σ.nary n) (v : fin n → signature.term) :  signature.term

-- constant terms.
def signature.cterm (σ : signature) : σ.const → σ.term
| c := term.app c fin_zero_elim

@[reducible]
def signature.term.rw : σ.term → σ.vars → σ.term → σ.term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, signature.term.rw (v m) x t in
    term.app f v₂

def signature.term.vars  : σ.term → set σ.vars
| (term.var a) := {a}
| (term.app f v) :=
    let v₂ := λ m, signature.term.vars (v m) in
    ⋃ m, v₂ m

@[reducible]
def signature.term.denotes (t : σ.term) : Prop := t.vars = (∅ : set σ.vars)
@[reducible]
def signature.term.conotes (t : σ.term) := ¬ t.denotes


#check signature.term.denotes

-- a σ.term in the proper sense of the σ.term (pun intended).
def signature.pterm (σ : signature) := subtype {t : σ.term | t.denotes}-- ∧ t.concrete}
def signature.expression (σ : signature) := subtype {t : σ.term | t.conotes}-- ∧ t.concrete}
-- def cterm := subtype term.concrete

theorem rw_eq_of_not_in_vars : ∀ (t₁ t₂ : σ.term) (x : σ.vars), x ∉ t₁.vars → t₁.rw x t₂ = t₁ :=
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

theorem den_rw : ∀ (t₁ t₂ : σ.term) (x : σ.vars), t₁.denotes → t₁.rw x t₂ = t₁ :=
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

def list.vars : list σ.term → set σ.vars
| [] := ∅
| (hd :: tl) := hd.vars ∪ tl.vars

def list.subterms : list σ.term → set σ.term
| [] := ∅
| (hd :: tl) := hd.subterms ∪ tl.subterms

def list.rw : list σ.term → σ.vars → σ.term → list σ.term
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rw x t) :: tl.rw x t

def subterms : set σ.term → set σ.term
| S := ⋃ x ∈ S, signature.term.subterms x

--  formulas
inductive  signature.formula (σ : signature)
| relational {n : ℕ} (r : σ.nrary n) (v : fin n → σ.term) :  signature.formula
| for_all :  σ.vars →  signature.formula →  signature.formula
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

def  signature.formula.rw :  σ.formula → σ.vars → σ.term →  σ.formula
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
def  signature.formula.free :  σ.formula → set σ.vars
| ( signature.formula.relational r v) := ⋃ m, (v m).vars
| ( signature.formula.for_all x φ) := φ.free - {x}
| ( signature.formula.if_then φ ψ) := φ.free ∪ ψ.free
| ( signature.formula.equation t₁ t₂) := t₁.vars ∪ t₂.vars
|  signature.formula.false := ∅

def  signature.formula.substitutable  :  σ.formula → σ.vars → σ.term → Prop
| ( signature.formula.for_all y φ) x t := x ∉ ( signature.formula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| ( signature.formula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t
| _ _ _ := true

-- open and closed  σ.formulas.
def  signature.formula.closed :  σ.formula → Prop
| φ := φ.free = ∅

def  signature.formula.open :  σ.formula → Prop
| φ := ¬ φ.closed

-- atomic and molecular formulas

def signature.formula.atomic :  σ.formula → bool
| (formula.relational r v) := tt
| (formula.equation t₁ t₂) := tt
| formula.false := tt
| _ := ff

def signature.formula.molecular : σ.formula → bool
| (formula.for_all x φ) := ff
| (formula.if_then φ ψ) := φ.molecular && ψ.molecular
| _ := tt

def signature.proposition (σ : signature) := subtype {φ : σ.formula | φ.molecular}

def  signature.formula.vars :  σ.formula → set σ.vars
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
def abstract_in : σ.vars → set  σ.formula → Prop
| x S := x ∉ (⋃ φ ∈ S,  signature.formula.free φ)

-- construct the generalization of a  σ.formula from a list of variables.
-- This is just a fold but, I like being explicit in my folds when possible.
def  signature.formula.generalize :  σ.formula → list σ.vars →  σ.formula
| φ [] := φ
| φ (x::xs) :=  signature.formula.for_all x $ φ.generalize xs

theorem formula_rw : ∀ {φ :  σ.formula} {x : σ.vars}, x ∉ φ.free → ∀(t : σ.term),φ.rw x t = φ :=
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
            (x : σ.vars) (xf : x ∈ φ.free)
            (abs : abstract_in x Γ)
            (h : proof Γ φ)
             : proof Γ ( signature.formula.for_all x φ)
| for_all_elim
            (Γ : set  σ.formula) (φ :  σ.formula)
            (x : σ.vars) --(xf : x ∈ φ.free)
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
            (x : σ.vars) (xf : x ∈ φ.free)
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

end logic