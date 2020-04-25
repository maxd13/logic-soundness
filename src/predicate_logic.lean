import data.set.countable tactic.find tactic.tidy tactic.ring
universe u

-- We introduce a much simplified version of
-- untyped first order (minimal) predicate logic.

-- make all propositions decidable. 
-- Allows us to freely use ifs like in Haskell
-- but then we must add noncomputable to all functions
-- local attribute [instance] classical.prop_decidable


namespace logic

open logic list tactic set

section formulas
parameters {functional_symbol : Type u} [decidable_eq functional_symbol]
parameter {relational_symbol : Type u}
parameter {arity : functional_symbol -> ℕ}
parameter {rarity : relational_symbol -> ℕ}

-- arity types
def is_constant (f : functional_symbol) := arity f = 0
def nary (n : ℕ) := subtype {f : functional_symbol | arity f = n}
def nrary (n : ℕ) := subtype {r : relational_symbol | rarity r = n}
@[reducible]
def const := nary 0

-- terms in the language
inductive term
| var : ℕ → term
| app  {n : ℕ} (f : nary n) (v : fin n → term) :  term

-- constant terms.
def nary.term : const → term
| c := term.app c fin_zero_elim

@[reducible]
def term.rw : term → ℕ → term → term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, term.rw (v m) x t in
    term.app f v₂

def term.rw_const : term → const → ℕ → term
| (@term.app _ _ _  0 f _) c x := if f = c then term.var x else f.term
| (@term.app _ _ _ (n+1) f v) c x := 
    let v₂ := λ m, term.rw_const (v m) c x in
    term.app f v₂
| t _ _ := t

def term.vars : term → set ℕ
| (term.var a) := {a}
| (term.app f v) :=
    let v₂ := λ m, term.vars (v m) in
    ⋃ m, v₂ m

@[reducible]
def term.denotes (t : term) := t.vars = ∅
@[reducible]
def term.conotes (t : term) := ¬ t.denotes

-- a term in the proper sense of the term (pun intended).
def pterm := subtype {t : term | t.denotes}-- ∧ t.concrete}
def expression := subtype {t : term | t.conotes}-- ∧ t.concrete}
-- def cterm := subtype term.concrete

-- theorem aux_rw : ∀ (t₁ t₂ : term) (x : ℕ), x ∉ t₁.vars → t₁.rw x t₂ = t₁ :=
--     sorry

-- theorem trivial_rw : ∀ (t:term) (x), t.rw x (term.var x) = t :=
--     sorry

theorem den_rw : ∀ (t₁ t₂ : term) (x : ℕ), t₁.denotes → t₁.rw x t₂ = t₁ :=
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
        dunfold term.rw, 
        simp[c₂],
end

def term.subterms : term → set term
| (term.app f v) := 
    let v₂ := λ m, term.subterms (v m) in
    (⋃ m, v₂ m) ∪ {(term.app f v)}
| t := {t}

def list.vars : list term → set ℕ
| [] := ∅
| (hd :: tl) := hd.vars ∪ tl.vars

def list.subterms : list term → set term
| [] := ∅
| (hd :: tl) := hd.subterms ∪ tl.subterms

def list.rw : list term → ℕ → term → list term
| [] _ _:= ∅
| (hd :: tl) x t := (hd.rw x t) :: tl.rw x t

def subterms : set term → set term
| S := ⋃ x ∈ S, term.subterms x

-- formulas
inductive uformula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : uformula
| false : uformula
| for_all :  ℕ → uformula → uformula
| if_then : uformula → uformula → uformula

def uformula.not (φ) := uformula.if_then φ uformula.false

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

instance uformula.has_exp : has_exp uformula := ⟨uformula.if_then⟩
local notation `∼` := uformula.not

def uformula.rw : uformula → ℕ → term → uformula
| (uformula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
    uformula.relational r v₂
| (uformula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
    uformula.for_all y ψ
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.rw x t) (ψ.rw x t)
| φ _ _ := φ

-- free variables
def uformula.free : uformula → set ℕ
| (uformula.relational r v) := ⋃ m, (v m).vars
| (uformula.for_all x φ) := φ.free - {x}
| (uformula.if_then φ ψ) := φ.free ∪ ψ.free
| _ := ∅

def uformula.substitutable  : uformula → ℕ → term → Prop
| (uformula.relational r v) _ _ := true
| uformula.false _ _ := true
| (uformula.for_all y φ) x t := x ∉ (uformula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| (uformula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t

-- open and closed formulas.
def uformula.closed : uformula → Prop
| φ := φ.free = ∅

def uformula.open : uformula → Prop
| φ := ¬ φ.closed

def uformula.vars : uformula → set ℕ
| (uformula.for_all x φ) := φ.free ∪ {x}
| (uformula.if_then φ ψ) := φ.vars ∪ ψ.vars
| φ := φ.free

def uformula.terms : uformula → set term
| (uformula.relational r v) := list.subterms (of_fn v)
| (uformula.for_all x φ) := φ.terms ∪ {term.var x}
| (uformula.if_then φ ψ) := φ.terms ∪ ψ.terms
| _ := ∅

def term.abstract_in : term → set uformula → Prop
| t S := t ∉ (⋃ φ ∈ S, uformula.terms φ)

def nat.abstract_in : ℕ → set uformula → Prop
| x S := x ∉ (⋃ φ ∈ S, uformula.free φ)

-- construct the generalization of a formula from a list of variables.
-- This is just a fold but, I like being explicit in my folds when possible.
def uformula.generalize : uformula → list ℕ → uformula
| φ [] := φ
| φ (x::xs) := uformula.for_all x $ φ.generalize xs

-- theorem uformula_rw : ∀ (φ : uformula)(t : term) (x : ℕ), x ∉ φ.free → φ.rw x t = φ :=
--     sorry

lemma trivial_uformula_rw : ∀ {φ:uformula} {x}, φ.rw x (term.var x) = φ :=
    begin
        intros φ x,
        induction φ;
        -- tactic.unfreeze_local_instances,
        dunfold uformula.rw;
        try{simp},
        -- any_goals{assumption},
            -- convert h,
            ext,
            induction (φ_v x_1);
            dunfold term.rw,
            by_cases x = a;
                simp [h],
            simp,
            ext,
            exact ih x_2,
        rw φ_ih,
        simp,
            simp [φ_ih_a, φ_ih_a_1],
    end

-- deductive consequence of uformulas: Γ ⊢ φ
inductive entails : set uformula → uformula → Prop
| reflexive (Γ : set uformula) (φ : uformula)(h : φ ∈ Γ) : entails Γ φ
| transitivity (Γ Δ : set uformula) (φ : uformula)
               (h₁ : ∀ ψ ∈ Δ, entails Γ ψ)
               (h₂ : entails Δ φ) :  entails Γ φ
| modus_ponens
            (φ ψ : uformula) (Γ : set uformula)
            (h₁ : entails Γ (φ ⇒ ψ))
            (h₂ : entails Γ φ)
             : entails Γ ψ
| intro
            (φ ψ : uformula) (Γ : set uformula)
            (h : entails (Γ ∪ {φ}) ψ)
             : entails Γ (φ ⇒ ψ)
| for_all_intro
            (Γ : set uformula) (φ : uformula)
            (x : ℕ) (xf : x ∈ φ.free)
            (abs : nat.abstract_in x Γ)
            (h : entails Γ φ)
             : entails Γ (uformula.for_all x φ)
| for_all_elim
            (Γ : set uformula) (φ : uformula)
            (x : ℕ) --(xf : x ∈ φ.free)
            (t : term) --(den : t.denotes)
            (h : entails Γ (uformula.for_all x φ))
             : entails Γ (φ.rw x t)
-- def minimal.theorem (φ : uformula) := entails ∅ φ

local infixr `⊢`:55 := λ Γ (φ : uformula), entails Γ φ

variables (Γ : set uformula) (φ : uformula)

-- theorem generalization_theorem : ∀ (x : ℕ), (∀ (ψ:uformula), ψ ∈ Γ → x ∉ ψ.free) → Γ ⊢ φ → Γ ⊢ (uformula.for_all x φ) :=
-- begin
--     intros x hx h,
--     apply entails.for_all_intro Γ φ x _ _,
--     -- dunfold nat.abstract_in,
--     -- simp,
--     assumption,
--     intros ψ H,
--     specialize hx ψ H,
--     exact hx,
--     rw trivial_uformula_rw,
--     exact h,
-- end

theorem self_entailment : entails Γ (φ ⇒ φ) :=
begin
    apply entails.intro,
    apply entails.reflexive (Γ∪{φ}) φ,
    simp
end

variables (Δ : set uformula) (ψ : uformula)

-- theorem monotonicity : Δ ⊆ Γ → entails Δ ψ → entails Γ ψ :=
-- begin
--     intros H h,
--     -- induction on the possible ways in which
--     -- Δ could prove ψ
--     induction h,
--     -- case it was proven by reflection
--         apply entails.reflexive Γ h_φ,
--         exact H h_h,
--     -- case it was proven by transitivity
--         apply entails.transitivity Γ h_Δ h_φ,
--         intros ψ₂ elem,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by and_intro
--         apply entails.and_intro,-- h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by and_elim_left
--         apply entails.and_elim_left h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by and_elim_right
--         apply entails.and_elim_right h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by or_intro_left
--         apply entails.or_intro_left h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by or_intro_right
--         apply entails.or_intro_right h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by or_elim
--         apply entails.or_elim,-- h_φ h_ψ h_δ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by modus ponens
--         apply entails.modus_ponens h_φ h_ψ Γ,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by intro
--         have c : entails h_Γ (h_φ ⇒ h_ψ),
--             apply entails.intro h_φ h_ψ h_Γ,
--             assumption,
--         apply entails.transitivity Γ h_Γ (h_φ ⇒ h_ψ),
--             intros ψ₂ elem,
--             have c₂ := H elem,
--             exact entails.reflexive Γ ψ₂ c₂,
--         assumption,
--     -- case it was proven by true_intro
--         exact entails.true_intro Γ,
--     -- case it was proven by for_all_intro
--         apply entails.for_all_intro Γ h_φ h_x h_xf h_c,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by for_all_elim
--         apply entails.for_all_elim Γ h_φ h_x h_xf,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by exists_intro
--         apply entails.exists_intro Γ h_φ h_x h_xf h_t,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by exists_elim
--         apply entails.exists_elim Γ h_φ h_ψ h_x h_xf,
--         repeat {assumption <|> apply_assumption},
--     -- case it was proven by identity_intro
--         apply entails.identity_intro Γ h_t,
--     -- case it was proven by identity_elim
--         apply entails.identity_elim Γ h_φ h_x h_xf h_t₁ h_t₂,
--         repeat {assumption <|> apply_assumption},
-- end

section semantics

parameters {α : Type u} [nonempty α]

-- functional interpretation
def fint  {n : ℕ} := nary n → (fin n → α) → α
-- relational interpretation
def rint {n : ℕ} := nrary n → (fin n → α) → Prop
-- variable assignment
def vasgn := ℕ → α

-- parameter [exists_ass : nonempty vasgn]

structure model :=
    (I₁ : Π {n}, @fint n)
    (I₂ : Π {n}, @rint n)

-- @[reducible]
def model.reference' (M : model) : term → vasgn → α
| (term.var x) asg := asg x
| (@term.app _ _ _  0 f _) _ := model.I₁ M f fin_zero_elim
| (@term.app _ _ _  (n+1) f v) asg := let v₂ := λ k, model.reference' (v k) asg
                                             in model.I₁ M f v₂

def model.reference (M : model) : pterm → α :=
    begin
        intro t,
        obtain ⟨t, den⟩ := t,
        induction t,
            simp [set_of] at den,
            revert den,
            dunfold term.denotes term.vars,
            intro den,
            replace den := eq_empty_iff_forall_not_mem.mp den,
            specialize den t,
            simp at den,
            contradiction,
        cases t_n,
            exact model.I₁ M t_f fin_zero_elim,
        have den_v : ∀ x, (t_v x).denotes,
            admit,
        have ih := λ x, t_ih x (den_v x),
        exact model.I₁ M t_f ih,
    end

def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y

def model.satisfies' : model → uformula → vasgn → Prop
| M (uformula.relational r v) asg := 
          M.I₂ r $ λm,  M.reference' (v m) asg
| M uformula.false _ := false
| M (uformula.for_all x φ) ass :=
    ∀ (a : α),
    M.satisfies' φ (ass.bind x a)
| M (uformula.if_then φ ψ) asg :=
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x → y


@[reducible]
def model.satisfies : model → uformula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

local infixr `⊨₁`:55 := model.satisfies
local infixr `⊢`:55 := entails

lemma false_is_unsat : ¬∃ M : model, M ⊨₁ uformula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    apply nonempty.elim _inst_2,
    intro x,
    exact h (λ_, x),
end

def model.for : model → set uformula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨₁ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ (M : model) ass, (∀ ψ ∈ Γ, M.satisfies' ψ ass) → M.satisfies' φ ass

local infixr `⊨`:55 := theory.follows

lemma bind : ∀ {ass : vasgn} {x : ℕ}, ass.bind x (ass x) = ass :=
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

lemma bind₃ : ∀ {ass : vasgn} {x y : ℕ} {a b} {M:model} {φ}, 
              M.satisfies' φ (ass.bind x a) →
              M.satisfies' φ (ass.bind y b) →
              M.satisfies' φ ((ass.bind x a).bind y b) :=
    begin
        intros ass x y a b M φ,-- h₁ h₂,
        by_cases diff : x = y,
            rw diff,
            rw bind₂,
            simp,
        induction φ;
        dunfold model.satisfies' vasgn.bind;
        intros h₁ h₂,
        swap,
            contradiction,
        all_goals{admit},
        -- cases φ_n,
        --     admit,
        
        -- convert h₂,
        -- induction φ_n,
        --     convert h₂,
        --     ext z,
        --     exact fin_zero_elim z,
        -- induction φ_v z;
        -- dunfold model.reference',
            -- simp [h, bind₂],
    end

lemma bind₅ : ∀ {M:model} {φ:uformula}{ass : vasgn}{x : ℕ}{a},
              x ∉ φ.free →
              (M.satisfies' φ (ass.bind x a) ↔
              M.satisfies' φ ass)
              :=
begin
    intros M φ ass x a,
    -- apply annoying;
    -- revert h₁;
    induction φ;
    dunfold uformula.free model.satisfies';
    simp;
    intros h₀,
    swap 3,
    replace h₀ := not_or_distrib.mp h₀,
    obtain ⟨h₀, h₁⟩ := h₀,
    constructor;
    intros h₂ h₃;
    have ih₁ := φ_ih_a h₀;
    have ih₂ := φ_ih_a_1 h₁,
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
            dunfold term.vars model.reference' vasgn.bind;
            intro h₀,
                simp at h₀,
                replace h₀ := ne.symm h₀,
                simp [h₀],
            cases n;
                dunfold model.reference',
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
    rename _inst_1 dont_annoy,
    all_goals{
        by_cases (x ∈ φ_a_1.free),
            specialize h₁ a₂,
            revert h₁,
            rw (h₀ h),
            rw bind₂,
            intro h₁,
            exact h₁,
        have ih := φ_ih h,
    },
    swap,
        have c := h₁ (ass φ_a),
        rw bind at c,
        replace ih := ih.2 c,
        specialize h₁ a₂,
        exact bind₃ ih h₁,
    have c := h₁ (ass.bind x a φ_a),
    rw bind at c,
    replace ih := ih.mp c,
    specialize h₁ a₂,
    -- set w := (vasgn.bind (vasgn.bind ass x a) φ_a a₂),
    -- set g := (vasgn.bind ass x a),
    -- set f := (vasgn.bind ass φ_a a₂),
    -- simp [vasgn.bind] at *,
    admit,

end

lemma fundamental : ∀ y x (M : model) ass, nat.abstract_in y Γ → 
            (∀ φ ∈ Γ, M.satisfies' φ ass) →
            ( ∀φ ∈ Γ, M.satisfies' φ (ass.bind y x))
            :=
        
begin
    intros y x M ass h₁ h₂ φ H,
    simp [nat.abstract_in] at h₁,
    specialize h₁ φ H,
    specialize h₂ φ H,
    exact (bind₅ h₁).2 h₂,
end

-- lemma bind_rw : ∀ {M:model} {t₁ t₂ : term} x ass, M.reference' (t₁.rw x t₂) ass = M.reference' t₁ (ass.bind x (M.reference' t₂ ass)) :=
-- begin
--     intros M t₁ t₂ x ass,
--     induction t₁;
--     dunfold term.rw model.reference' vasgn.bind,
--         by_cases x = t₁;
--             simp [h],
--         dunfold model.reference',
--         replace h := ne.symm h,
--         simp [h],
--     simp,
--     cases t₁_n;
--         dunfold model.reference',
--         refl,
--     simp,
--     congr,
--     ext,
--     have ih := t₁_ih x_1,

-- end

-- lemma uformula.rw.semantics (φ : uformula) 
--                             (x : ℕ)
--                             (h₀ : x ∈ φ.free)
--                             (ass : vasgn)
--                             (M : model)
--                             (t : term)
--                             : 
--                             M.satisfies' φ ass →
--                             M.satisfies' (φ.rw x t)
--                             (ass.bind x (M.reference' t ass))
--                             :=
-- begin
--     -- intro h,
--     induction φ;
--     dunfold uformula.rw;
--     dunfold model.satisfies';
--     intro h,
--         convert h,
--         ext,
--         induction φ_v x_1;
--         dunfold term.rw model.reference',
--             by_cases hyp : x = a;
--                 simp [hyp],
--                 rw ←hyp,
-- end
    -- have c₁ : (λ (m : fin φ_n), M.reference' (φ_v m) ass) = (flip M.reference' ass) ∘ φ_v,
    --     dsimp [flip, function.comp],
    --     refl,
--     -- have c : ∀ m, (M.reference' ((φ_v m).rw x t.val) (ass.bind x (M.reference' t.val ass))) = M.reference' (φ_v m) ass,
--     --     focus {
--     --         intro m,
--     --         induction (φ_v m);
--     --         dunfold term.rw;
--     --         dunfold vasgn.bind,
--     --         dunfold model.reference',
--     --         by_cases h₂ : x = a;
--     --             simp [h₂],
--     --             obtain ⟨t, pt₁, pt₂⟩ := t,
--     --             induction t,
--     --                 dunfold model.reference',
--     --                 simp,
                
    --             revert pt₁,
    --             dunfold term.denotes,
    --             dunfold term.vars,
    --             simp,
    --                 revert pt₂,
    --                 dunfold term.concrete,
    --                 contradiction,
    --             simp,
    --             induction t_n;
    --             dunfold model.reference',
                
    --                 -- dunfold model.reference',

    --     }

            

-- end


-- lemma semantic_generalization : ∀ (M:model) x, M ⊨₁ φ → M ⊨₁ (uformula.for_all x φ) :=
--     begin
--         intros M x h₁,
--         dunfold model.satisfies model.satisfies',
--         intros _ _ asg _ _,
--         induction φ;
--         exact h₁ asg,
--     end

-- lemma semantic_generalization₂ : ∀ (M:model) x ass, x ∈ φ.free → M.satisfies' φ ass → M.satisfies' (uformula.for_all x φ) ass :=
--     begin
--         intros M x ass h₁ h₂ e asg h₃ h₄,
--         tactic.unfreeze_local_instances,
--         induction φ;
--         dunfold model.satisfies' uformula.free at *,
--     end

-- So pretty.

-- lemma universal_generalization : ∀ (M:model) (ass:vasgn) x y, M.satisfies' (uformula.rw φ x (term.var y)) ass → M.satisfies' (uformula.for_all x φ) ass :=
--     begin
--         intros M ass x y h₁ a asg h₂ h₃,
--         induction φ;
--         revert h₁;
--         dunfold uformula.rw model.satisfies';
--         -- try{simp};
--         intro h₁,
--             convert h₁,
--             ext,
--             induction φ_v x_1;
--                 dunfold term.rw model.reference',
--                 by_cases x = a_1;
--                 simp [h];
--                 dunfold model.reference',
--                     admit,
--                 replace h : a_1 ≠ x := ne.symm h,
--                 rw (h₃ a_1 h),
--             cases n;
--                 dunfold model.reference';
--                 simp,
--             congr,
--             ext,
--             exact ih x_2,
--         contradiction,
--             intros a ass h₄ h₅,
--             have sat := h₁ a ass h₄,
--             admit,
--         admit,
--     end

lemma aux : ∀ {M:model} {ass:vasgn} {x t} {φ:uformula}, M.satisfies' (φ.rw x t) ass ↔ M.satisfies' φ (ass.bind x (M.reference' t ass)) :=
begin
    intros M ass x t φ,
    induction φ;
    dunfold uformula.rw model.satisfies';
    try{simp};
    constructor;
    intro h,
        convert h,
        ext y,
        induction φ_v y;
        dunfold term.rw model.reference' vasgn.bind,
            by_cases eq : a = x;
                simp [eq],
            replace eq := ne.symm eq,
            simp [eq],
            dunfold model.reference',
            refl,
        simp,
        cases n,


end

theorem soundness : Γ ⊢ φ → Γ ⊨ φ :=
begin
    intros entails M ass h,
    induction entails generalizing ass,
    -- case reflexive
    exact h entails_φ entails_h,
    -- case transitivity
    apply entails_ih_h₂,
    intros ψ H,
    exact entails_ih_h₁ ψ H ass h,
    -- case modus ponens
    have c₁ := entails_ih_h₁ ass h,
    have c₂ := entails_ih_h₂ ass h,
    -- intro ass,
    -- specialize c₁ ass,
    -- specialize c₂ ass,
    revert c₁,
    dunfold model.satisfies',
    simp,
    intro c₁,
    exact c₁ c₂,
    -- case intro
    intro h₂,
    have sat := entails_ih,
    apply sat,
    intros ψ H,
    cases H,
    exact h ψ H,
    simp at H,
    rwa H,
    -- case universal intro
    intro x,
    have c := fundamental entails_Γ entails_x x,
    specialize c M ass entails_abs h,
    have ih := entails_ih (ass.bind entails_x x),
    apply ih,
    exact c,
    -- exact universal_generalization entails_φ M ass entails_x entails_y_1 sat,

    -- case universal elim
    have ih := entails_ih ass h,
    clear entails_ih,
    revert ih,
    dunfold model.satisfies',
    intro ih,
    set ref := M.reference' entails_t ass,
    specialize ih ref,
    exact aux.2 ih,
    -- induction entails_φ generalizing ass;
    -- dunfold uformula.rw model.satisfies';
    -- intro ih,
    --     convert ih (M.reference' entails_t ass),
    --     ext y,
    --     induction entails_φ_v y;
    --     dunfold term.rw model.reference',
    --         by_cases entails_x = a;
    --             simp [vasgn.bind, h],
    --         dunfold model.reference',
    --         replace h := ne.symm h,
    --         simp [h],
    --     cases n;
    --         dunfold model.reference',
    --         refl,
    --     simp at *,
    --     congr,
    --     ext z,
    --     exact ih_1 z,
    -- tactic.unfreeze_local_instances,
    -- obtain ⟨x⟩ := _inst_2,
    -- exact ih x,
    --     intro a,
    --     by_cases eq : entails_φ_a = entails_x;
    --         simp[eq],
    --         specialize ih (ass entails_x) a,
    --         simp [eq, bind₂] at ih,
    --         exact ih,
    --     -- here we will need the fundamental lemma
    --     admit,
    -- simp at *,
    --         -- simp [ne.symm, h],
    -- -- clear h,
    -- -- clear entails_ih,
    
    -- -- revert ass,
    -- -- exact semantic_generalization φ M entails_x sat,
    -- -- tactic.unfreeze_local_instances,
    -- -- dunfold nat.abstract_in at *,
    -- -- revert asg,
    -- -- revert x,
    -- -- admit,
    -- -- focus {
    -- --     induction entails_φ;
    -- --     revert sat;
    -- --     dunfold model.satisfies';
    -- --     try{simp};
    -- --     intro sat;
    -- --     convert sat;
    -- --     try{simp},
    -- --         ext,
    -- --         focus {
    -- --             induction (entails_φ_v x_1),
    -- --                 dunfold model.reference',
    -- --                 revert asg,
    -- --             -- dunfold term.rw,
    -- --             by_cases entails_x = a,
    -- --             -- simp [h],
                
    -- --         },
    -- --     revert sat;
    -- --     dunfold uformula.rw;
    -- --     dunfold model.satisfies';
    -- --     try{simp},
    -- --         intro sat,
    -- -- },
    -- -- admit,
    -- -- case universal elim
    -- -- focus {
    -- --     induction entails_φ;
    -- --     have sat := entails_ih h;
    -- --     revert sat;
    -- --     dunfold uformula.rw; try{simp},
    -- --     -- I cant go any further applying strategies to
    -- --     -- all goals because the linter gets very slow.
    -- --     dunfold model.satisfies', try{simp},
    -- --         intro sat,
    -- -- },
    -- -- have sat := entails_ih h,
    -- admit,
end



end semantics

section consistency
end consistency

end formulas
end logic