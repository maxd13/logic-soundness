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
parameters {functional_symbol : Type u} [decidable_eq functional_symbol]
parameter {relational_symbol : Type u}
parameter {arity : functional_symbol → ℕ}
parameter {rarity : relational_symbol → ℕ}

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
inductive formula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : formula
| false : formula
| for_all :  ℕ → formula → formula
| if_then : formula → formula → formula

def formula.not (φ) := formula.if_then φ formula.false

reserve infixr ` ⇒ `:55
class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp

instance formula.has_exp : has_exp formula := ⟨formula.if_then⟩
local notation `∼` := formula.not

def formula.rw : formula → ℕ → term → formula
| (formula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
    formula.relational r v₂
| (formula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
    formula.for_all y ψ
| (formula.if_then φ ψ) x t := formula.if_then (φ.rw x t) (ψ.rw x t)
| φ _ _ := φ

-- free variables
def formula.free : formula → set ℕ
| (formula.relational r v) := ⋃ m, (v m).vars
| (formula.for_all x φ) := φ.free - {x}
| (formula.if_then φ ψ) := φ.free ∪ ψ.free
| _ := ∅

def formula.substitutable  : formula → ℕ → term → Prop
| (formula.relational r v) _ _ := true
| formula.false _ _ := true
| (formula.for_all y φ) x t := x ∉ (formula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| (formula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t

-- open and closed formulas.
def formula.closed : formula → Prop
| φ := φ.free = ∅

def formula.open : formula → Prop
| φ := ¬ φ.closed

def formula.vars : formula → set ℕ
| (formula.for_all x φ) := φ.free ∪ {x}
| (formula.if_then φ ψ) := φ.vars ∪ ψ.vars
| φ := φ.free

def formula.terms : formula → set term
| (formula.relational r v) := list.subterms (of_fn v)
| (formula.for_all x φ) := φ.terms ∪ {term.var x}
| (formula.if_then φ ψ) := φ.terms ∪ ψ.terms
| _ := ∅

def term.abstract_in : term → set formula → Prop
| t S := t ∉ (⋃ φ ∈ S, formula.terms φ)

@[reducible]
def nat.abstract_in : ℕ → set formula → Prop
| x S := x ∉ (⋃ φ ∈ S, formula.free φ)

-- construct the generalization of a formula from a list of variables.
-- This is just a fold but, I like being explicit in my folds when possible.
def formula.generalize : formula → list ℕ → formula
| φ [] := φ
| φ (x::xs) := formula.for_all x $ φ.generalize xs

theorem formula_rw : ∀ {φ : formula} {x : ℕ}, x ∉ φ.free → ∀(t : term),φ.rw x t = φ :=
    begin
        intros φ x h t,
        revert h,
        induction φ;
        dunfold formula.free formula.rw;
        simp;
        intro h,
            ext y,
            specialize h y,
            revert h,
            induction φ_v y;
            dunfold term.rw term.vars;
            intro h;
            simp at *,
                simp[h],
            ext z,
            specialize h z,
            specialize ih z,
            exact ih h,
        classical,
        rename _inst_1 dont_annoy,
        by_cases eq₁ : x ∈ φ_a_1.free,
            simp [h eq₁],
        by_cases eq₂ : φ_a = x;
            simp [eq₂],
        exact φ_ih eq₁,
            push_neg at h,
            obtain ⟨h₁, h₂⟩ := h,
            constructor;
            apply_assumption;
            assumption,
    end

lemma trivial_formula_rw : ∀ {φ:formula} {x}, φ.rw x (term.var x) = φ :=
    begin
        intros φ x,
        induction φ;
        -- tactic.unfreeze_local_instances,
        dunfold formula.rw;
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

-- deductive consequence of formulas: Γ ⊢ φ
inductive entails : set formula → formula → Prop
| reflexive (Γ : set formula) (φ : formula)(h : φ ∈ Γ) : entails Γ φ
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
            (abs : nat.abstract_in x Γ)
            (h : entails Γ φ)
             : entails Γ (formula.for_all x φ)
| for_all_elim
            (Γ : set formula) (φ : formula)
            (x : ℕ) --(xf : x ∈ φ.free)
            (t : term) (sub : φ.substitutable x t)
            (h : entails Γ (formula.for_all x φ))
             : entails Γ (φ.rw x t)

local infixr `⊢`:55 := entails

variables (Γ : set formula) (φ : formula)

theorem self_entailment : Γ ⊢ (φ ⇒ φ) :=
begin
    apply entails.intro,
    apply entails.reflexive (Γ∪{φ}) φ,
    simp
end

variables (Δ : set formula) (ψ : formula)

theorem monotonicity : Δ ⊆ Γ → Δ ⊢ ψ → Γ ⊢ ψ :=
begin
    intros H h,
    have c₁ : ∀ φ ∈ Δ, entails Γ φ,
        intros φ hφ,
        apply entails.reflexive Γ φ,
        exact H hφ,
    apply entails.transitivity;
    assumption,
end

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
            intro x,
            simp [set_of] at den,
            revert den,
            dunfold term.denotes term.vars,
            simp,
            intro den,
            have c := set.subset_Union (logic.term.vars ∘ t_v) x,
            simp [den] at c,
            -- could have used the set lemma,
            -- but library search finished
            -- this one off.
            exact eq_bot_iff.mpr c,
        have ih := λ x, t_ih x (den_v x),
        exact model.I₁ M t_f ih,
    end

def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y

def model.satisfies' : model → formula → vasgn → Prop
| M (formula.relational r v) asg := 
          M.I₂ r $ λm,  M.reference' (v m) asg
| M formula.false _ := false
| M (formula.for_all x φ) ass :=
    ∀ (a : α),
    M.satisfies' φ (ass.bind x a)
| M (formula.if_then φ ψ) asg :=
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x → y


@[reducible]
def model.satisfies : model → formula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

local infixr `⊨₁`:55 := model.satisfies
local infixr `⊢`:55 := entails

lemma false_is_unsat : ¬∃ M : model, M ⊨₁ formula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    apply nonempty.elim _inst_2,
    intro x,
    exact h (λ_, x),
end

def model.for : model → set formula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨₁ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ (M : model) ass, (∀ ψ ∈ Γ, M.satisfies' ψ ass) → M.satisfies' φ ass

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

lemma bind₅ : ∀ {M:model} {φ:formula}{ass : vasgn}{x : ℕ}{a},
              x ∉ φ.free →
              (M.satisfies' φ (ass.bind x a) ↔
              M.satisfies' φ ass)
              :=
begin
    intros M φ ass x a,
    induction φ generalizing ass;
    dunfold formula.free model.satisfies';
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


lemma aux : ∀ {M:model} {ass:vasgn} {x t} {φ:formula}, M.satisfies' (φ.rw x t) ass ↔ M.satisfies' φ (ass.bind x (M.reference' t ass)) :=
begin
    intros M ass x t φ,
    classical,
    rename _inst_1 dont_annoy,
    by_cases xf : x ∉ φ.free,
        rw formula_rw xf t,
        simp[bind₅ xf],
    simp at xf,
    -- no more need for classical reasoning.
    clear _inst,
    revert xf,
    induction φ generalizing ass;
    dunfold formula.rw model.satisfies';
    try{simp};
    intro xf,
    focus {
        constructor;
        intro h,
        all_goals{
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
        cases n;
            dunfold model.reference';
            simp,
        congr,
        ext z,
        exact ih z,},
    },
    focus{
        revert xf,
        dunfold formula.free,
        simp_intros xf,
        obtain ⟨xf₁, xf₂⟩ := xf,
        replace xf₂ := ne.symm xf₂,
        simp [xf₂],
        constructor;
        intros h a,
            -- specialize h a,
            -- -- simp [bind] at h,
            -- have ih := (φ_ih xf₁).mp h,
            -- rw bind_symm,
            -- revert ih,
            -- induction t;
            -- dunfold model.reference' vasgn.bind;
            -- intro ih,
            admit,
        set asg := ass.bind x (M.reference' t ass),
        specialize h (asg φ_a),
        simp [bind] at h,
        have ih := (φ_ih xf₁).2 h,
        admit,
        
        
    },
    admit,
end

-- So pretty.

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
    -- dunfold formula.rw model.satisfies';
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
    -- --     dunfold formula.rw;
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
    -- --     dunfold formula.rw; try{simp},
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