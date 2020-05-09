import syntax
universe u

namespace logic
-- namespace semantics
open list tactic set

structure signature.structure (σ : signature) (α : Type u) [nonempty α] :=
    -- functional interpretation
    (I₁ : Π {n}, σ.nary n → (fin n → α) → α)
    -- relational interpretation
    (I₂ : Π {n}, σ.nrary n → (fin n → α) → Prop)

variables {σ : signature} {α : Type u} [nonempty α]
-- variable assignment
def signature.vasgn (σ : signature) (α : Type u) := σ.vars → α

#check signature.term.var

-- @[reducible]
def signature.structure.reference' (M : σ.structure α) : σ.term → σ.vasgn α → α
| (signature.term.var x) asg := asg x
| (@signature.term.app _ 0 f _) _ := M.I₁ f fin_zero_elim
| (@signature.term.app _  (n+1) f v) asg := let v₂ := λ k, signature.structure.reference' (v k) asg
                                    in M.I₁ f v₂


#check signature.structure.reference'

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

def signature.vasgn.bind (ass : σ.vasgn α) (x : σ.vars) (val : α) : σ.vasgn α :=
    λy, if y = x then val else ass y

def signature.structure.satisfies' : σ.structure α →  σ.formula → σ.vasgn α → Prop
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
| M φ := ∀ (ass : σ.vasgn α), M.satisfies' φ ass

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

variables (Γ : set σ.formula) (φ : σ.formula)

-- semantic consequence
def theory.follows : Prop :=
    ∀ (M : σ.structure α) (ass : σ.vasgn α),
      (∀ ψ ∈ Γ, M.satisfies' ψ ass) → M.satisfies' φ ass

local infixr `⊨`:55 := @theory.follows σ α _

#check theory.follows

lemma bind_symm : ∀ {ass : σ.vasgn α} {x y : σ.vars} {a b}, x ≠ y → (ass.bind x a).bind y b = (ass.bind y b).bind x a :=
    begin
        intros ass x y a b h,
        simp [signature.vasgn.bind],
        ext z,
        replace h := ne.symm h,
        by_cases eq : z = y;
            simp[eq, h],
    end

lemma bind₁ : ∀ {ass : σ.vasgn α} {x : σ.vars}, ass.bind x (ass x) = ass :=
    begin
        intros ass x,
        simp [signature.vasgn.bind],
        ext y,
        by_cases y = x;
        simp[h],
    end

lemma bind₂ : ∀ {ass : σ.vasgn α} {x : σ.vars} {a b}, (ass.bind x a).bind x b = ass.bind x b :=
    begin
        intros ass x a b,
        simp [signature.vasgn.bind],
        ext y,
        by_cases y = x;
        simp[h],
    end

lemma bind_term : ∀ {M : σ.structure α} {ass : σ.vasgn α} {x : σ.vars} {t : σ.term} {a},
                  x ∉ t.vars →
                  M.reference' t (signature.vasgn.bind ass x a) =
                  M.reference' t ass :=
begin
    intros M ass x t a,
    induction t;
    dunfold signature.term.vars;
    simp;
    intro h,
        dunfold signature.structure.reference' signature.vasgn.bind,
        simp [ne.symm h],
    cases t_n;
        dunfold signature.structure.reference';
        simp,
    congr,
    ext y,
    specialize h y,
    exact t_ih y h,
end

lemma bind₃ : ∀ {M : σ.structure α} {φ: σ.formula}{ass : σ.vasgn α}{x : σ.vars}{a},
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
            dunfold signature.term.vars signature.structure.reference' signature.vasgn.bind;
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

lemma term_rw_semantics : ∀ {M : σ.structure α} {ass:σ.vasgn α} {x} {t₁ t₂ : σ.term},
                          M.reference' (t₁.rw x t₂) ass =
                          M.reference' t₁ (ass.bind x (M.reference' t₂ ass))
                          :=
begin
    intros M ass x t₁ t₂,
    induction t₁,
        dunfold signature.term.rw signature.structure.reference',
        by_cases x = t₁;
            simp [signature.vasgn.bind, h],
        dunfold signature.structure.reference',
        simp [ne.symm h],
    cases t₁_n;
        dunfold signature.term.rw signature.structure.reference';
        simp,
    congr,
    ext y,
    exact t₁_ih y,
end

lemma rw_semantics : ∀ {M : σ.structure α} {ass:σ.vasgn α} {x t} {φ: σ.formula},
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
        dunfold signature.term.rw signature.structure.reference' signature.vasgn.bind,
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
        have ih := @φ_ih (signature.vasgn.bind ass φ_a a) h₂;
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

local infixr `⊢`:55 := proof

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
--     have ass : σ.vasgn α := sorry,
--     specialize h M ass,
--     revert h,
--     dunfold signature.structure.satisfies',
--     simp,
-- end

-- end semantics
end logic