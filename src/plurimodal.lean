-- import syntax order.complete_boolean_algebra data.vector
-- universe u


-- namespace logic

-- open set vector

-- variable (σ : signature)

-- def signature.nmary (n : ℕ) := subtype {r : σ.modality | σ.marity r = n}

-- inductive signature.event 
-- | var : σ.vars → signature.event
-- | func  {n : ℕ} (f : σ.nary n) (v : fin n → signature.event) :  signature.event
-- | rel   {n : ℕ} (R : σ.nrary n) (v : fin n → signature.event) :  signature.event
-- | mod   {n : ℕ} (diamond : σ.nmary n) (v : fin n → signature.event) :  signature.event
-- | for_all  :  σ.vars →  signature.event →  signature.event
-- | if_then  :  signature.event →  signature.event →  signature.event
-- | equation : signature.event →  signature.event →  signature.event
-- | false    :  signature.event


-- #check signature.event

-- def sup_preserving {α}{n} : ((fin n → set α) → set α) → Prop := sorry


-- structure signature.model (α : Type u) :=
--     -- functional interpretation
--     (I₁ : Π {n}, σ.nary n → (fin n → set α) → set α)
--     -- relational interpretation
--     (I₂ : Π {n}, σ.nrary n → (fin n → set α) → Prop)
--     -- modalities interpretation
--     (I₃ : Π {n}, σ.nmary n → (fin n → set α) → set α)
--     -- modalities axiom
--     (mod : ∀ {n} (d : σ.nmary n), sup_preserving (I₃ d) )

-- def signature.vasgn (α : Type u) := σ.vars → α
-- variable {α : Type u}

-- local notation `model` :=  signature.model σ α

-- def ref' (M : model) (asg : σ.vasgn (set α)) : σ.event → set α
-- | (event.var a) := asg a
-- | (@event.func _ 0 f v) := M.I₁ f fin_zero_elim
-- | (@event.func _ (n+1) f v) := let v₂ := λ k, ref'  (v k)
--                                in M.I₁ f v₂
-- | (@event.rel _ 0 R  v) := _
-- | (event.mod diamond v) := _
-- | (event.for_all a a_1) := _
-- | (event.if_then a a_1) := _
-- | (event.equation a a_1) := _
-- | event.false := _




-- end logic