import semantics
universe u

open logic set

-- unused for now:
-- variable (σ : signature) 
-- variable [σ.symbolic]
-- variables (Γ Δ: set σ.formula) (φ ψ: σ.formula)
-- local infixr `⊨`:55 := σ.follows

local infixr `⊢`:55 := proof

-- Here are just a bunch of exercises about logic.

section propositional

local notation `prop` := propositional_signature.formula
local notation `⊥` := @signature.formula.false propositional_signature

-- lifts a natural number to an atomic propositional formula
@[reducible]
def π (n:ℕ) := 
    @signature.formula.relational 
    (propositional_signature ℕ) 0
    ⟨n, by dunfold propositional_signature; simp⟩
    fin_zero_elim

-- Exercise 1

-- 3 sisters Anne, Mary and Claudia went to a party with dresses of different colors.
-- One dressed in blue, another in white and another black. 
-- When they arrived at the party, the host asked them who was who,
-- and they answered. (1) The blue one said: "Anne is in white", 
-- (2) the white one said "I am Mary", (3) the black one said 
-- "Claudia is in white". The host was able to identify how each was dressed
-- considering that: Anne always tells the truth, Mary sometimes tells the
-- truth, Claudia never tells the truth.

-- predicates
inductive color
| blue
| white
| black

-- constants
inductive sister
| anne
| mary
| claudia

def σ : signature :=
{ functional_symbol := sister,
  relational_symbol := color,
  rarity := λ_,1 
}

-- lift sisters to constant terms of the language
def sister.cterm (s : sister) := 
    σ.cterm 
    ⟨ s
    , by dunfold σ
    ; simp
    ⟩

-- lift colors to relational symbols of arity 1
-- in the language
def color.nrary (c : color) : σ.nrary 1 := 
    ⟨c
    , by dunfold σ
    ; simp
    ⟩

-- predicates
def Blue (s : sister) := 
    signature.formula.relational 
    color.blue.nrary
    (λ_, s.cterm)

def White (s : sister) := 
    signature.formula.relational 
    color.white.nrary
    (λ_, s.cterm)

def Black (s : sister) := 
    signature.formula.relational 
    color.black.nrary
    (λ_, s.cterm)

#check Blue

-- formalization of the exercise.
def ex1 : set σ.formula := 
    { -- Anne always tells the truth (1)
      Blue sister.anne ⇒ White sister.anne
      -- Anne always tells the truth (2)
    , White sister.anne ⇒ White sister.mary  
      -- Anne always tells the truth (3) 
    , Black sister.anne ⇒ White sister.claudia
      -- Every color is wore by a sister
    , ((Blue sister.anne).or (Blue sister.mary)).or (Blue sister.claudia)
    , ((White sister.anne).or (White sister.mary)).or (White sister.claudia)
    , ((Black sister.anne).or (Black sister.mary)).or (Black sister.claudia)
    } ∪
    -- No sister wears 2 colors
    ⋃ s : sister, 
    { ((Blue s).and (White s)).not
    , ((Blue s).and (Black s)).not
    , ((Black s).and (White s)).not
    }

-- Here is the solution the host found:
def ex1_solution := ((Black sister.anne).and (Blue sister.mary)).and (White sister.claudia)

-- TODO
-- theorem ex1_theorem : ex1 ⊢ ex1_solution :=
-- begin
--     -- dunfold ex1 ex1_solution,
--     have c₁ : ex1 ⊢ Black sister.anne,
--         dunfold ex1,

    
-- end


end propositional
