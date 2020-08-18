import tactic

-- Exercise 1

 -- 3 sisters Anne, Mary and Claudia went to a party with dresses of different colors.
 -- One dressed in blue, another in white and another black. 
 -- When they arrived at the party, the host asked them who was who,
 -- and they answered. (1) The blue one said: "Anne is in white", 
 -- (2) the white one said "I am Mary", (3) the black one said 
 -- "Claudia is in white". The host was able to identify how each was dressed
 -- considering that: Anne always tells the truth, Mary sometimes tells the
 -- truth, Claudia never tells the truth.

 -- constants
 inductive sister
 | anne
 | mary
 | claudia

 structure ex1 :=
    (blue : sister → Prop)
    (white : sister → Prop)
    (black : sister → Prop)
    -- Anne always tells the truth (1)
    (h₁ : blue sister.anne → white sister.anne)
    -- Anne always tells the truth (2)
    (h₂ : white sister.anne → white sister.mary)
     -- Anne always tells the truth (3) 
    (h₃ : black sister.anne → white sister.claudia)
    -- Every color is wore (uniquely) by a sister
    (hblue  : ∃! s, blue s)
    (hwhite : ∃! s, white s)
    (hblack : ∃! s, black s)
    -- No sister wears 2 colors
    (single_color₁ : ∀ s, blue s → ¬ white s ∧ ¬ black s)
    (single_color₂ : ∀ s, white s → ¬ blue s ∧ ¬ black s)
    (single_color₃ : ∀ s, black s → ¬ white s ∧ ¬ blue s)

 -- Here is the solution the host found:
 -- (it is actually so easy to prove it, lean does it by itself.
 -- Actually it is not so easy for a puny human 
 -- to prove it using lean without any thinking,
 -- so hooray for ATPs)
 --   theorem ex1_solution {e : ex1} : e.black sister.anne ∧ e.blue sister.mary ∧ e.white sister.claudia :=
 --   begin
 --      -- Destructs the ex1 structure, and for every color, make
 --      -- all possible permutations of hypothesis about sisters wearing
 --      -- that colour. This gives us 27 proof cases, since there are 3
 --      -- colours and 3 sisters.
 --      cases_type* ex1 exists_unique and sister;
 --      -- use this automatic propositional theorem prover to solve
 --      -- each of the 27 goals.
 --      safe,
 --      -- if it looks like we are cheating, that's because we are.
 
 --      -- You should honestly keep this theorem commented out,
 --      -- otherwise the linter is going to keep checking this proof,
 --      -- everytime you create a new line, and that basically involves
 --      -- redoing the whole proof again.
 --      -- It takes a while to type check this though. 
 --   end


-- Exercise 2

 /-! 
 Albert, Charles and Eduard are friends. One of them is an statistician,
 another is a geographer and the other is a mathematician. 
 Considering that each one has exactly one profession among the 3,
 determine the profession of all 3 given that **only** 
 a single one of the following claims are true:
 1. Albert is a geographer.
 2. Charles is not an statistician.
 3. Eduard is not a geographer. 
 -/

 inductive friend
 | charles
 | albert
 | edward

 local notation p `||` q := xor p q

 structure ex2 :=
    (geographer : friend → Prop)
    (statistician : friend → Prop)
    (mathematician : friend → Prop)
    (h₁ : (geographer friend.albert ||
     ¬ statistician friend.charles) ||
     ¬ geographer friend.edward
    )
    -- Every profession is held (uniquely) by a friend
    (hgeographer  : ∃! f, geographer f)
    (hstatistician  : ∃! f, statistician f)
    (hmathematician  : ∃! f, mathematician f)
    -- No friend has 2 professions
    (single_profession₁ : ∀ s, geographer s → ¬ statistician s ∧ ¬ mathematician s)
    (single_profession₂ : ∀ s, statistician s → ¬ geographer s ∧ ¬ mathematician s)
    (single_profession₃ : ∀ s, mathematician s → ¬ geographer s ∧ ¬ statistician s)

 
 -- as you can see it ain't that trivial for a puny human to prove
 -- these sorts of theorems
 -- (actually, in this case, safe wasn't able to solve it though):
 theorem ex2_solution {e : ex2} : e.statistician friend.albert ∧
                                  e.mathematician friend.charles ∧
                                  e.geographer friend.edward
                                  :=
 begin
    -- automatically destroys ex2.
    -- This comes at the cost of everything in 
    -- the proof context having weird, hard to read, names.
    cases_type* ex2 exists_unique xor or and;
    simp at *,

    -- suppose albert is a geographer, 
    -- we will show an absurdity
    exfalso,
    -- first we get that albert is that unique geographer that exists.
    have c₁ := e_hgeographer_h_right friend.albert e_h₁_left_left,
    -- then we have that it is false that edward is not a geographer,
    -- so by double negation elimination, edward is a geographer
    simp at e_h₁_right,
    -- then edward is that unique geographer that exists.
    have c₂ := e_hgeographer_h_right friend.edward e_h₁_right,
    -- we can then conclude that edward and albert are equal.
    rw ←c₂ at c₁,
    -- however, this is absurd.
    contradiction,

    -- suppose then that charles is not an statistician.
    -- This is the correct case, so we focus on this and split
    -- the goals:
    focus {
        repeat {constructor},
        -- first we have to prove that albert is an statistician,
        -- for that lets first talk abstractly about the stats guy.
        rename e_hstatistician_w the_stats_guy,
        -- lets make some hypothesis about who the stats guy is,
        cases the_stats_guy,
        -- suppose it is charles...
        -- well, that's is of course impossible,
        -- by our assumption.
        case friend.charles {contradiction},
        -- supposing that it is albert...
        -- then it is albert
        case friend.albert {assumption},
        -- supposing it were edward...
        -- oh, but alas, we already know that edward is a geographer.
        case friend.edward {
            -- get that edward is a geographer
            simp at e_h₁_right,
            -- but if he were the stats guy, he couldn't be a geographer
            have c₂ := e_single_profession₂ friend.edward e_hstatistician_h_left,
            cases c₂,
            contradiction,
        },

        -- next we have to prove that charles is a mathematician,
        -- so we talk about the maths guy
        rename e_hmathematician_w the_maths_guy,
        -- and just the same, we make some hypothesis about
        -- who that could be
        cases the_maths_guy,
    }

 end