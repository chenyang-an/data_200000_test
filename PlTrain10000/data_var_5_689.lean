variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111547307824011518775229962949 : ((((((p2 ∧ (p1 ∧ ((p1 ∨ p3) → (True ∨ p1)))) ∧ ((p5 ∨ p5) → (False → (p4 ∧ p1)))) ∨ (p3 ∨ p1)) ∧ p5) ∨ True) ∨ (True ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738890276136615031838688465921 : ((((p3 ∧ True) ∨ (p1 → (True ∧ ((p5 ∨ p4) ∨ (((True → (True ∨ p4)) → (p3 ∨ (((False → (p4 → True)) → False) → p3))) ∨ False))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (p4 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357507356147877999022901381509 : (p5 → (True ∧ ((False ∧ ((((p2 → p1) ∧ p3) → (p1 → (p4 → False))) → ((False ∧ p3) ∧ p2))) ∨ ((p4 → (p2 ∨ (p1 → p1))) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216012065480612677144346792877 : ((p5 ∨ ((p2 ∧ p1) ∧ False)) ∨ ((p4 ∨ (p2 → ((p5 → True) → ((p1 ∧ (((True ∨ p5) → p5) ∨ p3)) → ((p4 ∧ p5) → p5))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230978897515635987595909424124 : (((p4 ∧ p3) ∨ p2) → ((p5 ∧ (((p5 ∨ p4) ∧ p1) ∨ (p3 → (p4 ∨ ((p4 ∨ True) → (p2 ∨ p4)))))) ∨ ((p1 ∧ p3) → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112840595214267101780622317757 : ((((p1 → ((p4 ∨ True) ∨ p1)) → (((p2 ∧ (((p2 → p1) → False) ∨ (p4 ∨ p1))) ∧ p4) ∧ (p5 → (p5 ∧ p4)))) → p4) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p4 ∨ True) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45015058943475722928063371400 : ((((p5 ∧ False) ∨ (((True ∧ (p5 → (True → (p1 ∧ True)))) ∨ (((p3 → p2) ∧ (p5 ∨ True)) ∨ True)) ∨ (False ∨ (p3 ∨ True)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90924119576388416607048510123 : (((True → p1) ∧ ((((p4 ∨ (p1 → False)) ∨ (p2 → p5)) ∨ (p5 ∨ ((p2 ∧ (p2 ∨ (((p5 → p4) ∨ p3) ∧ p2))) ∨ p5))) ∧ p3)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h26 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h27 := h2 h26
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h31 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h33 := h2 h32
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h35 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h36 := h2 h35
            -- One of the premise coincides with the conclusion.
            exact h36
      case inr h37 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h39 := h2 h38
        -- One of the premise coincides with the conclusion.
        exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149834196324130471166041324250 : ((p1 ∨ (((p3 → (False ∧ ((p3 → p5) ∨ (p2 ∨ p2)))) ∨ True) → ((p2 → p3) ∧ (p5 → (p5 → p2))))) ∨ (True ∨ ((p5 → p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313057441994625399700558849325 : (p3 ∨ (((True ∧ (((p2 ∧ (((((p1 ∧ p4) ∨ p5) → False) ∨ p5) ∨ p4)) ∧ (((True ∧ p1) ∨ (p2 → p2)) ∨ p2)) → p4)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679796521477274627536817389172 : ((((((True ∨ p1) ∨ ((p2 ∧ ((p2 ∧ (p2 → False)) → p3)) ∧ ((p3 ∨ False) → (p5 ∧ p2)))) ∨ False) → ((p1 → False) ∧ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128997482533779597410220165392 : (((p3 → ((((p1 ∧ p1) ∨ ((True ∧ (p4 → p3)) → p5)) ∨ p2) ∨ ((p4 ∧ (p4 ∨ p3)) → (p5 ∨ p4)))) ∧ True) ∧ (p4 → (p3 ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42730802720887497686643755309 : (((True → ((((((False → ((p5 ∨ (p5 ∧ p2)) ∨ (p4 → p3))) ∧ p5) ∧ p3) → False) ∨ (p1 ∨ ((False ∨ p2) ∨ p1))) → p4)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179194687824675570095544568729 : ((p3 ∧ ((True ∨ p4) → (False ∨ ((True ∨ ((False ∧ p1) ∨ p5)) ∧ p4)))) ∨ (True ∧ (p5 → (True ∧ ((p5 ∧ ((p2 ∧ p1) ∧ False)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115029701303393539971651456738 : (((p1 → (p1 → ((p1 → (((p4 ∧ p1) ∧ p5) ∨ p1)) ∧ p5))) ∧ ((p5 → p4) ∧ ((p5 ∨ ((p3 → False) ∨ True)) ∧ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65466752565605882313539576825 : ((p3 ∨ (True ∧ (((p4 ∨ p4) → p2) → ((((p4 ∧ p2) ∨ (p5 → p4)) ∧ ((p3 → (p2 ∨ p3)) ∨ (False ∧ (p3 ∨ p1)))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227007169133010847336246744498 : (((p1 ∨ p4) → False) ∨ ((p3 ∨ (p5 ∨ ((False ∨ (((p3 → (False ∨ (((p3 ∧ True) → p1) ∨ (False ∧ p1)))) ∨ p5) → True)) → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198559685484470613862346702218 : ((p1 ∨ ((p1 → (p3 → (p3 ∧ p5))) ∨ p2)) ∨ (((p3 ∧ (p5 ∨ (p4 ∧ p5))) → (((((p4 → p1) ∧ True) ∨ p5) ∨ p5) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197895939211863072397386386296 : ((((p4 → False) → True) → ((p3 ∨ p2) ∧ p3)) ∨ ((((p2 ∨ (p4 ∨ (False → False))) ∨ ((p4 ∨ (p2 ∨ False)) → p4)) → (p3 → p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765481583553555260735107780911 : (((p4 ∧ ((True → (((True → ((True → False) → p2)) ∧ (((p3 ∨ p4) → (p2 → p4)) ∨ p1)) → p1)) → ((p3 ∨ p4) ∨ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718318079387104635002889712912 : ((((((p2 → p1) ∧ p5) → p1) ∨ (p1 → (((((((p2 ∨ False) → (p2 → False)) → p1) → p1) → (False ∨ False)) ∧ p2) ∧ (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148425629084002472520253708462 : (((((p4 ∧ p5) ∧ (p2 ∨ p3)) → ((p1 → p1) ∧ ((p5 ∧ True) → False))) → ((True → p3) → (p1 ∧ p4))) ∨ ((False ∨ True) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57126566190206992981391744344 : ((((True → False) ∧ p1) ∨ (False ∧ (p4 ∧ (p1 ∨ ((p5 ∨ (p2 → ((((p3 → p5) → (p1 ∨ p4)) ∨ (p1 ∧ p4)) ∨ p3))) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67752144304579583580136042458 : ((p2 → (((((p4 ∨ p4) ∧ p2) → ((p1 → p2) → ((True → (p4 → ((False ∨ p3) ∧ (p1 ∨ False)))) ∨ (p5 ∨ p5)))) ∨ p4) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165200373159602137656632157918 : ((((True ∧ ((((p3 ∨ p1) ∧ p3) ∨ False) ∨ ((p3 ∧ p5) ∨ p2))) ∨ p2) ∨ (True ∨ True)) ∨ ((p1 ∧ (((False ∧ True) ∨ True) ∧ p4)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302827884944343245389460647173 : (False ∨ (p5 ∨ ((((True → True) ∨ p5) ∨ False) ∧ ((((True ∧ p5) → False) ∨ True) → ((p5 ∨ ((p2 → (p4 → (p3 ∨ p3))) ∨ p4)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171878882917611716828077980487 : (((p5 ∧ ((True → ((p1 ∨ True) ∧ False)) ∨ (p2 ∧ ((False ∨ p1) ∨ p3)))) → False) ∨ (True ∨ (p1 → (((p2 ∧ (p3 → p3)) ∨ p2) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62197939186395178676299437396 : ((p3 ∧ (((p5 ∨ ((p3 → ((p2 ∧ (p5 ∨ p3)) ∨ p4)) ∧ ((p3 ∧ p1) ∨ p1))) ∧ ((p5 ∨ ((p4 ∧ p3) → p3)) ∧ True)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112235075597985708452213495578 : (((p2 ∨ ((p2 → p3) ∧ (False ∧ ((p1 ∨ p3) ∨ ((p4 ∨ p3) ∨ (p5 ∨ ((p1 ∨ ((p4 ∨ p4) ∧ True)) ∨ True))))))) ∨ True) ∨ (True ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259387547575497822649415874312 : ((False → p3) → (((True ∨ (p4 ∧ (((True → True) ∨ (p2 → p2)) → (p1 ∨ (p5 → (p3 ∨ p5)))))) ∧ (p2 ∧ True)) → (p3 ∨ (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184554355159371055866078051862 : ((((((p2 ∧ p3) → p5) ∨ p2) ∧ (p5 → p1)) → (p3 ∧ p2)) ∨ (((p3 ∧ (p1 → (p2 ∧ p5))) ∨ ((p5 ∨ False) ∨ True)) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777263539907229612356863285 : (((p2 ∨ p4) ∨ ((((p5 ∨ (((p5 ∧ p1) → (False → (p4 ∨ (True ∨ True)))) ∧ (p2 ∨ p2))) ∨ p3) ∧ (False → True)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781720689393635426735205969392 : (((p2 ∨ (p4 ∨ ((p1 → (((p5 ∧ ((True ∧ p2) ∨ (False ∧ True))) ∧ p1) → (p5 ∨ True))) → (((p4 → True) → p2) → (p3 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2487183538875739342122760209 : ((((p5 → p4) → ((False ∧ True) ∨ p2)) ∧ (p2 ∨ p4)) → (((True ∧ (False ∧ p1)) → True) ∧ ((p1 ∨ p1) ∨ (p5 → (True → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160356754890823274250964731766 : ((((((p5 ∧ ((True ∧ (True ∧ p3)) ∨ False)) ∧ p3) ∨ (True ∧ p4)) ∨ p1) ∧ (p1 → (p4 ∨ False))) → ((p2 → p3) ∨ (p4 ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594210488586462269046165821957 : (((((p3 ∧ ((True ∧ (False → (((p4 ∧ True) ∨ (True ∧ p2)) ∨ (p4 ∨ (p3 ∧ p3))))) ∨ p4)) → (p3 ∧ (p3 ∧ (True ∧ p4)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173053889264901614329933852974 : ((False ∨ ((((p3 ∨ True) → ((p1 ∨ p2) ∧ p4)) → (p3 → p5)) ∧ (p4 → p5))) ∨ ((p1 → p4) → (p1 → (((p5 → False) ∧ p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51589659555243951472928541217 : (((False → (p5 → ((True ∧ p2) ∧ (((True → p1) ∨ (False → p3)) ∨ ((p2 ∧ p1) → p1))))) → (((False ∨ (p1 ∧ p2)) ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170014911872075904894818202917 : ((((p1 ∧ ((p2 ∧ p4) ∧ ((p3 ∧ p1) ∨ p3))) ∨ p5) ∨ ((p2 → False) → True)) ∧ (((p5 ∨ ((True ∨ p3) ∨ True)) ∨ True) → (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231203145382652927172395430304 : (((p3 ∨ p1) ∨ p1) → ((p3 ∧ (False ∧ (p4 ∨ p4))) ∨ (((p2 ∨ p4) ∨ (False ∨ (True → (p2 ∧ (((p4 ∧ p1) ∧ True) → p1))))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45368836743994020248285134316 : (((p4 ∧ ((p3 ∧ p1) ∧ (((p2 ∧ False) ∨ (((p3 ∧ ((p1 ∨ p5) ∧ p4)) ∨ p3) ∨ p4)) ∧ ((p3 ∧ (p1 → p2)) ∧ p4)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221141457070520228696060796074 : (((True ∨ p4) ∨ True) ∧ ((p1 → (((p2 → (p3 ∧ False)) ∨ (((p2 ∧ ((False ∧ False) ∨ p4)) ∧ ((p3 ∨ p3) ∧ True)) ∨ p1)) ∨ p3)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798398977827171759236873012842 : (((p1 → ((p2 ∨ (((((p3 ∧ p1) → p4) ∧ False) ∧ (p1 ∧ p5)) ∧ True)) ∨ (p5 ∧ ((p5 → p4) ∨ (p3 ∨ (p2 ∧ (p5 → False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596527825229104511343334031648 : ((((((False → (p1 ∨ p2)) ∧ (p2 ∧ (p4 ∧ p5))) → (p3 → ((True ∧ (p3 ∧ ((p5 ∧ (p3 → (p1 ∧ p5))) ∧ p1))) ∧ True))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231581298453625324407312746868 : (((p5 → p5) ∨ p3) → ((p3 ∨ ((((p5 ∨ (((True → p5) ∧ p5) ∨ (p2 ∨ True))) ∧ (p2 → (p3 ∨ p3))) ∧ p3) → p1)) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157642863188961364969422163695 : (((p4 ∨ (False ∧ ((p4 ∧ (True ∧ (p2 ∨ ((p5 → p3) ∧ p5)))) ∧ p3))) ∧ (p5 → (p1 → p3))) ∨ ((p2 ∧ False) → (True ∨ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307327537222620353335408425401 : (p1 ∨ (p3 ∨ (((((p5 ∨ p4) → p4) ∨ True) ∨ (p4 ∨ p5)) → (((p4 ∧ (True → True)) ∨ (True → p4)) → (((p2 → p5) ∧ True) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h19 := h15 h18
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h22 := h15 h21
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h27 := h15 h26
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219868016376563794800252160294 : ((p3 → (True → (p2 ∧ True))) → ((((p1 → ((p4 ∨ (p1 ∧ False)) → (False ∨ p5))) ∨ ((False → False) → p5)) → (p1 → p2)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258334627242574859811234995104 : ((p5 ∨ False) → ((((p4 ∧ (False ∧ (False → p1))) → p1) → ((p3 → (((p5 ∨ p5) ∨ p3) → (p2 ∧ (p2 ∧ (False ∧ p1))))) ∨ True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148437899501393294388630316550 : (((p2 ∨ (((True → (False ∨ p5)) ∧ (True ∨ (p2 ∨ p5))) ∨ (False ∨ p5))) → ((p2 ∧ (p2 ∨ p3)) ∧ p4)) ∨ (True ∨ (False → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683308729906688662067241854533 : ((((p3 ∨ (((p5 ∧ False) → ((False ∨ ((p1 ∨ p2) → (p4 → True))) ∧ (True → p5))) → True)) ∧ ((p3 → (False ∨ False)) ∨ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148050012705961180496839948243 : (((p5 ∧ ((p3 → (p2 ∨ ((p4 → p2) ∧ (p4 → (False ∧ (p3 ∧ p3)))))) ∨ (p3 → p5))) ∨ (p3 → p3)) ∨ (True ∨ (p4 ∧ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232260267113354988865704230875 : (((p2 → False) → p1) → (((p2 → p1) → ((True ∧ p4) ∨ p4)) ∨ ((True ∨ (p2 ∨ (p3 ∧ (((p1 ∧ p4) ∨ p5) ∧ (True ∨ True))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171314154013067079027791268727 : (((((((p1 → ((p2 ∨ p2) ∧ False)) → True) → (False ∧ True)) ∧ True) ∨ True) ∧ True) ∨ (p5 ∧ (p3 ∧ (((True ∧ p1) ∨ (p4 ∧ p1)) ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300979581361730134929710168408 : (False ∨ ((True → (p5 → (((p4 ∨ (False → p5)) → False) ∨ (p1 → True)))) ∨ (((p4 ∧ p5) → p5) → ((p5 ∧ (True ∨ (p2 ∧ False))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107050930585682952612583760536 : (((((p4 ∧ p5) ∨ False) ∨ p4) → (False ∨ (p1 ∨ ((p2 → (p2 ∧ (p2 → ((False ∨ ((p4 → p3) → True)) ∧ p1)))) ∨ p4)))) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133642140672389335980377703550 : ((((((((p4 → p2) ∧ ((p4 ∧ ((True → False) ∧ p4)) → True)) ∧ (p1 ∧ True)) ∨ p5) ∨ p2) ∧ (False ∨ p3)) ∧ p5) ∨ ((False → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48791670464157402538286928951 : (((False ∧ (((False → False) ∧ ((p3 ∨ (p5 ∧ p3)) ∨ ((True ∨ ((p3 ∨ (p1 ∨ p5)) → False)) → p5))) ∧ True)) ∧ (p3 → (False → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117531386049174746722559396979 : ((p2 ∧ (((((p3 → p1) → (p1 ∨ (True ∧ True))) → (False → (p4 ∨ (False ∨ (True → (p2 → True)))))) → p1) ∧ (p4 ∨ False))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158087714521364001407460034453 : (((p2 ∨ (p2 → (p3 → (p2 ∧ False)))) → (((False ∨ p1) → (p2 ∨ (False → (p3 → p2)))) → p4)) ∨ (((False ∧ p1) ∧ p2) → (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201442786724142733753083886184 : (((((p2 ∧ p2) ∧ False) → p2) ∧ True) ∧ ((False ∨ (p1 ∧ ((((p3 → (False ∨ p4)) ∧ ((p1 → p4) → (p2 → False))) ∨ True) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265880363172621104682146323924 : (True ∧ (True → ((True → (p4 → ((p5 → (False → p2)) → (p4 ∧ (True → (((p3 ∧ (p2 ∧ (p1 ∨ (True ∧ p2)))) ∨ p4) ∨ p3)))))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103404846466799847431473112416 : (((p4 → ((p4 → (p2 ∨ (p3 ∨ ((p5 → False) → (p3 ∨ (True → p3)))))) ∨ ((p1 ∨ False) → ((True ∧ p2) ∧ p5)))) ∨ True) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207361253531787049209398090153 : ((((p2 ∨ p3) → (p1 ∨ p1)) ∨ p1) → (p5 ∨ ((p5 ∧ p1) → ((((p2 → (p1 ∨ (p2 ∨ (p3 ∧ (p1 → p3))))) ∧ p1) → p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174225070205262155571750352822 : ((((p3 ∨ (p5 → p3)) ∧ ((False ∨ p5) → (True ∧ (p1 ∨ p5)))) → (p1 → p5)) → (((p2 ∧ (False ∧ (p2 → p5))) ∧ (p3 ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687890060621237959900451566145 : ((((((((p2 ∨ (p5 ∧ (p5 → p4))) → p3) → p1) → p4) → (p2 ∧ (True ∨ p3))) ∧ (((p5 ∧ (p3 ∨ (p3 ∧ p2))) ∨ p1) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310242154928960662350457743212 : (p2 ∨ ((((False ∨ (p1 ∨ p2)) ∨ True) ∧ (((p3 → p1) ∨ True) → False)) → ((p4 ∧ (((p4 ∧ True) → p5) ∨ p2)) ∨ ((True ∨ False) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : ((p3 → p1) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : ((p3 → p1) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((p3 → p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63344174255051949720777388009 : ((p5 ∧ (False ∧ (((p1 ∨ True) → (((p1 ∧ (p4 ∧ True)) → p4) ∧ ((p3 ∨ p1) ∧ (p5 ∧ ((p2 ∨ p4) ∧ (p2 ∨ p5)))))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50131592810043728739104421765 : (((p4 ∨ ((p2 ∧ True) ∨ ((p3 ∧ (True ∧ (p3 → ((p2 ∨ p2) ∧ p2)))) → ((p2 → False) → False)))) ∧ (((p1 ∨ p3) → False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310065669306284579824350529973 : (p2 ∨ ((((p1 ∧ p2) ∨ p3) ∧ (((False ∧ (True → (False ∧ (p5 ∧ p1)))) ∨ p3) → p2)) → ((((p2 ∨ p1) ∧ False) ∨ (p5 ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318963018246797066597441884754 : (p4 ∨ ((p5 ∧ (((((False ∨ (((p2 → p5) ∧ p2) ∧ False)) → p1) ∨ p5) → ((True ∨ p4) ∨ (False → p3))) → p2)) → ((False ∨ p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((False ∨ (((p2 → p5) ∧ p2) ∧ False)) → p1) ∨ p5) → ((True ∨ p4) ∨ (False → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323235412831572308329512434796 : (p5 ∨ ((((False ∨ p5) ∨ p4) ∧ ((((p4 ∧ p1) ∨ (((True → (False ∧ p1)) ∨ p2) → p1)) → ((True ∨ p1) ∨ p3)) → p5)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57241191383665845956532508446 : ((((p2 ∧ p1) → p4) ∨ ((False → (False ∧ (False ∨ True))) → (p4 ∧ ((p4 ∨ ((p5 → p5) ∧ (True → (p2 ∧ True)))) → (p4 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314930924979572324420997118487 : (p3 ∨ (((p4 → False) → (p4 ∧ (p4 ∨ (p4 → (p4 → p2))))) ∨ ((p1 ∧ (((False ∧ (p1 → p1)) ∨ p3) → (p2 → True))) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60245600943098893569870697312 : (((False → True) → (((((p2 ∧ (p4 ∨ p1)) ∨ ((p4 ∨ (p2 ∨ p1)) ∨ p4)) → (p3 → p1)) → ((False ∨ p5) ∨ p5)) ∨ (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124758491376357355163485475825 : ((((p2 → p2) → (True → p2)) ∧ (p1 ∨ ((p2 ∨ ((((p5 → (p5 ∧ True)) ∨ p3) ∧ p1) ∧ p1)) ∨ ((p2 → p3) ∧ False)))) → (p2 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h19 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h20
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h21 := h2 h19
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h23 := h21 h22
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h25 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h27 := h2 h25
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h28 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h29 := h27 h28
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204797470455804956694832646982 : ((((p4 → (p4 ∧ p5)) ∧ True) → p1) ∨ (((((((False → p1) ∨ p4) ∨ False) ∧ p1) ∧ ((p1 ∨ p5) ∧ (p5 ∧ (p2 ∨ p1)))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192608032160086434063050963707 : (((((False → ((True ∧ False) → p2)) ∨ False) ∧ False) → True) → (p4 → (p3 ∨ (p2 ∨ ((p4 ∧ (p3 ∨ (p1 ∧ (p1 ∧ False)))) → (p1 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962338473217420155414929257180 : ((((p5 ∨ p5) ∧ ((p5 → False) ∧ ((p2 ∨ ((p5 ∨ False) → ((p3 ∨ p4) ∧ (p1 → (True ∧ (p2 → True)))))) ∧ (p2 → (True ∧ p1))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h22 := h16 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h24 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h25 := h16 h24
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346790849245124681846208933653 : (p3 → (((p1 ∧ p5) ∧ ((((((True ∨ True) → p3) ∧ False) ∨ ((p2 ∨ p4) → False)) ∧ p5) ∨ (p4 ∨ True))) ∨ ((p4 ∧ p2) → (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135058072127418960990654901133 : (((((((((p1 ∨ p5) → (p2 ∧ (p5 ∧ p4))) ∨ (p2 ∨ False)) → p4) → True) ∧ (p1 → p2)) → False) ∨ (p5 ∧ p2)) ∨ ((p3 ∨ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147045999137597514964609120579 : (((((False → (((p3 ∨ p3) ∨ p4) ∧ (True → (p2 ∨ p4)))) ∨ p1) → (p3 ∨ (p3 ∨ (True ∧ p5)))) ∧ False) ∨ ((p4 ∧ p2) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200315588705280544625782236766 : (((p4 ∧ p5) ∧ (True ∧ ((p5 ∨ p4) ∧ p5))) → (((((p2 ∨ p1) ∨ p1) → (False ∧ p4)) ∧ True) ∨ ((((p3 → False) → p1) ∨ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185549527620053025433998507738 : ((p4 ∨ ((((((p5 → False) ∧ p2) ∨ p5) ∨ p4) → p1) ∨ p4)) ∨ ((p1 ∨ (p1 → p4)) ∨ (False → ((True → ((False ∧ True) ∧ False)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62722216696153633495779751219 : ((p4 ∧ ((p3 → (((p5 → (True ∨ ((p4 ∨ (p2 ∨ p3)) ∧ (p1 → (p5 ∨ ((p1 ∨ p3) ∨ p4)))))) ∧ False) → (True ∧ p1))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64486046151905755871842773474 : ((p1 ∨ (((((p1 ∨ p5) ∨ (p4 ∧ (False → p4))) → (p3 → (True ∧ (p1 ∨ p5)))) ∧ (p2 ∨ False)) → (p1 ∧ (False → (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319169409565098071821854214664 : (p4 ∨ ((((p2 → False) → (((False ∧ (p3 ∨ True)) ∧ False) ∧ (p5 ∨ p1))) → (p4 → (p5 ∧ False))) ∨ ((True ∨ (True → (p1 → True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178109212141474778021450653585 : ((((False ∨ (p4 ∧ ((p4 ∨ p2) ∧ (False → False)))) ∨ (p3 ∨ p5)) → False) ∨ (((((p1 → (True ∧ p4)) ∧ (True ∧ True)) ∧ p2) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166766526988037729672863299492 : ((p5 → ((((True → p2) ∧ (((p5 ∨ p1) ∧ (False ∨ (p5 ∨ p2))) ∨ p1)) ∨ p1) ∨ p2)) ∨ (((((True → p5) ∧ p4) ∧ p3) → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111033955276127526405272072353 : ((((((p5 ∧ p1) ∨ ((p5 ∧ p5) → ((p4 → p5) → p5))) → ((p3 ∧ p5) ∧ p4)) ∧ ((p3 → (False ∧ p2)) ∨ p5)) ∧ True) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129140769526404079457486542888 : ((((False → ((p2 → (((((p5 ∧ True) ∨ True) → True) → (p3 ∨ p4)) ∨ p2)) ∨ (True ∨ (p3 → p4)))) → p1) ∨ True) ∧ ((p3 ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186808517155343309103758799792 : (((p5 ∧ ((p1 ∧ p2) → p4)) ∧ (p3 ∧ ((p4 ∨ p2) ∨ p2))) → (((p5 → False) → p4) ∧ (((p1 ∨ ((p2 ∨ True) → p5)) ∧ p3) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h18.left
  let h22 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h32 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h33
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h35 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  -- Conjunctions on the left can always be decomposed.
  let h36 := h1.left
  let h37 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h37.left
  let h41 := h37.right
  -- Disjunctions on the left can always be decomposed.
  cases h41
  case inl h42 =>
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h43 =>
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h44 =>
      -- One of the premise coincides with the conclusion.
      exact h40
  case inr h45 =>
    -- One of the premise coincides with the conclusion.
    exact h40
  -- Conjunctions on the left can always be decomposed.
  let h46 := h1.left
  let h47 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h48 := h46.left
  let h49 := h46.right
  -- Conjunctions on the left can always be decomposed.
  let h50 := h47.left
  let h51 := h47.right
  -- Disjunctions on the left can always be decomposed.
  cases h51
  case inl h52 =>
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- One of the premise coincides with the conclusion.
      exact h48
    case inr h54 =>
      -- One of the premise coincides with the conclusion.
      exact h48
  case inr h55 =>
    -- One of the premise coincides with the conclusion.
    exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38905270661138256752534686018 : ((((p5 ∧ (p1 → p3)) ∨ (((p1 → ((p1 ∧ (p4 → (p5 ∨ ((p1 → p5) ∧ p5)))) ∧ ((p1 ∨ p2) ∨ p3))) ∨ p5) ∨ p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716091022062432872025800156051 : ((((((False ∧ True) → p4) → p4) ∧ (((((p1 ∨ p4) → False) ∧ ((True ∨ ((p3 → (p5 ∨ p5)) ∨ p5)) ∨ p1)) ∨ (True ∧ p4)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61850634526768032933368650472 : ((p2 ∧ (((((p5 → p1) → False) ∨ (((((True ∧ (p5 → p3)) → p5) ∨ p5) → p4) ∨ p2)) ∨ (True ∧ (p4 ∧ (False ∨ False)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197659532914477241095921169404 : ((((p3 → p1) ∧ (False ∨ p1)) → (p5 ∧ p1)) ∨ ((p5 ∧ (p3 ∧ (((p3 → False) ∧ True) ∨ p1))) ∨ (p5 → (p5 ∨ ((p5 → False) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218879347596186494627221372839 : ((p2 ∧ (p1 → (p3 ∧ p1))) → ((p4 ∧ p5) → ((p1 ∧ ((((p2 → p1) ∨ True) ∨ False) → (False ∧ (p2 ∨ (p3 ∧ p2))))) ∨ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196905656084082424671726612743 : (((p5 → (p2 ∨ ((False ∧ False) → p3))) ∧ p5) ∨ (p4 → (((((p4 ∨ False) ∨ True) → (((p4 ∨ p3) ∧ p5) ∧ (False → p5))) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149150742564887124725108421458 : (((False ∨ p5) ∧ ((p1 → (p1 → ((p4 → p2) ∨ (False ∨ (p5 ∧ (p2 ∨ (p1 ∨ p2))))))) ∨ (p5 → p5))) ∨ (((False ∨ p1) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50362882133370637962259786874 : ((((p5 ∧ (p4 → p2)) ∧ ((p4 ∧ (p2 ∧ ((((True ∧ p2) → (p5 ∨ p4)) ∧ p4) ∧ False))) ∧ p5)) ∨ ((True ∨ (p5 ∧ p3)) ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



