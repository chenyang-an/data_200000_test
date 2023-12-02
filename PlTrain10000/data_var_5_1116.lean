variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112077004443365590053031292364 : ((((p1 ∧ p5) ∨ (((True ∨ ((p3 ∨ False) ∨ ((p5 ∧ (p3 ∨ p1)) ∨ (p1 → p4)))) → (p1 ∨ p5)) ∨ (p2 → p5))) ∨ False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151452869028201057536156962962 : (((((p3 ∨ p4) ∧ (((p3 → ((p2 ∧ (p4 ∧ (p3 ∨ False))) ∧ p5)) ∨ p2) ∨ True)) ∧ p5) ∨ (p1 ∧ p5)) → ((True ∨ p2) → (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h31 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
        case inr h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150306066872289790623817529086 : ((p4 → (((False ∧ p2) ∨ (p1 ∨ p4)) → ((False ∨ (False → (p4 → p1))) ∧ ((p1 → p4) → (p4 → p1))))) ∨ (True ∧ (p3 → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116029797341884691070513007153 : (((p4 ∧ (p5 → (p1 ∨ p4))) → ((p5 ∨ ((((p5 ∧ p3) → False) ∧ p2) ∨ (p1 → False))) ∨ ((False ∧ (False → True)) ∧ True))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57135925232104588934341082708 : ((((p1 → p4) ∧ False) ∨ ((((p2 → True) ∨ False) → p2) ∨ (p5 ∨ (p5 ∧ ((p4 ∧ (True ∨ p1)) ∨ (p5 ∧ ((p4 → True) ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172851424747974979943746063660 : ((False ∧ ((p4 ∨ (False → p1)) ∧ ((p1 → (p1 → p5)) ∨ (p5 ∧ (True ∨ True))))) ∨ (p2 ∨ ((p5 ∧ (p3 → p1)) ∨ ((True ∨ p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218622070370711422612398183290 : (((p5 → p5) → (p1 → p5)) → (((((p4 ∨ (((p5 ∧ (((True → True) → p5) ∨ p1)) ∨ p5) → True)) ∨ p2) → p1) ∨ (True → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340934231480234149529666098907 : (p2 → (((p4 ∨ (p5 → (p3 ∨ p4))) ∧ ((True → ((p4 → p4) ∨ (p4 → (p2 ∨ p1)))) ∧ ((True ∨ False) → ((True ∧ p4) ∧ p4)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672080209825350509742750323419 : ((((((False → ((p5 ∨ (p4 ∧ p3)) ∨ p2)) ∧ (((p4 ∧ p3) ∨ ((p4 → False) ∨ True)) ∧ (True → True))) ∨ p4) → (p2 ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638076323097159151160639171495 : (((((p4 ∧ (p3 → ((p2 → p3) ∨ (p3 ∨ p3)))) ∨ (True ∧ ((((p4 → ((p3 → p1) ∨ True)) ∨ p3) ∨ (False → p4)) → p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122805356853293556189194511872 : (((((p3 → p4) ∧ ((p1 ∧ True) → (p1 ∧ (p2 ∧ (p1 ∧ (((p5 → p1) ∧ p3) ∧ True)))))) ∧ p4) ∧ (p3 ∨ (True ∨ p1))) → (p1 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h17 := h8 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h21 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h22 := h8 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45478386229349382809842441645 : (((False ∨ ((((p3 → (((True → (False ∨ (p2 → True))) ∨ p3) ∨ p5)) → p4) ∧ (True ∨ p4)) → ((p1 ∨ p2) → (p3 ∧ p5)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313318891540777778235908396152 : (p3 ∨ ((p2 ∨ (p2 → (p3 ∧ (p4 ∨ (((((p1 ∧ p4) → (p2 ∧ p5)) → p2) ∧ ((p4 → ((p1 ∨ True) ∧ p1)) → p3)) ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78032454057585782739350363558 : (((p5 ∨ ((p1 ∧ (((False → (((p1 → False) ∨ (p5 → (False ∨ p2))) → True)) ∧ ((True ∧ False) ∨ p5)) → p1)) ∨ (True ∨ False))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((p1 ∧ (((False → (((p1 → False) ∨ (p5 → (False ∨ p2))) → True)) ∧ ((True ∧ False) ∨ p5)) → p1)) ∨ (True ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52662615848241636881429176145 : (((p4 ∧ ((((True ∧ (p1 ∨ p3)) ∧ p3) ∨ p2) ∧ (p3 ∨ (False → True)))) ∨ (((True → p5) ∨ True) ∨ (True ∨ (p5 ∧ (p3 ∧ True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158481099142082760798672790467 : (((True ∧ p5) → (((((((p4 ∨ p2) ∨ p4) ∨ p1) → p1) ∧ ((p4 → p4) → p1)) ∧ p3) ∧ p1)) ∨ ((False → p4) → (p5 → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621412036843553677716238903988 : ((((True ∧ (True → (p4 ∧ ((p1 ∨ ((False ∨ p3) ∨ p1)) ∨ ((False ∨ p1) ∨ ((p4 ∨ ((p1 ∨ (False ∨ p3)) ∧ p3)) → p1)))))) ∨ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788567697700427155597783517842 : (((p5 ∨ (((((p5 ∧ p2) ∨ (((((True ∧ ((p5 → True) ∨ p4)) → (False → p2)) ∨ p4) → p3) ∧ p3)) ∨ (p1 ∧ p2)) ∧ p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63953087532054366640882453590 : ((False ∨ ((False ∨ ((False ∧ p5) ∧ (p2 → (((True ∧ (p3 ∨ p4)) ∧ ((p5 → p3) ∨ (p1 → ((p4 ∧ p1) → p1)))) ∨ p4)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50371392403021965533975292632 : (((((p4 ∨ p5) ∨ p3) → (False ∨ ((((p3 ∨ p1) ∧ p4) → p5) ∧ ((False ∨ (True ∨ True)) ∨ p2)))) ∨ ((p5 ∨ p2) ∧ (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132178391042165288260789132426 : ((True ∧ (p2 ∨ (p3 ∨ ((((p3 → (p2 ∧ p4)) ∧ (p5 ∧ p3)) ∨ ((p3 ∨ (p2 ∧ True)) ∨ True)) ∨ (True → p3))))) ∧ (p3 → (False → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264223280923920276813434131471 : (True ∧ (((p5 → (False ∧ (p4 → p2))) ∨ True) ∧ (((p2 ∨ (p3 ∨ False)) ∨ (((p3 ∨ True) ∧ (p4 ∨ p5)) ∨ True)) ∨ (False → (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41590314664808754689087534900 : ((((False ∨ ((False ∨ ((False → p4) → p5)) ∨ p4)) ∧ ((p1 ∧ ((p3 → (False → (p5 ∨ (p1 → p5)))) ∨ (True ∨ p4))) → p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60219262631165764018582482381 : (((True → p1) → (((p4 → p3) → p5) → (p1 ∧ (p3 → ((p1 → (p2 ∨ p2)) → ((p4 ∨ (False ∧ (p3 ∧ (p3 → False)))) ∨ True)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65645109390739094776015040480 : ((p4 ∨ (((p1 ∨ (p2 ∧ p1)) ∨ (((p5 → (p5 ∨ False)) → (p1 ∧ p4)) → (p4 ∧ ((p2 ∨ ((False ∧ p2) → True)) → p1)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313356947645958301777681825542 : (p3 ∨ ((p2 → (True ∧ (((p1 ∧ (((p1 → p4) → p3) ∨ (p5 ∨ ((p5 ∨ (p5 ∨ p1)) → p5)))) → p3) ∧ ((False ∨ False) ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310766850794193905187829158340 : (p2 ∨ (((p5 ∧ p4) ∧ False) ∨ ((False ∨ (((p5 ∧ p1) → (((p4 ∨ p5) → ((p2 ∧ p5) ∨ p3)) ∧ (p4 ∨ True))) → True)) ∨ (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618830971119610907859943701043 : (((((True ∨ (p3 ∨ p3)) ∧ ((True ∨ (p5 ∧ ((p3 ∨ p5) ∧ (True ∨ ((p2 ∧ p1) ∧ p5))))) → ((True ∧ (p2 ∧ p1)) → False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932219049941819729269087527459 : (((((p1 ∨ ((p5 → True) → p1)) ∧ (p4 ∨ p5)) ∧ ((((p1 ∧ (p2 ∨ p2)) ∨ p4) ∧ (p4 → (p3 → True))) ∧ ((False ∨ False) ∨ p5))) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- False on the left can always be used.
              apply False.elim h17
            case inr h18 =>
              -- False on the left can always be used.
              apply False.elim h18
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- False on the left can always be used.
              apply False.elim h22
            case inr h23 =>
              -- False on the left can always be used.
              apply False.elim h23
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h13
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h3.left
      let h32 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h39
            case inl h40 =>
              -- False on the left can always be used.
              apply False.elim h40
            case inr h41 =>
              -- False on the left can always be used.
              apply False.elim h41
          case inr h42 =>
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h44 =>
            -- Disjunctions on the left can always be decomposed.
            cases h44
            case inl h45 =>
              -- False on the left can always be used.
              apply False.elim h45
            case inr h46 =>
              -- False on the left can always be used.
              apply False.elim h46
          case inr h47 =>
            -- One of the premise coincides with the conclusion.
            exact h36
      case inr h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h49 =>
          -- Disjunctions on the left can always be decomposed.
          cases h49
          case inl h50 =>
            -- False on the left can always be used.
            apply False.elim h50
          case inr h51 =>
            -- False on the left can always be used.
            apply False.elim h51
        case inr h52 =>
          -- One of the premise coincides with the conclusion.
          exact h6
  case inr h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h3.left
      let h56 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h57 := h55.left
      let h58 := h55.right
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h59.left
        let h61 := h59.right
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h63 =>
            -- Disjunctions on the left can always be decomposed.
            cases h63
            case inl h64 =>
              -- False on the left can always be used.
              apply False.elim h64
            case inr h65 =>
              -- False on the left can always be used.
              apply False.elim h65
          case inr h66 =>
            -- One of the premise coincides with the conclusion.
            exact h60
        case inr h67 =>
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h68 =>
            -- Disjunctions on the left can always be decomposed.
            cases h68
            case inl h69 =>
              -- False on the left can always be used.
              apply False.elim h69
            case inr h70 =>
              -- False on the left can always be used.
              apply False.elim h70
          case inr h71 =>
            -- One of the premise coincides with the conclusion.
            exact h60
      case inr h72 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h73 =>
          -- Disjunctions on the left can always be decomposed.
          cases h73
          case inl h74 =>
            -- False on the left can always be used.
            apply False.elim h74
          case inr h75 =>
            -- False on the left can always be used.
            apply False.elim h75
        case inr h76 =>
          -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
          have h77 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h78
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h53, we can now drive its conclusion.
          let h79 := h53 h77
          -- One of the premise coincides with the conclusion.
          exact h79
    case inr h80 =>
      -- Conjunctions on the left can always be decomposed.
      let h81 := h3.left
      let h82 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h83 := h81.left
      let h84 := h81.right
      -- Disjunctions on the left can always be decomposed.
      cases h83
      case inl h85 =>
        -- Conjunctions on the left can always be decomposed.
        let h86 := h85.left
        let h87 := h85.right
        -- Disjunctions on the left can always be decomposed.
        cases h87
        case inl h88 =>
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h89 =>
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h90 =>
              -- False on the left can always be used.
              apply False.elim h90
            case inr h91 =>
              -- False on the left can always be used.
              apply False.elim h91
          case inr h92 =>
            -- One of the premise coincides with the conclusion.
            exact h86
        case inr h93 =>
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h94 =>
            -- Disjunctions on the left can always be decomposed.
            cases h94
            case inl h95 =>
              -- False on the left can always be used.
              apply False.elim h95
            case inr h96 =>
              -- False on the left can always be used.
              apply False.elim h96
          case inr h97 =>
            -- One of the premise coincides with the conclusion.
            exact h86
      case inr h98 =>
        -- Disjunctions on the left can always be decomposed.
        cases h82
        case inl h99 =>
          -- Disjunctions on the left can always be decomposed.
          cases h99
          case inl h100 =>
            -- False on the left can always be used.
            apply False.elim h100
          case inr h101 =>
            -- False on the left can always be used.
            apply False.elim h101
        case inr h102 =>
          -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
          have h103 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h104
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h53, we can now drive its conclusion.
          let h105 := h53 h103
          -- One of the premise coincides with the conclusion.
          exact h105
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793833840135209450091384693348 : (((True → (p2 → (p5 ∧ ((((p3 → p3) → ((p5 → p2) ∨ p5)) ∧ ((p5 ∨ p4) ∧ (((p1 → True) ∧ True) → (p2 ∨ True)))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313367634787859380208357803611 : (p3 ∨ ((p4 → ((p5 → (False ∧ p5)) ∨ (p4 → (False ∨ (((p3 ∧ (p5 → (p4 ∨ (p3 → False)))) ∧ ((False ∧ True) ∧ True)) ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260540411169400631365679203378 : ((p3 → p1) → (((p1 → ((False ∨ ((((p4 → True) → ((p4 ∧ p2) ∧ (p1 ∨ p4))) ∧ p1) → p5)) ∧ p3)) ∨ p5) ∨ (p3 → (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259156333216622348000668898164 : ((False → True) → (((True → (True ∧ p1)) ∨ p1) ∨ ((p2 ∨ (((((True → p5) → ((p5 ∧ p3) ∨ p4)) ∨ p5) ∧ p4) ∧ (p2 ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86377563465350341955176190104 : ((((False ∨ ((p5 ∧ p1) ∨ ((p4 ∧ False) ∧ True))) → True) → ((p4 ∨ (((((p5 → (p3 ∧ False)) ∧ p4) ∨ p3) → False) ∨ True)) → False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p5 ∧ p1) ∨ ((p4 ∧ False) ∧ True))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ (((((p5 → (p3 ∧ False)) ∧ p4) ∨ p3) → False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124785617958576979760172376428 : (((True → (p5 ∧ (p2 → True))) ∧ (p2 → (((True → (((p4 ∧ p4) ∨ p5) ∧ True)) ∧ ((p1 → p1) ∧ (p1 → p1))) → False))) → (p5 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313930473511292622674911197315 : (p3 ∨ ((((p2 ∨ (p2 ∨ (p2 ∧ ((False → p5) → (((p4 ∨ ((True → False) ∧ p4)) ∧ (p3 ∨ p3)) ∧ p1))))) ∧ p5) ∨ p4) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_565945577659498568037620672432 : (((True → ((((True → ((p2 ∨ p2) ∧ p2)) ∧ (p2 ∨ p5)) ∨ True) ∧ ((p4 → (((False ∨ False) ∧ ((p4 → p4) → p4)) ∨ p4)) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318643237808607243093542437701 : (p4 ∨ ((p2 ∨ (((p5 → (p2 ∧ p2)) → (True → p3)) → (p4 → ((p5 ∧ (False → p5)) → (False ∨ (p2 ∧ (p5 → False))))))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130185599412058923175505562893 : (((p4 ∨ (((False ∧ p4) ∨ (p2 ∨ (p1 ∧ p5))) ∨ (((p5 ∨ p5) ∨ p5) ∧ (True → (p3 → p1))))) ∨ (p3 → p3)) ∧ ((p1 ∨ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758922831371053162849227640784 : (((p2 ∧ ((((False ∧ ((((p3 ∧ ((False ∧ True) ∨ True)) ∨ p4) → p5) ∧ True)) → False) ∧ ((p5 ∧ p1) → (p1 ∧ (p3 ∨ p2)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620376346334053667874352515819 : (((((p3 ∨ p2) ∨ (p3 ∨ (p5 ∨ (((p3 ∨ p4) ∨ (((True ∨ p5) ∧ False) → (p5 → False))) → ((False ∧ p5) ∨ (p2 → p4)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83277238606472896683771005770 : (((((((p3 ∧ p5) ∧ (False ∧ (p1 ∧ (True ∨ True)))) → p1) ∨ (p3 → p1)) → (p5 ∧ p4)) ∧ ((p1 → p3) ∧ (p3 ∨ (p2 → p1)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((((p3 ∧ p5) ∧ (False ∧ (p1 ∧ (True ∨ True)))) → p1) ∨ (p3 → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h7
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : ((((p3 ∧ p5) ∧ (False ∧ (p1 ∧ (True ∨ True)))) → p1) ∨ (p3 → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h21.left
      let h25 := h21.right
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h18
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42697879239698389728082343941 : (((p5 ∨ (((((((p3 ∨ p3) ∨ p1) → (p3 → (p1 ∨ (False ∨ True)))) ∨ True) → (True → False)) ∧ p4) → (False ∧ (p3 → False)))) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∨ p3) ∨ p1) → (p3 → (p1 ∨ (False ∨ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : ((((p3 ∨ p3) ∨ p1) → (p3 → (p1 ∨ (False ∨ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208585997812375823230306466830 : (((p1 → p1) → (p5 ∧ (p4 ∧ False))) → (p5 → (p2 ∨ (False ∧ ((((p3 ∨ (p3 ∨ (p4 ∨ True))) ∨ p5) → p4) → (p4 ∨ (p1 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651017270258224511492436077247 : (((((p2 ∧ ((p2 ∧ (False ∨ p5)) ∨ p1)) → (p4 ∧ (p3 ∨ (((p3 ∨ (True ∨ p1)) ∧ ((p4 → p2) → p4)) ∨ p4)))) ∧ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130156408143939703175448967433 : ((((False ∧ p4) ∨ ((((p3 ∧ True) → (p5 ∨ p2)) ∨ (p4 → (p4 ∧ (True ∧ p5)))) ∧ (p1 ∧ p1))) ∨ (True ∧ True)) ∧ ((p1 → True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203659500309715450333535833972 : ((p3 ∨ ((False ∧ p2) → (p3 → p1))) ∧ ((p4 ∨ ((((p3 ∨ p1) ∨ (((p4 → True) ∧ (p3 ∧ True)) ∧ p3)) ∨ p2) ∨ False)) ∨ (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346619693013008356781570350270 : (p3 → (((((p1 → True) ∧ False) ∧ p5) ∨ ((((p2 → p2) ∧ ((p2 ∧ (p3 ∧ p3)) ∧ p4)) ∨ p2) ∧ (True ∧ p3))) ∨ (p1 ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_341309242322079329928611953190 : (p2 → ((((p3 → ((False ∧ p4) ∨ (p1 → p3))) → (((False ∨ True) ∨ p5) → p1)) ∧ (False ∨ (((p3 → p3) → p4) ∨ (p4 ∧ p5)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
      have h8 : (p3 → ((False ∧ p4) ∨ (p1 → p3))) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h8
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : ((False ∨ True) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (p3 → ((False ∧ p4) ∨ (p1 → p3))) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h17
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((False ∨ True) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300353459907633321360853277778 : (False ∨ ((((p1 → (True ∨ ((((p4 → True) → (((p3 → (True ∨ p1)) → p3) → p3)) ∨ p3) ∨ p4))) → p2) ∧ p2) ∨ ((p1 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165043903986785990661934621749 : ((((p4 ∧ p5) ∨ (p3 ∨ (((p1 ∧ (p3 ∨ (True ∨ p4))) ∨ p2) ∨ (True ∧ p1)))) → p5) ∨ (False → ((p5 ∧ p3) ∧ ((p5 → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262147604962483223866227867690 : (True ∧ (((((((((p3 ∧ p4) → p3) → p4) ∨ True) ∧ (p5 ∨ p4)) ∨ ((((p1 ∧ True) ∨ p3) ∨ p4) ∨ p4)) ∧ (p2 ∧ p1)) ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216141506598645568155230114391 : ((True → (p5 → (p5 ∧ p3))) ∨ ((p1 ∧ (False ∧ (p3 ∨ (False ∨ (((((p5 → p5) ∧ p1) → p5) ∨ p3) ∧ p2))))) ∨ (p5 → (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173349567278342194100618977104 : ((p3 → (((False ∨ p4) → (((p5 → p1) ∨ (p2 → (p2 ∧ p1))) → False)) ∨ p3)) ∨ (((True ∧ (p5 → p4)) → (True → p4)) ∧ (True → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600105568702109270077942959112 : (((((p4 ∨ p1) → ((p2 ∨ (((False ∨ (True → (p5 → ((((True ∧ p2) ∨ True) ∧ p1) → (p1 ∨ p5))))) → p4) ∨ p1)) ∨ p3)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51819412774444213579561564473 : (((p1 → ((((p3 → (p2 ∧ p2)) ∨ (p5 → (False → (p4 ∨ p1)))) → p3) ∨ p1)) ∧ ((p1 ∨ (False → (True → (p3 ∨ True)))) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183381297088071883407980262400 : ((False ∨ (((p3 ∨ (p5 → ((p3 ∧ p4) ∧ p2))) ∧ p2) ∨ True)) ∧ ((((False → p3) ∧ p5) ∨ ((p2 ∨ True) ∨ p1)) → ((p5 ∧ True) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216777060579349094193068102669 : (((True ∧ (p3 ∨ p5)) ∧ p2) → ((p5 → (False → True)) ∧ (p4 ∨ ((True → ((False → p1) ∨ p1)) ∧ (p1 → ((False ∧ (p4 ∧ p1)) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56696334823981500509329765878 : ((((p1 ∧ True) ∨ p3) ∧ (((p1 ∨ p3) ∧ (p4 ∧ ((False → ((p1 → True) ∨ (p4 ∧ (p2 → True)))) → p2))) → ((p4 ∧ p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149935147607181313545010184495 : ((p3 ∨ ((p3 ∧ p2) ∧ ((((p3 ∧ p1) ∨ ((False → True) ∨ (False → (p4 ∧ p5)))) ∧ (p4 ∧ p1)) → p5))) ∨ (True ∨ (False ∨ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617228874752082715431522403155 : ((((((p4 ∨ p4) → ((p1 ∨ p3) ∨ (p5 ∨ p3))) ∨ (True ∧ ((((p3 ∧ p2) → p2) → p5) ∧ ((p4 ∨ p5) → (False ∨ p2))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225690867076139487682308551819 : (((p3 → p1) ∧ True) ∨ ((p3 → (((p2 ∨ p4) → p1) ∧ p5)) → (((p4 ∧ p3) ∨ p5) → (((False ∨ (p3 → (p4 → p2))) ∧ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184100095013861144323104692486 : ((((p2 ∧ p3) ∧ ((True ∨ ((True → True) ∧ p5)) → True)) ∨ p1) ∨ (p3 ∨ (True ∧ ((False ∨ ((False → p2) ∨ (p3 ∨ p3))) ∨ (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352012199935697033163936546508 : (p4 → ((p5 ∧ (((p3 → (p3 → True)) ∧ p2) ∨ False)) ∨ (((((False → p1) → (((p2 → p5) → False) ∧ (p5 → True))) ∧ p1) ∧ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134660021398741361025029951377 : (((((((p5 ∧ p2) ∨ (p1 ∧ False)) ∨ (p3 ∧ False)) → p2) ∨ (p3 → ((p1 ∧ p3) → ((False ∨ False) ∨ False)))) → p4) ∨ (True ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244900557456967009047416677182 : ((p1 ∧ p2) ∨ (False ∨ (p2 → (((p3 ∧ (True ∨ p2)) ∧ ((p1 ∧ ((p3 ∧ ((p1 → False) → p5)) ∨ p3)) → False)) ∨ (False → (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158601604760873852033585820607 : ((False ∧ ((True → ((p1 ∨ (True ∧ (((p5 ∧ (True ∧ True)) → p3) ∧ p4))) → (p4 ∧ p3))) → p1)) ∨ (True ∨ ((True ∨ True) ∧ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245160701550558850346531333638 : ((p2 ∧ False) ∨ (((((((p5 → False) ∨ True) ∧ p2) → ((p4 ∨ (((True → p5) ∨ False) → p3)) ∧ p5)) → (p1 ∨ p3)) → (False ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54451875807628289399878830981 : ((((((p5 ∨ True) ∧ p3) ∨ (p1 → p3)) → False) ∨ ((True ∧ ((False → p1) → p5)) → (False → (((p3 ∧ True) ∨ p4) ∨ (p2 → p4))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443228890585806119063243932 : ((((p2 ∨ (((p5 ∧ p2) ∨ True) → ((True ∧ (p2 ∨ p5)) ∧ (False → True)))) → ((p4 ∧ (p4 → p1)) ∧ ((False ∨ False) → p2))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115623921091303541178669279213 : (((p5 → ((True → (p2 → False)) → p5)) ∧ (p4 ∨ ((((p2 → (((p5 ∨ p2) → p1) → p5)) ∨ p3) ∧ (p1 ∧ False)) ∨ p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226379207241510291879212623622 : (((True → p4) ∨ p2) ∨ ((((((p3 ∧ p3) → p5) ∨ p3) ∨ p2) ∧ ((p1 ∨ (p4 ∧ p4)) ∨ p3)) ∨ ((p5 → (p2 → (False → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75745883251353935892013637575 : (((((((p4 ∨ (True ∧ p1)) → (((p5 → ((p1 → p2) → p4)) → p2) → p4)) ∧ p2) ∧ ((p5 ∨ p1) ∨ (p1 ∨ p3))) ∨ True) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∨ (True ∧ p1)) → (((p5 → ((p1 → p2) → p4)) → p2) → p4)) ∧ p2) ∧ ((p5 ∨ p1) ∨ (p1 ∨ p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136036131522188734810530282089 : (((True ∧ (p1 → (p1 ∧ ((False → (p3 ∧ p1)) ∨ p2)))) → ((((False ∨ (p3 ∧ True)) → p1) ∧ (p4 ∧ p5)) ∨ p5)) ∨ ((p3 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156887189814211871641114492857 : (((((True → (((p3 → p5) ∧ (False ∨ (p5 ∧ False))) ∨ (p4 ∨ p2))) ∨ (False ∨ False)) ∨ p5) ∨ True) ∨ (((p3 ∨ (p3 → p2)) ∨ p1) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227290938728238214396873986519 : (((p1 → p5) → p3) ∨ (((((p2 ∨ (p4 ∨ p1)) ∨ True) ∨ (p3 ∨ (p3 ∨ (p4 ∨ (p2 ∧ p3))))) → p3) → (((p3 ∨ True) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765532391827248480989830687012 : (((p4 ∧ ((p5 ∨ ((p3 → False) → (p5 ∧ ((False → p5) → ((False ∨ p4) ∨ (False ∨ False)))))) ∨ ((False ∧ (p5 → (p5 ∨ p3))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177945360137203379826310543256 : ((((p1 ∨ (True ∧ p4)) ∨ (p2 → ((p4 ∨ (p4 ∨ p4)) → p1))) ∨ p4) ∨ (((p1 ∧ p2) ∨ False) → ((p5 ∧ (p1 ∨ (p2 → p5))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172966912214683180780782162542 : ((p4 ∧ (((p5 ∨ ((p1 → (p1 ∧ p4)) ∧ p1)) ∧ p4) ∨ ((False → p5) ∨ p1))) ∨ ((True → ((p2 ∨ (p4 → (False ∧ True))) ∧ p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634434618954851335504941806343 : ((((((p1 ∨ (p4 → (False ∨ (((True → p4) → (p3 ∨ (p1 ∨ p3))) ∨ ((p4 → p2) → p1))))) → p4) ∧ (p3 → (p5 ∧ p2))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102598236566732074632628266984 : ((((((((p4 ∨ False) ∨ ((p2 → (p1 → (False → p3))) ∨ p1)) → False) ∧ (p3 ∨ (False ∧ (p1 ∧ p5)))) ∧ p2) ∧ p5) ∨ True) ∧ (p3 ∨ True)) := by
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
theorem thm_5_vars_115845325517861886656987792977 : (((True ∨ ((False ∧ True) → p3)) ∧ (p1 → (((((True ∨ p2) ∨ (((p4 ∨ True) → p2) ∨ p5)) ∨ p2) ∧ (p2 ∧ p2)) → p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601094727796946049615914129304 : ((((p1 ∧ (p3 ∧ ((((p2 ∨ p4) ∨ ((True ∧ ((p2 ∧ p3) ∨ (p3 → p3))) → p1)) ∨ p3) ∨ ((p1 → p2) ∨ (False ∧ p2))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351917219830792419642183468424 : (p4 → ((p3 ∧ (((p3 ∧ ((p5 ∧ p4) ∧ p2)) ∨ True) ∧ p1)) ∨ (p3 → (p4 ∧ (((p1 ∧ (p4 ∧ p5)) ∨ False) → (p3 ∨ (p3 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40136814804144675505909591109 : (((((((p3 → ((p2 ∧ False) → ((p5 ∧ p5) ∨ True))) → ((p3 ∨ p5) ∨ p2)) → p4) ∨ (((p5 ∨ p3) ∨ p4) ∧ p5)) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57364427260993485029176649107 : (((p4 ∧ (p5 ∧ p3)) ∨ (((((p3 → ((p4 ∨ p4) → (p3 → p4))) ∧ (p1 → (True ∧ p3))) ∧ (p5 ∨ p1)) ∧ True) ∧ (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233304187178160100531915094737 : ((True ∨ (p4 ∨ True)) → ((True → (p4 → ((p5 ∨ ((p2 → ((False ∨ ((p1 ∨ p4) → (p2 ∧ p1))) ∧ p3)) ∧ (False ∧ True))) ∨ p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627719278728462268644962490356 : ((((((p4 ∧ (p4 ∧ ((p2 ∨ (p5 ∧ ((p5 → False) ∨ True))) ∨ (p3 ∧ ((p3 → p1) ∧ p2))))) → ((p1 → True) ∧ True)) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1546115452092135204182605804 : ((p2 ∧ (p5 ∨ (((True → False) ∨ p3) ∨ (True → ((False ∨ (p5 ∧ p4)) ∨ ((p1 ∧ ((p3 → False) ∨ p1)) → False)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115990889976764989289083224729 : (((((False ∨ p1) ∨ True) → False) → ((p5 ∨ (p5 ∨ (p1 ∧ p3))) ∧ (p2 ∨ ((True ∧ (p3 ∨ ((p1 → p3) → False))) ∨ True)))) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38874865757274531054998244646 : ((((p4 → (p2 ∨ p3)) ∧ (((((p3 ∨ (((p2 → True) ∧ p4) → ((p5 → True) ∧ True))) → (True ∧ p1)) ∨ p4) → p3) → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309626134721583402050669916800 : (p2 ∨ (((((False ∨ p2) ∨ p3) → (p1 ∧ ((p5 ∧ (p1 ∨ p4)) ∨ (p2 → p1)))) ∨ (True ∨ ((p1 ∨ p3) → p5))) ∨ (False ∨ (True ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328609657070410182377550104766 : (True → (((((p2 ∧ p1) ∨ p2) → (((p1 ∧ (p4 → p2)) ∧ p5) ∧ p1)) → p3) ∨ ((p1 ∧ (((p1 ∧ p1) → True) → (p5 ∨ p3))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179366552333553172838586764921 : ((p2 ∨ ((p5 ∨ (p1 ∧ False)) ∧ (p2 ∧ (p3 ∧ ((p2 ∧ True) ∨ p1))))) ∨ (p1 ∨ ((True ∧ (p4 ∧ p5)) → ((p2 → p5) ∨ (p2 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928403111280386727154729854532 : ((((True ∨ (p1 ∧ ((True ∨ (p1 ∧ False)) → (p1 → p2)))) ∧ (p2 ∧ (p3 → (((((p1 ∨ True) → (p4 → p3)) ∧ False) → False) ∨ p1)))) → p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197293484835160118986021622164 : ((((p1 ∧ (True ∨ p3)) → (False ∧ p3)) → p5) ∨ (p3 ∨ (p4 ∨ (p2 ∨ (((((p5 → True) ∨ (False ∨ p3)) → p1) → True) ∨ (True → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134835892393097551249198743243 : (((p2 ∨ (False → (((False ∨ p2) → ((p5 → p3) → p5)) → (p2 ∨ (p4 ∨ (((p4 ∨ True) ∧ p2) ∧ p2)))))) → p5) ∨ (p1 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73418973750880186126152110598 : (((((p3 → False) → (((p4 ∨ ((p1 ∧ p4) → False)) ∧ (p4 ∧ (p3 ∧ p5))) ∨ ((p3 → p4) ∨ (p5 → p3)))) → (p4 ∧ True)) ∨ False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p3 → False) → (((p4 ∨ ((p1 ∧ p4) → False)) ∧ (p4 ∧ (p3 ∧ p5))) ∨ ((p3 → p4) ∨ (p5 → p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h3
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160525979906598728719695888837 : ((((((False → True) → ((p4 ∨ True) ∧ p1)) ∨ (p3 → p4)) → p3) ∨ ((p3 ∨ p2) → (False → p5))) → (p5 ∨ ((False ∧ False) → (True ∨ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166279438407791368492547772407 : ((p4 ∧ (((p3 → ((p2 → (((p3 ∨ p1) ∧ True) → (p1 ∧ False))) → p5)) ∧ p2) ∨ p2)) ∨ ((p1 ∧ p2) ∨ ((p3 → (p1 → p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



