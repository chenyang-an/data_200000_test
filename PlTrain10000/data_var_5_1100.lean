variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171515659460440813390219221321 : (((((p4 ∧ p1) ∨ (p5 ∧ ((p4 ∧ False) ∨ (p4 ∧ (p3 → True))))) ∧ True) ∨ False) ∨ ((p4 → (((p5 ∨ p4) → (p2 ∧ p4)) → p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41596916933008798104842057743 : (((((p3 ∨ (True ∧ (p2 ∧ (p5 ∨ p4)))) ∧ p3) ∨ (False → (((((True ∨ p3) ∨ p2) → p1) ∧ ((p5 → False) ∨ False)) ∨ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694508033766854114085052047588 : ((((True ∧ (p2 → ((p5 ∧ (p5 ∧ (p4 ∨ ((p3 ∨ p3) ∨ p4)))) ∨ p2))) ∨ ((True ∧ False) → (((p3 ∧ False) → (p1 ∧ False)) → False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109450235112689960420366819305 : ((p2 ∨ (((True ∨ p3) ∧ ((((p4 → (True ∧ p2)) → (p5 → False)) ∨ True) ∨ p5)) ∨ (True → ((True ∨ (p2 ∨ p4)) ∧ p4)))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135668848650927858945423762667 : (((p1 ∨ (((p4 ∧ (p2 ∧ (p1 ∧ (False ∧ p3)))) ∨ (p2 → p1)) → (p2 → p2))) → ((p4 ∨ True) → (p3 → p4))) ∨ (p5 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122138081680026562107249131462 : (((((False → (p1 → p2)) ∨ (((p5 → (False ∧ (False ∧ True))) ∨ (False → (p2 ∨ p2))) → (p1 → p3))) ∨ p1) ∧ (p3 ∧ True)) → (p2 ∨ True)) := by
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
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160262085908759218631055147124 : (((False ∨ (p5 ∧ ((((p2 ∨ p1) ∨ p4) ∧ True) ∨ (True ∨ (p4 ∧ (p3 → p5)))))) ∨ (False ∧ p1)) → (((True ∨ (p5 ∨ False)) → p1) → p1)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h13 : (True ∨ (p5 ∨ False)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h14 := h2 h13
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : (True ∨ (p5 ∨ False)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h21 : (True ∨ (p5 ∨ False)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h22 := h2 h21
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h26 : (True ∨ (p5 ∨ False)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_553982495425531593815143965369 : (((p2 ∨ (((p5 ∧ ((False ∧ False) ∧ ((p4 → p4) ∧ (p1 → p3)))) → p4) ∧ ((((p3 → p1) → p3) → p2) ∨ (True ∨ (True → p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45772543721048623668315471142 : (((False → (p5 ∨ ((p4 ∧ p2) → (False ∧ (((((p5 ∧ ((p2 ∧ (p4 ∧ p1)) → p3)) ∨ (False → p1)) ∧ p1) → p4) → p2))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151638445651051756772788336460 : ((((p1 ∨ ((((False ∧ False) ∨ (((False ∧ True) → p3) → p3)) ∧ False) → p5)) ∧ p3) ∧ (p5 ∧ (p1 ∧ p4))) → (((p5 ∨ True) → p3) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207711803943829219556669954929 : (((p1 ∧ ((p4 ∧ p4) ∧ p1)) → False) → ((((p1 ∧ (((False → (((False ∧ p2) ∧ True) ∧ p5)) → p2) → True)) → p5) ∨ (False → p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67512403629910388394599148018 : ((p1 → ((p4 ∨ (p4 ∨ ((p5 ∧ (p1 ∨ p2)) → p2))) → (((((((True → False) → p4) ∨ p1) ∧ p1) → p3) ∧ p5) → (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782541720750907982603465870913 : (((p3 ∨ ((p2 ∧ (((((p5 → ((p5 ∨ ((False → p1) → (False ∧ True))) ∨ p4)) ∨ p4) ∧ ((p3 ∨ p4) → p4)) → p4) ∧ False)) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69326435864324452521183029205 : ((p5 → (p5 ∧ (((p1 → p4) ∧ p3) → (((p2 → (((False → (True ∨ False)) ∧ p1) ∧ False)) ∨ p4) → (p2 → (p1 ∨ (p2 → p4))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69101399138126201392805270243 : ((p5 → (((((((p3 ∨ True) → ((((p2 → p2) → False) ∨ (p5 ∨ True)) ∨ p5)) ∨ p4) ∨ (p5 ∧ p2)) ∨ False) ∨ p4) ∧ (p5 ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51371952994257478998961747182 : ((((((((p3 ∨ p1) ∧ p5) ∨ ((p1 → p3) ∨ (p5 ∧ (p2 ∨ False)))) → p4) ∧ p3) ∨ p4) → (((p2 ∨ (False ∨ True)) ∧ p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340716860304647961670996523451 : (p2 → ((((p5 → p3) → ((((((False → (((p2 ∨ p4) ∨ (p3 ∧ p5)) ∨ (True ∧ p3))) → p2) → True) ∨ True) ∨ p1) → p1)) ∧ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24772591834543459148495373190 : ((((p1 → False) ∧ p1) ∨ (p2 ∨ ((p2 ∨ (p1 ∧ ((True → (False ∧ False)) ∧ (p4 ∨ p2)))) → (((p5 ∧ (p5 ∨ p2)) ∨ p4) → p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h15 := h11 h14
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h36 := h32 h35
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- One of the premise coincides with the conclusion.
        exact h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348739819925679283520458816382 : (p3 → (False ∨ ((p1 ∨ (False ∧ ((p1 ∨ (p5 ∧ (((p1 → False) ∧ p5) → (False ∧ (False ∧ p5))))) → (p1 → (p3 ∧ False))))) ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3914465548418509555263357929 : (False ∨ (((((p1 ∨ p3) → False) → p4) → ((((p4 ∧ (p4 → p2)) ∨ (p3 → False)) ∨ False) ∧ ((True ∧ p5) ∨ False))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120071850852824173750922193690 : ((((True ∨ ((True ∧ (p4 → p2)) → p1)) ∧ (((p4 ∧ (((p1 ∧ p5) → ((p5 ∧ p1) ∧ True)) → p5)) ∧ p4) ∨ False)) ∧ p2) → (p3 ∨ p5)) := by
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
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : ((p1 ∧ p5) → ((p5 ∧ p1) ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h18 := h11 h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : ((p1 ∧ p5) → ((p5 ∧ p1) ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h27.left
        let h31 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h30
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h32 := h25 h26
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245446898382157701332454912784 : ((p2 ∧ p4) ∨ (False ∨ ((p1 ∧ p1) ∨ (((((p1 → True) ∨ p2) ∨ (False → p2)) ∧ p2) ∨ (False → (((p1 → p2) → p3) ∧ (False → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66483396046741180970482127036 : ((True → (((((p4 ∧ (p3 ∨ p3)) ∨ ((False ∧ (p1 ∨ p1)) → p2)) ∧ ((False ∧ (False ∨ p2)) ∨ (False → p5))) ∨ (p1 → p3)) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257457928911073386290698411492 : ((p3 ∨ True) → (((p1 ∧ p5) ∧ p4) ∨ (p5 → (((p3 ∨ (p5 → p2)) → (p2 ∧ (p4 ∧ p3))) ∨ ((p5 → ((True ∧ p2) ∧ False)) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720238451977343774081016613 : (((p1 ∧ (p5 ∧ ((p2 → p3) ∧ p1))) ∧ ((((p5 ∨ p4) → p3) → (False ∧ (p4 ∧ p1))) ∨ ((False ∨ (p1 ∨ p5)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327825120402260135878034676405 : (True → ((((p5 ∨ (((False ∨ (p2 → p3)) → (p3 → (p2 ∧ (p1 ∧ p2)))) ∧ p5)) ∨ (False → (True → True))) ∨ (p3 ∧ p4)) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350023768658563261796883170764 : (p4 → ((((False ∨ ((p2 → p3) ∧ (((((p4 ∧ False) → (True ∧ ((False → p1) → p3))) → p3) ∨ p1) ∧ (p1 → True)))) → p1) → False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158671734461909105894826873031 : ((p2 ∧ (((p4 ∧ p2) ∧ ((p4 → p2) ∨ (((False → (p5 → (False ∨ True))) ∨ True) → p4))) ∨ p2)) ∨ ((p3 → False) → (False ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777280859814854941990284870526 : (((p1 ∨ (((False ∨ True) → ((((((p3 → p1) → p4) → p5) → (p1 ∨ p5)) ∧ True) ∧ (p2 ∨ (p3 ∨ p2)))) → (p2 → (p5 → p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324358498276559469919554210057 : (p5 ∨ ((((p3 → p4) → (p1 ∧ p4)) ∨ p2) ∨ ((p3 → (p2 → p3)) ∨ ((p1 ∨ ((p3 ∨ (p2 ∧ (p1 ∧ True))) ∨ p2)) ∨ (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781644458109302795560301552755 : (((p2 ∨ (p2 ∨ ((p4 ∨ ((((False ∨ p2) ∨ p3) → p4) ∧ p4)) ∨ (((p1 ∨ p4) → (p3 → (((p3 ∨ p2) ∧ p5) ∧ False))) ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765544115572963810018695185832 : (((p4 ∧ (((((p1 → (False → ((p3 → True) ∨ p4))) ∧ p1) ∧ (p4 → p2)) → (p5 → p3)) → (p3 ∧ (p4 ∨ (p1 → (False ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259918698759554071120101923768 : ((p1 → p5) → (((p3 → (p4 → ((p1 → ((((p5 → p3) ∨ p1) ∧ p2) → p5)) ∨ p4))) → (p3 ∧ ((p2 ∧ (p5 ∧ p1)) → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157328201072318226356965823221 : (((True ∨ ((p2 → True) ∧ (((p1 ∧ ((p2 ∧ p1) ∧ ((p5 ∨ p5) ∧ p4))) → p4) ∧ p5))) → p3) ∨ ((p3 → True) ∨ ((True ∧ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118635667507295446024055359604 : ((p4 ∨ ((p4 ∨ (False → False)) → ((p4 ∨ ((p5 ∨ True) → ((((p5 ∨ True) ∨ p4) ∨ (False ∧ True)) ∧ (True ∨ p2)))) → p3))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225285153159767445310716506149 : (((True ∨ p5) ∧ p5) ∨ ((((False ∧ (True ∨ True)) ∨ (p5 ∨ (p5 ∨ p4))) ∨ p1) → (p2 ∨ ((p4 ∨ True) ∨ ((p5 ∨ False) → (p5 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54465803475248071336479396502 : ((((p3 → (p5 ∧ (True → (p2 ∧ p1)))) → p3) ∨ (p5 ∨ (False → (p5 ∧ (((p2 ∧ p1) ∧ (False ∧ ((p2 → p4) ∨ p3))) → p2))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137745591056523407123376253631 : ((p2 ∨ ((((p2 ∨ p3) ∨ (True → p1)) ∧ ((p2 ∨ (p3 ∧ ((True → p2) → (p1 ∧ (p3 ∧ p2))))) ∨ p3)) ∧ True)) ∨ (p1 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38445528442327467066329193509 : ((((p3 ∨ ((p4 ∨ True) ∧ (p3 → ((p2 → (p1 ∧ p3)) ∧ (p2 → True))))) ∨ (((p1 → p5) → (p3 ∧ p4)) ∨ (p1 ∨ True))) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42651043239447658617339320567 : (((p4 ∨ ((((((False ∧ ((p4 ∧ True) ∨ True)) → p4) ∨ p2) → (((p3 ∧ p4) → (True ∧ False)) ∧ (True ∧ False))) ∨ p3) → p5)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59154669670927945735529251406 : (((False ∨ p1) ∨ (((((((((p3 → p3) → p5) → ((p3 ∧ False) → p2)) → p2) ∧ (p3 → p1)) ∧ p4) ∧ p2) ∨ p5) ∨ (True ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185600459756855590289059558866 : ((p5 ∨ (p1 ∨ (p1 ∧ ((((p2 ∧ p2) → True) → p5) ∧ p1)))) ∨ (((p2 ∧ True) ∨ (True ∧ (p3 ∨ ((False ∨ (p1 ∨ p4)) → p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113179610586320456332105494648 : (((((True → ((((False ∨ p3) ∧ p5) → False) → (p5 ∧ ((p5 → (p4 ∨ p3)) ∧ (False → p1))))) ∨ p5) ∧ p4) ∧ (True ∨ p5)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305489537616922672791117617132 : (p1 ∨ (((p2 → ((p2 ∧ (p4 ∨ p3)) ∨ (p3 → (False ∧ (p3 → True))))) ∧ p5) ∨ ((((p5 ∨ p5) ∨ True) ∨ (p2 ∧ p2)) ∨ (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147976085478491622794903449377 : (((((p1 ∧ ((((((False → True) → True) ∧ True) ∨ p2) → (p5 → True)) → False)) ∧ p5) ∧ p5) ∨ (False ∨ p3)) ∨ (((p3 ∧ p5) ∧ p5) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184087696017619447849461077844 : ((((p1 → (p4 → p4)) ∧ ((p2 ∨ p1) → (p4 ∨ p3))) ∨ p3) ∨ (True ∧ ((p4 ∧ ((p1 → p4) → False)) → ((False ∧ False) → (p2 ∧ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226925227209486353300657985213 : (((True ∨ p3) → p3) ∨ ((p5 ∧ (p5 ∨ ((p1 ∨ (p2 ∧ (p3 → (((p1 ∨ ((True ∨ p4) ∧ (True ∧ p3))) → True) ∨ False)))) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149598353994153450690859313506 : ((p3 ∧ ((p3 → ((p2 → ((p5 ∧ True) ∧ False)) → ((p1 → p4) → p1))) ∧ ((p4 ∨ (p2 ∧ False)) ∧ True))) ∨ (True ∨ (p5 ∧ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346913071781567806288961069953 : (p3 → ((((p2 ∨ (p3 ∨ p5)) ∨ p5) → ((p4 ∧ (((p1 → True) ∧ False) → True)) → (p2 ∨ False))) ∨ (((p1 ∧ (p3 ∧ p4)) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244855699160528445371005070783 : ((p1 ∧ p2) ∨ ((((True → ((p1 ∧ (True ∧ False)) ∧ ((((((p2 → p1) ∧ False) → p2) → p5) → p3) ∨ (p3 ∨ False)))) ∧ p1) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753884447072511746644721482904 : (((False ∧ (((p1 → (False → p5)) → (True → (False ∨ p5))) ∨ (p3 → (((p4 → True) ∧ (p3 ∨ p4)) ∧ (p5 → ((p1 → True) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636313915211669684740260085975 : (((((((((p4 ∧ (p5 ∨ p5)) → (False → p5)) ∧ ((p4 ∨ False) ∧ False)) → p5) → p1) → ((False → (p5 → p4)) ∨ (p5 ∧ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200579624807394285373135219017 : ((True ∧ ((((True → p5) ∧ p2) → p3) → True)) → (p2 ∨ ((p3 ∧ (p1 ∨ (((p5 → p5) ∨ p2) ∨ ((p2 → p3) ∧ False)))) → (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773412562969635556929383498118 : (((False ∨ (((((p3 → (((p5 ∨ p1) ∨ False) ∨ ((p2 ∨ p3) ∧ p2))) → (((p4 → p1) → p4) ∧ False)) ∧ (True ∧ p2)) ∧ True) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158162697782345061725642626750 : ((((p1 ∨ (p1 ∨ p5)) ∧ p1) → (p4 ∧ (p2 → ((((p1 → p3) → False) → p5) → (p4 → False))))) ∨ ((p4 ∧ (p4 ∨ (p5 ∨ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355880807314208563354987291817 : (p5 → ((p4 ∧ (True ∧ (((p3 ∨ (p5 → (p3 ∨ (p2 ∨ (p4 ∧ (p5 ∨ (True ∧ (p4 → p2)))))))) ∧ p1) ∨ p5))) ∨ (p3 → (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147423836897100604594707425465 : ((((p5 → (p3 → False)) ∧ (False ∧ (((p1 → False) ∧ (True ∧ p1)) ∨ (((p1 ∨ p2) ∧ p5) ∧ p1)))) ∨ True) ∨ ((False ∨ p3) → (True ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207342951377804378724169382007 : ((((True → True) ∨ (False ∧ True)) ∨ True) → (p3 → ((p4 ∨ (p3 ∧ (((p2 → ((True ∨ p2) ∨ p1)) ∧ ((p1 ∧ p4) ∧ p1)) → False))) ∨ p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137701619237716697633327883802 : ((p1 ∨ ((((p1 → (p2 ∨ p3)) ∨ True) ∧ ((False → (((p4 ∨ p5) → p3) ∨ True)) → p5)) ∨ (p2 ∨ (p2 ∨ p2)))) ∨ ((p3 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112896765738113518433760175728 : ((((p2 → p1) ∧ (((p4 → (((p5 → (p1 ∨ (True → True))) → True) ∧ (p5 ∨ (True ∨ False)))) → (p4 ∨ True)) → p2)) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938046553506695325219557778720 : ((((True → (p4 ∧ (p2 ∨ (p3 ∧ p2)))) ∧ ((p5 → ((p5 ∧ (False ∨ ((False ∨ True) → p4))) ∨ ((p3 ∧ p5) ∧ (p4 → p1)))) ∨ p5)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658482233109364057025005625762 : ((((p1 ∨ (p3 ∧ (((p3 ∨ (p1 ∧ ((((False → p5) ∨ (p4 → p1)) ∨ p3) ∨ p3))) → (False ∨ True)) → (p3 ∨ p1)))) ∨ (True → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60462401964684986301389826514 : (((p5 → p2) → (p3 ∨ ((p5 ∧ ((True → p4) → ((p2 ∨ ((p3 ∨ (p2 ∨ p3)) → p1)) ∨ p4))) ∨ (p3 ∨ (p4 → (p4 → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680335795064907471053399221162 : (((((((p2 → p4) → p1) ∨ (False ∨ (False → (p1 → (p2 → (True ∧ False)))))) ∨ (True ∨ (False → p5))) → (p2 → (p5 ∨ (p3 ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773741718828725728908895507936 : (((False ∨ (((((p4 ∨ (((p4 ∧ p3) → False) ∧ (((True → True) ∧ p1) ∨ (p3 → p4)))) ∧ p3) ∨ (True ∧ (p3 ∨ p5))) → True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41389305320258984480027481181 : (((((p2 → (((p4 → p1) ∧ p5) ∨ (p2 → p4))) ∨ ((True → False) ∧ p4)) ∧ ((True → p2) → (p5 ∨ (True → (p4 ∧ False))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218452695379401518029502503450 : (((p4 ∧ p3) → (p3 ∧ p4)) → ((((False ∨ True) → (p2 → False)) ∨ (True → True)) ∧ ((p4 → (p3 → p4)) → (((True → p2) → p3) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742231706771537194561426594468 : ((((p1 → False) ∨ (False ∨ ((((True ∧ (p2 ∧ (p1 ∧ p1))) ∧ True) ∨ (True ∨ False)) ∨ ((p1 ∨ p3) ∧ ((p3 ∧ p1) ∧ (p4 ∨ p3)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47321734362466467442317528745 : (((((p4 ∧ False) → p2) → (((((p2 ∧ p2) ∧ (((p5 → (p5 ∧ False)) → True) ∨ p1)) ∧ (False ∨ p2)) ∨ p2) ∧ p4)) ∨ (True ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320104222479665114491414378734 : (p4 ∨ (((p4 ∨ p3) → p3) → ((((True ∧ p2) → p4) ∧ ((False → ((p2 ∨ p2) ∨ p3)) ∨ ((p5 ∨ p1) ∨ p4))) ∨ (p1 → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113917707785928370173288374118 : ((((p3 ∨ ((False → p1) ∧ ((True ∨ True) ∧ (((False → p1) → True) ∧ (False → False))))) → (False ∨ False)) ∧ ((p5 ∨ p3) → p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136057685990798402088449722732 : (((((True ∧ (p1 ∧ (p1 ∨ p5))) ∨ p5) → p5) ∧ ((((p2 ∧ True) ∧ p5) ∨ (p4 ∧ ((False ∨ p3) ∨ p4))) ∨ False)) ∨ (True ∨ (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106837287028886022771731475130 : (((p3 ∨ (p3 → (p4 → (True → p1)))) → (((p4 ∧ ((p5 ∨ (p3 → ((p2 → p1) ∧ False))) ∨ p4)) ∨ p4) ∨ (False → p1))) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42182780728120646486728756423 : (((True ∧ ((p5 ∨ ((((p1 → False) ∨ ((p2 → (p3 → False)) ∧ (p5 → (p1 ∧ p2)))) ∨ (p3 ∧ p5)) ∨ False)) ∧ (p2 ∨ True))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181457791495011800310305855256 : ((p4 ∨ (((((p3 → (p1 → p1)) ∧ False) ∨ p2) ∧ (p5 ∨ p5)) ∧ p4)) → ((p5 → (p1 ∨ (p4 → (True → (p3 ∨ p5))))) ∨ (p1 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349050738306357301899234115521 : (p3 → (p5 ∨ ((True ∧ ((((p1 ∧ p4) ∨ True) → ((((p1 → p5) → p1) ∨ False) → p4)) ∨ p1)) ∨ (p2 ∨ ((p3 ∨ (True ∨ p5)) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234709495583160787863278903143 : ((p4 → (p1 ∨ p5)) → ((((p1 ∨ p1) → ((p1 → p4) ∨ p1)) ∨ (p4 → p4)) ∨ ((False ∨ (((True ∧ p1) ∨ (False → p1)) → False)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47426670980569729076580885809 : (((p1 ∧ (p4 ∨ ((((True ∨ p5) ∧ ((p4 → p1) → False)) ∧ ((False ∨ (p3 → (p4 → (p4 ∧ p3)))) → True)) ∧ True))) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49237355817254168163401238982 : ((((p2 ∧ True) → (p3 → (((p5 ∨ p4) ∨ p2) ∧ (p4 ∨ (((p5 ∧ False) ∨ p2) ∧ ((True ∧ p3) ∧ True)))))) ∨ (p4 → (True ∧ True))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170252881879077980152469452383 : ((((p2 ∧ True) → (p3 ∧ (p2 → p4))) → ((p4 ∨ ((True ∧ p3) ∨ True)) ∨ p2)) ∧ (((p5 → p3) → ((False ∨ False) → p1)) ∨ (p2 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232877817437727197442205804263 : ((p2 ∧ (p5 → False)) → (((((p5 ∨ ((p2 ∧ (p2 ∧ p3)) → p5)) ∧ ((p3 ∨ (p4 ∨ False)) ∨ p2)) → p5) ∨ (p4 ∧ p1)) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113338045284074105652087865849 : ((((False ∨ p4) → (((((((p5 ∧ False) ∧ False) ∧ (True ∧ (True ∧ p2))) → (p5 ∧ False)) → p2) → False) → p1)) ∧ (p2 ∨ False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138216460470708776594325124940 : ((p2 → ((False ∨ ((p3 ∨ p2) → ((True ∨ (((True ∧ p2) ∨ (p5 ∨ True)) ∧ (p3 ∨ (p1 → True)))) → p5))) ∨ p3)) ∨ ((p2 ∨ p2) → p2)) := by
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
theorem thm_5_vars_313271583293435937324333700626 : (p3 ∨ ((p1 ∧ ((True → (((p3 ∧ p2) ∨ True) → False)) ∧ ((p3 → True) ∧ ((p2 ∧ (False ∨ p4)) ∨ ((p3 → True) ∧ (p3 → p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314858511941933797815671925855 : (p3 ∨ (((((True ∧ (p3 → True)) ∨ (p5 → p1)) → (p2 → True)) → False) → (((p5 ∧ ((True ∧ (p4 → (p3 ∨ p3))) ∧ p3)) ∨ p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ (p3 → True)) ∨ (p5 → p1)) → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((True ∧ (p3 → True)) ∨ (p5 → p1)) → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60400729144063004484006152143 : (((p3 → p5) → (p5 ∨ (p1 ∨ (p2 → ((False ∨ ((p2 ∨ (False → p3)) ∨ ((True ∧ p5) ∨ p4))) → (p4 ∨ ((p2 → p3) ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301519466535916821756299153994 : (False ∨ (((p3 ∧ False) ∧ p5) ∨ (True → (((True ∧ (((p2 ∨ (True ∨ p3)) → (p1 ∨ True)) ∨ p5)) ∧ True) → (False ∨ ((p4 ∧ False) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137156963328367742274958221647 : ((False ∧ ((((p3 ∧ False) ∧ False) ∨ ((p1 ∨ ((p4 ∧ p2) → ((p5 ∨ ((p4 ∨ p4) → False)) → False))) → False)) ∨ p4)) ∨ ((p1 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44657464534118949213955274629 : ((((False ∧ (p4 → (p1 ∧ (True ∨ p2)))) ∨ (((p1 ∧ ((False ∧ (p2 ∨ p3)) → (p1 ∨ (p2 ∨ (True ∧ False))))) ∨ p5) ∨ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737339752283300047995373541407 : ((((p4 → p2) ∧ ((p3 ∧ (True ∨ (p4 ∨ (True → p2)))) ∨ ((p5 ∨ p3) → ((p4 → ((p4 → False) ∨ p2)) ∧ ((True → p4) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44361841034998319266989210936 : (((((p3 ∨ ((p5 ∧ (((True → p2) → p1) ∧ True)) ∧ (p4 ∨ True))) → p3) ∧ (False ∨ ((p4 → (p4 → (p1 ∨ False))) → True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321712908696047242668675077297 : (p4 ∨ (p5 → (((p5 → ((False ∧ ((((p3 ∨ p3) ∨ (p3 → False)) ∨ (True ∧ p4)) → p4)) ∧ True)) ∨ ((p3 → (p1 ∨ p3)) ∨ p2)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615094893900479583086734964096 : (((((((((((p2 ∨ (p5 → False)) → p1) → True) → (p1 ∨ False)) ∧ True) → p5) ∧ p5) ∧ (p2 ∧ (True → ((p3 → True) ∧ True)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_247361431988692360402205368729 : ((False ∨ p1) ∨ (((((p2 ∧ (p4 ∧ p3)) ∧ (p4 → p3)) ∧ (p2 ∨ True)) ∨ ((p1 → (False ∨ (p2 → p1))) ∨ p2)) ∧ ((p4 ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740840812114248476090206701080 : ((((p3 ∨ False) ∨ ((((((False ∧ (p3 ∧ p5)) ∧ False) ∧ p5) ∨ p2) ∨ p1) ∨ ((((False ∧ p1) ∨ (True ∧ p4)) ∨ (False → p4)) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786166391873217892272059137870 : (((p4 ∨ ((False ∧ (True → ((p1 ∧ (p2 ∨ ((False → False) ∧ p5))) ∨ (p4 → (((True ∨ p1) ∨ False) ∧ False))))) ∨ ((p5 ∧ p2) → p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620869102786207698237932761910 : (((((p1 ∨ p4) → ((((p2 ∨ p5) ∧ (p1 ∧ (((((p3 → False) ∨ p1) ∨ False) ∨ ((p3 ∧ True) ∨ p4)) ∧ p2))) ∧ p3) ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778749311931562791762831433083 : (((p1 ∨ (p4 ∨ (((False ∧ (p2 → p1)) ∧ False) ∨ (p1 ∧ (p5 → (((p4 ∨ ((p4 ∨ (True ∧ (False → True))) → False)) → False) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147591551919051567083067084998 : (((((True ∨ (p2 ∧ (p5 → ((p5 ∧ (p1 ∧ True)) ∧ (((p3 → p1) ∨ p5) → p2))))) ∨ p1) ∨ p2) → p4) ∨ ((p1 ∨ True) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190208169602537655192732561977 : (((True → ((((False → p5) ∧ False) → p3) ∨ False)) ∧ p2) ∨ (((p2 ∧ (False ∨ p1)) ∧ False) ∨ ((False → p2) ∨ ((p5 ∨ False) ∧ (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



