variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308592768434593719394883597046 : (p2 ∨ (((p5 ∧ (True ∨ p4)) ∨ (p1 → (((((((p5 ∧ (p3 ∧ (p5 ∨ p2))) ∨ p4) ∨ (p4 ∨ False)) ∨ p2) ∧ p1) ∧ False) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658049111538258885070311381633 : ((((p3 ∧ ((True ∧ (((((p4 ∧ True) ∨ p3) → (p5 → (p2 ∧ ((p3 → p2) ∨ p3)))) → p2) ∧ (p1 → False))) ∨ p5)) ∨ (False → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64242564088031840848212784762 : ((False ∨ (p1 ∨ (True ∧ ((p4 ∨ (p1 → (False ∧ (False ∨ ((p4 ∧ (False ∧ True)) → False))))) ∧ (((p2 ∨ True) → p2) ∧ (p2 ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183811303975723702860597848624 : ((((p2 → (p4 ∨ ((p4 ∧ p1) ∨ (p1 ∨ False)))) ∨ True) ∧ True) ∨ (((p1 ∧ (p4 ∨ (p1 → p4))) ∧ (p3 → p2)) ∧ (p5 → (p2 ∧ False)))) := by
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
theorem thm_5_vars_69040968398962809593350637926 : ((p5 → (((True ∨ (((p1 ∨ ((p1 ∧ p1) ∨ p2)) → p2) ∧ True)) ∧ ((((p5 ∧ (True → (False → True))) → False) → p2) → False)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548435090705520707270749231302 : (((False ∨ (((p4 ∨ p5) ∧ p1) ∨ ((p5 ∨ (False ∨ True)) ∨ ((((p3 ∨ p5) ∨ (p4 → (((p2 → p4) ∧ True) → p4))) ∧ False) ∨ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664922398014279277014528311891 : ((((p3 → (((p2 → p5) ∨ (((p1 → (((p4 ∧ p4) ∧ (p4 ∨ p5)) ∨ p2)) ∨ (p3 ∧ p5)) ∧ (p2 → p2))) → False)) → (p5 → p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325068472103887723560595153748 : (p5 ∨ ((p4 ∨ True) → ((((p4 ∧ p3) ∧ (True ∨ (p4 → (p4 → p1)))) ∨ ((p3 ∧ True) ∨ (((p3 ∧ p5) → (p2 ∨ p4)) → True))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188532682901598042887548760887 : (((p2 → ((True → p3) ∨ ((p4 ∧ p1) → True))) → True) ∧ ((False ∨ p3) → (((p3 → p1) ∨ p5) → ((p5 ∨ True) → ((True → p4) → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h15
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h21
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h27 := h5 h26
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152230397947418199728519860748 : (((True → (((p3 ∧ True) ∧ p2) ∧ False)) ∧ ((p2 ∧ ((False ∧ p3) ∨ ((False ∨ (p1 → p3)) ∨ False))) ∨ p1)) → (p3 ∧ (p4 ∧ (p2 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- We need to get the right conjuct of h15 based on <expert-advice>.
          let h16 := h15.right
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h34 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h35 := h22 h34
          -- We need to get the right conjuct of h35 based on <expert-advice>.
          let h36 := h35.right
          -- False on the left can always be used.
          apply False.elim h36
      case inr h37 =>
        -- False on the left can always be used.
        apply False.elim h37
  case inr h38 =>
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h39 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h40 := h22 h39
    -- We need to get the right conjuct of h40 based on <expert-advice>.
    let h41 := h40.right
    -- False on the left can always be used.
    apply False.elim h41
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h42 := h1.left
  let h43 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h43
  case inl h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h47.left
      let h49 := h47.right
      -- False on the left can always be used.
      apply False.elim h48
    case inr h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- One of the premise coincides with the conclusion.
          exact h45
      case inr h54 =>
        -- False on the left can always be used.
        apply False.elim h54
  case inr h55 =>
    -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
    have h56 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h42, we can now drive its conclusion.
    let h57 := h42 h56
    -- We need to get the left conjuct of h57 based on <expert-advice>.
    let h58 := h57.left
    -- We need to get the right conjuct of h58 based on <expert-advice>.
    let h59 := h58.right
    -- One of the premise coincides with the conclusion.
    exact h59
  -- Conjunctions on the left can always be decomposed.
  let h60 := h1.left
  let h61 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h61
  case inl h62 =>
    -- Conjunctions on the left can always be decomposed.
    let h63 := h62.left
    let h64 := h62.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h65 =>
      -- Conjunctions on the left can always be decomposed.
      let h66 := h65.left
      let h67 := h65.right
      -- False on the left can always be used.
      apply False.elim h66
    case inr h68 =>
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h69 =>
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h70 =>
          -- False on the left can always be used.
          apply False.elim h70
        case inr h71 =>
          -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
          have h72 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h60, we can now drive its conclusion.
          let h73 := h60 h72
          -- We need to get the right conjuct of h73 based on <expert-advice>.
          let h74 := h73.right
          -- False on the left can always be used.
          apply False.elim h74
      case inr h75 =>
        -- False on the left can always be used.
        apply False.elim h75
  case inr h76 =>
    -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
    have h77 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h60, we can now drive its conclusion.
    let h78 := h60 h77
    -- We need to get the right conjuct of h78 based on <expert-advice>.
    let h79 := h78.right
    -- False on the left can always be used.
    apply False.elim h79



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217867860438329446591511070577 : (((False → (p3 ∨ p1)) → p1) → ((p1 ∨ p4) ∧ (p1 ∨ ((p1 ∨ ((p3 ∨ (p1 ∧ False)) → False)) ∧ ((True ∧ p5) ∨ (True ∨ (True ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p3 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p3 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148240378581272139559808208329 : ((((((p1 → p1) ∨ (p3 → True)) → (p4 → p5)) ∧ (p2 ∨ (p3 ∧ (p5 ∨ p1)))) ∨ ((p4 ∨ p5) ∧ p1)) ∨ (True → ((p3 → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192953759224317875440179394715 : ((((p4 → p3) → (p4 → (False ∨ True))) ∨ (p2 → True)) → ((((True ∧ (p1 ∧ True)) ∨ ((p3 ∧ (p3 ∨ p2)) ∨ (p5 ∧ p1))) ∧ p3) → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66785632361704668445340424531 : ((True → (False ∨ (((False ∨ ((((p2 → True) ∧ (((p3 ∨ (p4 ∨ p3)) → p1) ∨ p3)) → p3) ∨ p3)) → p4) ∨ ((p2 ∨ True) ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135749360679004069071831018812 : ((((False ∧ False) ∧ (((p5 → (p1 → (False ∧ p3))) ∨ p1) → (p1 ∧ False))) ∨ (p1 ∧ (p1 → ((p2 ∨ p2) → p5)))) ∨ ((p1 ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184392097052117279670557674631 : (((p4 → ((((p3 ∧ p4) ∨ p3) → (p1 ∧ p3)) ∨ p5)) → p2) ∨ ((True → p1) ∨ ((p3 → p3) ∨ ((True ∧ (p2 ∧ p1)) → (p3 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700130585568490679409110418611 : (((((p4 ∧ p2) ∧ (((False → p5) ∧ p5) ∧ (True ∨ (True → p5)))) → ((((True ∧ p2) → (False ∨ (p3 ∧ (p2 ∨ p5)))) ∧ p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_964070594583366872898077691196 : ((((p5 → False) ∧ ((p2 ∧ False) ∨ (p5 ∧ ((p5 → (((p5 → p5) ∧ p2) ∨ p3)) ∨ ((True ∧ (p5 ∨ (True → (p1 → p1)))) ∨ p1))))) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h21 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h22 := h2 h21
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h24
        -- False on the left can always be used.
        apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358066971153320482761682920356 : (p5 → (p1 ∨ ((p4 ∨ p5) ∧ ((((p3 ∧ False) ∨ p4) ∧ (p1 → p1)) ∨ (((p5 ∨ p2) ∨ (p2 ∨ ((p5 ∨ p2) → False))) ∨ (True → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776499917503802105120066776090 : (((p1 ∨ (((((p2 ∧ p3) → p2) ∨ (p4 → (((p3 ∧ (False ∨ p1)) → p4) ∧ (p2 ∨ p3)))) → ((False ∨ p4) → (p5 ∧ p1))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_243946773104294875226221789963 : ((True ∧ p1) ∨ ((((p1 ∨ (p5 → p3)) → ((False → p5) → (((p4 → p3) ∨ False) ∨ p2))) → (p2 ∨ ((p5 → p4) ∨ (True → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200148543642577673134495474130 : ((((False → True) ∧ True) ∨ (p1 ∧ (p5 → False))) → (((True → (p5 ∨ False)) ∧ ((((p4 ∨ False) → p5) → False) ∧ (p4 ∨ (p2 ∨ True)))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h28 := h3 h27
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h35 := h3 h34
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h37 =>
          -- False on the left can always be used.
          apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h43 := h3 h42
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h45 =>
          -- False on the left can always be used.
          apply False.elim h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h49 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h50 := h3 h49
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- One of the premise coincides with the conclusion.
          exact h51
        case inr h52 =>
          -- False on the left can always be used.
          apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172274245043337188708069950568 : ((((p3 ∨ (p1 ∨ p3)) ∨ (False ∨ (False ∨ True))) ∨ (p1 ∨ (p1 ∨ (p3 → True)))) ∨ ((True → p4) → ((((False ∧ p1) ∧ True) ∧ p2) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2069126642099383689403646610 : ((((p2 ∨ (p4 ∧ p2)) ∧ ((False ∨ p5) ∧ ((((p2 ∨ p4) → p2) ∧ p4) ∧ True))) ∧ p1) ∨ (((False → (p1 ∨ p1)) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60408373327574126486686171761 : (((p4 → False) → ((False ∨ ((((True → (p1 ∨ (p3 → p3))) ∨ (p4 → ((p4 → p4) ∧ (False ∨ p5)))) ∨ p5) → (p1 ∨ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157675099108783263557182902181 : ((((False → (p1 ∨ p5)) → (True → (p1 ∧ (False → ((p2 ∨ True) ∧ p3))))) ∨ (p5 ∧ (p4 ∧ p4))) ∨ ((p3 ∨ ((True ∨ p1) ∨ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689027934169302191128719602653 : ((((((p2 → (p1 ∧ (p2 → (p3 → (p5 → p1))))) ∧ ((False ∨ p5) ∧ p5)) ∨ p3) ∨ ((True ∧ ((p3 ∨ p4) ∨ p3)) ∧ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330860267034451389285831147846 : (True → (p3 → (((((p1 ∨ ((False ∨ (False ∨ (p4 ∧ (False ∧ p2)))) ∨ False)) → p1) ∧ p2) → (p1 ∨ False)) ∨ (False → (p5 ∨ (p3 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40502609068154921139539005143 : ((((False ∧ (True → (((p1 ∨ (p1 → (p2 → p3))) ∧ (True ∧ (((True → (p5 ∨ p3)) ∨ False) → p2))) ∧ (p3 ∨ False)))) ∨ True) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179404909870582069508170677349 : ((p3 ∨ (p3 ∨ ((False → ((False ∨ p4) ∨ ((p5 ∧ p1) ∧ p4))) → p5))) ∨ (p2 → (p5 ∨ ((p4 → False) ∨ (False → (p5 → (False ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137518428639154926270803802032 : ((p5 ∧ ((p1 ∨ (p5 ∨ p2)) ∨ (p1 ∨ (p3 ∨ ((p3 ∧ ((True → (p5 → p5)) → (p1 → p1))) ∧ (p3 ∨ p5)))))) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49538956894672671281854694962 : ((((((p4 ∧ ((((p4 ∧ p4) ∨ False) ∧ p3) ∨ (p3 → p1))) → (p2 ∧ True)) → (p1 ∨ p5)) → (False ∨ False)) → ((False ∨ p4) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654553400773446434630278612774 : (((((False ∨ (p5 ∧ ((((p1 ∨ ((p1 → False) ∨ (p2 → (p1 ∨ p3)))) ∧ True) ∨ p2) ∧ (p3 → (p5 ∧ p4))))) ∨ True) ∨ (p1 → p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56482783901938348138533740979 : (((True ∧ ((True ∧ p1) → p2)) → (((False ∧ False) ∨ p3) ∧ ((((False ∧ p1) → p4) ∨ (False ∨ False)) ∧ ((p4 ∧ (p4 ∧ p1)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178160912946349410166577402161 : ((((False → p5) ∧ ((((True ∨ p4) ∧ p2) ∨ (p1 ∧ p1)) ∨ p4)) → p4) ∨ (True ∨ ((False ∧ (((True ∨ p1) → p4) ∧ (True ∨ p2))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262326580051379061259876427537 : (True ∧ ((((p1 ∨ False) ∨ (((p3 ∨ p3) → False) ∨ p5)) → ((p2 ∨ (p4 ∧ ((((p3 ∨ False) ∧ (p3 → True)) ∨ p5) ∨ True))) ∧ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192882334613814477173701959382 : (((p2 ∧ (((p4 → True) ∨ p2) ∨ p4)) ∧ (p2 ∨ p4)) → ((p5 ∨ ((p3 ∧ (p4 ∨ (True ∨ (p2 ∧ True)))) → False)) ∨ ((False → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325736587787615336455458237338 : (p5 ∨ (p2 ∨ ((False ∨ ((p1 ∨ p4) → (((p4 ∨ (p5 ∧ p3)) ∨ (((False ∨ (p3 → (True ∧ p1))) → (p5 ∧ p3)) ∧ False)) ∨ True))) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46829772446953132610321000247 : ((((((p5 ∧ p4) ∧ ((p2 → ((True → False) → p5)) ∧ ((True ∨ p5) → (p5 ∧ False)))) ∨ ((p1 ∨ False) ∨ False)) ∧ p4) ∨ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192545031929908978870869521370 : (((p4 ∧ ((p1 → ((p3 ∨ p5) ∨ p3)) ∧ p4)) ∨ p1) → (p5 ∨ (((p5 ∧ (True ∧ True)) ∧ (p1 ∨ (p4 ∧ (False ∧ (p3 ∨ True))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348227354706989763595202216565 : (p3 → ((p4 → p4) → ((((False → (p1 → p3)) → ((False → p5) → p4)) ∨ (True → p3)) ∨ ((p3 ∧ (p4 ∨ True)) → ((p5 ∧ p1) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259636377480983666395288054668 : ((p1 → False) → ((((((True → p5) ∧ (p5 ∨ False)) ∨ (p3 → p5)) ∨ p5) ∨ False) ∨ (p4 ∨ ((False ∨ (p2 → True)) ∨ ((p1 ∨ p2) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43910566983683586933345473966 : ((((((((((p2 ∨ p2) → True) ∨ ((p2 ∧ ((p1 → p4) → p3)) ∧ p5)) → p2) → p4) ∧ (True ∧ p2)) ∨ p4) ∨ (p5 → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188204269819356077902936159468 : ((((True ∧ (False ∨ p4)) ∨ ((False ∧ True) ∧ p5)) ∨ True) ∧ ((((True ∨ (True → True)) ∧ ((False → p2) → ((p2 ∨ p4) ∨ True))) → p5) ∨ True)) := by
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
theorem thm_5_vars_187666084359147707022840274579 : ((True → ((p5 → (p4 → ((True ∧ p5) ∧ p2))) → (p2 ∨ True))) → (((p1 ∧ ((p1 → (p5 → p4)) → False)) ∨ (p4 → (p3 ∨ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53870167120837227733265201867 : ((((False → p2) ∧ ((p2 ∧ (True ∧ (p3 → p3))) ∨ p4)) ∨ (((p5 → (True ∧ ((p1 ∨ p1) → (p1 → False)))) → p3) ∨ (p1 ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307608791691697198707888053451 : (p1 ∨ (p1 → ((False ∨ (p5 ∨ ((p1 ∨ ((p4 ∧ (p2 → p1)) ∨ p4)) → (((((p2 ∨ p4) → p2) ∧ (True → p4)) → p2) ∧ True)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : (p2 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56292260218691046438996322685 : (((((False ∧ p2) ∨ p4) ∧ True) → (((True ∨ p2) ∧ (((p4 ∧ (p3 → p5)) → (p3 ∧ p1)) ∧ p5)) ∨ ((False ∧ True) ∨ (p4 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689338469945533900668880306162 : (((((((((True ∧ (p5 ∨ True)) ∨ p2) → True) ∧ p2) ∨ (p1 ∧ p5)) ∨ (p1 ∧ p1)) ∨ ((False ∧ p4) → ((p1 ∨ p5) → (p4 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356613747587607944024404771933 : (p5 → (((p1 → (((False ∧ True) ∧ p3) ∧ False)) ∧ p4) ∨ ((p4 ∨ ((p4 ∧ (((False → p5) ∧ True) → True)) ∨ p5)) ∧ (True ∧ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134447404103209703088596274632 : (((((p5 ∧ (p2 ∨ ((True → (False ∧ (False → ((p4 ∧ (False ∨ False)) ∨ p4)))) → (p5 ∧ p1)))) → False) ∧ p2) → p3) ∨ ((False ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301819649211670475649582674345 : (False ∨ ((p1 ∨ False) ∨ (p1 ∨ ((p5 ∨ (False → (((True → ((True ∨ p4) ∨ (p5 → ((p2 → p1) ∧ True)))) ∧ False) → p1))) ∨ (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941918722119761540366465784104 : ((((((p4 ∧ p2) ∧ p2) ∧ p2) ∧ (((p3 → (p5 ∨ p4)) → p1) ∧ (((True ∨ p4) → (p1 ∧ (p2 ∧ ((p4 → p5) ∨ p5)))) ∨ p5))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258398714758478062447768917464 : ((p5 ∨ p1) → ((((p2 ∨ p1) ∧ ((p5 ∧ (True ∧ (p2 ∧ (False ∧ ((p4 ∧ False) ∨ ((p1 ∨ (True ∨ True)) ∨ False)))))) ∨ True)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239604142649820618782357610872 : ((p3 ∨ True) ∧ ((True → (p5 → False)) ∨ (p1 ∨ (p5 ∨ (((p1 → False) ∨ ((p1 ∨ p3) ∧ p4)) ∨ ((p2 ∧ p3) → (p1 ∨ (p5 ∨ p2)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347657468331521406223252943786 : (p3 → (((p4 ∧ p2) ∨ (p3 → True)) → ((((p2 ∧ p1) ∨ p1) ∨ ((p2 → ((p1 ∧ p3) ∨ ((p4 → False) ∨ True))) ∨ (p1 → p2))) ∨ True))) := by
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
theorem thm_5_vars_159538718417835880986406611461 : (((p2 ∧ (False → (p4 ∨ ((((True ∧ p5) ∧ (((p4 ∨ True) → p1) ∧ False)) ∧ p2) ∨ p1)))) ∧ p1) → ((((p5 ∨ p4) → False) ∨ False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234880083964367552914914382903 : ((p5 → (p4 → False)) → (p2 ∨ ((p2 → (p1 ∨ ((True ∨ p2) → ((((p2 ∨ (True → (p1 ∨ p1))) → p1) ∨ p2) ∧ p1)))) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350179989205077040659980013341 : (p4 → (((p1 ∨ ((p1 ∧ True) ∧ p1)) ∧ ((p1 → ((p2 ∨ True) ∨ False)) ∧ (p2 ∧ ((p2 ∨ p2) ∨ (p5 ∨ (False → (True → p1))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66166868720426391777998797854 : ((p5 ∨ (((((p5 ∨ (True ∨ (p5 ∨ True))) → True) → p5) ∨ (True ∨ (False → ((p1 ∨ p3) ∨ (p5 ∨ p2))))) ∨ (False → (False ∨ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_681917575066421573413714500859 : ((((((((((True ∧ p3) ∨ (p5 ∨ (p3 ∧ True))) → (p5 → p4)) → p5) ∧ p3) ∨ False) ∨ p2) ∧ (((p3 → (p1 ∨ p3)) ∨ p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217199507338526252342900806172 : ((((p3 ∨ p3) → p5) ∨ True) → (((p1 ∧ p4) → ((((False ∧ (((p1 ∨ False) ∧ False) ∧ (p1 → p4))) ∨ False) ∨ (p1 ∨ True)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3469068927697643870467078258 : (True ∧ (p4 → (p1 ∨ (((True → (((p2 ∧ (False → ((p5 → p1) → p1))) → ((p3 ∧ False) → p3)) → p1)) ∨ p5) ∨ (True ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618410070170573278403969746716 : (((((((p5 → False) ∧ True) ∧ p4) → (p1 ∨ (p2 → (p2 ∧ (((True → False) ∧ p1) ∧ (((p1 ∨ True) ∧ False) → (True ∧ True))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345375667524788866554264757424 : (p3 → (((((p3 → p1) ∧ p1) → (p5 ∨ ((((((True ∨ True) ∧ p4) ∨ p1) ∧ p4) → p3) ∧ ((p2 ∨ (p3 ∨ p3)) → False)))) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170614282405192194027495946983 : (((p4 ∧ True) → ((p2 ∨ (((p1 ∨ (False → True)) → p5) ∨ (False ∨ p1))) ∨ p4)) ∧ (p1 → (((((True → False) ∧ p1) → p1) ∨ p3) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685029295200372943236758239772 : ((((p5 ∧ (p3 ∨ (p1 ∧ ((((p5 ∧ ((p2 ∧ p5) ∧ True)) ∨ p3) ∨ (False ∧ False)) ∧ p4)))) ∨ ((p5 ∨ (p3 ∧ (False ∧ p2))) → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152331018142366212531422853463 : (((True ∨ (True → (p4 → False))) ∧ ((((p5 ∨ (False ∨ p5)) → p1) → (False ∨ (False ∧ p5))) ∧ (p2 → p5))) → (True → ((p3 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40879357351040142654544196295 : ((((((((p2 ∧ False) → True) ∨ p4) ∨ (False ∧ (p1 ∨ (p5 ∧ ((p4 ∨ False) ∧ p2))))) → ((True → p3) → p4)) ∧ (False ∨ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303945014775253968047509615749 : (p1 ∨ (((p2 ∧ ((p1 → p2) → (False ∧ False))) → ((p2 ∨ p1) → (((p2 ∧ p3) ∧ (p5 → (True ∧ (p1 ∨ False)))) ∨ (p1 ∨ p2)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342173718343448953941681233310 : (p2 → ((p2 ∧ ((p4 ∧ (p3 ∨ ((True → p3) → False))) ∧ (p4 ∨ ((True → p5) ∨ (False ∨ (True ∨ p2)))))) ∨ ((p3 → True) ∨ (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737655241690409984833008872706 : ((((p5 → p3) ∧ (((True ∧ (p4 ∧ True)) → False) ∧ (((p3 → p3) ∨ True) → ((p2 ∨ p2) ∧ ((p5 ∨ ((False → True) ∧ False)) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343223475696129519112684906367 : (p2 → (((p5 → p1) → False) → (((((p3 ∨ (((True ∧ p4) ∧ p2) ∧ False)) ∧ p3) → (p1 ∨ p4)) → p3) → (((p3 → p3) → p5) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350929903836006345011664800364 : (p4 → ((((((p2 ∨ (p5 ∨ p1)) ∧ (((p2 ∧ p1) → p2) ∧ p5)) → p1) ∧ (((p5 ∧ True) ∨ (p2 → False)) → p4)) → p5) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800234362286604787100749450015 : (((p2 → (((p1 ∨ (True → (p5 → (((p2 → (p3 → (p3 ∧ p4))) → (p1 ∧ ((p1 ∨ p3) ∧ (True → p5)))) ∧ True)))) ∨ False) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111043829340127832224316337104 : (((((((p5 → False) → False) → p3) ∧ ((p1 → (p5 ∨ p4)) ∧ (True ∨ (p3 ∧ False)))) ∨ (((p3 ∧ False) → p3) ∧ p4)) ∧ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256321380271058964920331860876 : ((False ∨ p1) → (p5 ∨ (((p4 → p1) → ((True → (False ∧ ((p1 ∨ p5) ∧ p1))) ∨ p4)) → ((p2 → ((p2 ∧ p1) → (p1 → False))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323808003121198886654182816116 : (p5 ∨ ((p1 ∨ ((((p1 ∧ True) ∨ (p1 ∨ (((False → (p4 ∧ False)) ∨ True) → p5))) → p1) ∨ False)) ∨ ((((p4 ∧ p3) ∧ True) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149843738384850004713976162613 : ((p1 ∨ ((p1 → p3) ∨ ((p3 ∧ ((((p2 → (p2 → (True ∨ p3))) ∨ p1) → (False ∧ p2)) ∧ p1)) ∨ p3))) ∨ ((p3 ∧ (p3 ∧ False)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181668335793364047063621264417 : ((p4 → ((((p3 ∨ (((p3 ∧ True) → False) ∧ False)) → p5) → False) → True)) → (((False ∧ (p1 ∨ p4)) ∨ True) → ((p2 → False) ∨ (False → p1)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178930317120428126665238254638 : (((p5 → p2) ∧ (((p3 → p1) ∨ (p3 → ((False ∨ p5) → True))) ∧ False)) ∨ (((True ∧ p1) ∨ p5) → (p4 ∨ (p3 ∨ ((p3 ∧ p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67684909102866350618321514457 : ((p1 → (p2 → (((((p5 → ((p4 ∧ p5) ∨ (False → ((p3 → ((False → (p2 → True)) ∨ p4)) ∧ True)))) → False) ∨ p4) ∨ True) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632326597334325260517776633147 : (((((p4 ∧ (((p1 → (p3 → p3)) → (p4 ∨ (((False ∨ (True → (p3 ∧ (p3 ∧ (True → p2))))) → p1) ∧ True))) → p5)) → p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206029810387484722534074854640 : ((p2 ∧ ((False ∧ p3) ∨ (p5 ∧ False))) ∨ (((p1 ∧ p3) ∧ p3) ∨ ((((p1 → ((p4 ∧ p3) → (p3 → p5))) ∨ (p3 ∨ p3)) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124311388481642814607137690740 : ((((False ∧ (False → p2)) → ((False ∧ False) ∧ p2)) ∧ ((p1 ∧ (((p2 ∧ p2) → p3) ∧ ((p1 → (p1 ∨ p4)) → True))) ∨ p2)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732241326685171950063493379562 : ((((False ∧ True) ∧ (((p2 ∧ (p1 ∨ (((((p4 ∨ ((p2 ∨ p4) ∧ p1)) ∨ False) ∨ (p2 → (p1 ∨ p3))) ∧ p3) ∨ False))) → p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1781507282707237413351493959 : (((((((p2 ∧ p4) ∨ p1) ∨ (False ∨ (False → (p4 ∧ (True ∧ False))))) → False) → False) ∧ (p5 ∧ (False → p2))) ∨ (p1 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41404140481184534989575682493 : (((((p3 → (((p1 ∧ False) ∧ False) ∧ (p1 → ((p4 ∨ p3) → True)))) ∧ False) ∨ ((p3 ∧ (((p1 ∨ p3) ∨ p2) ∨ p2)) ∧ p2)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593197904764237138373459125471 : ((((((True ∧ p2) ∨ ((p2 ∧ (p3 → True)) ∧ ((((False → False) ∧ p1) → p4) → ((p1 → p5) ∨ p5)))) ∨ ((p1 ∧ p2) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148501894376746765026817506686 : (((p1 ∧ (p3 ∨ (p2 ∨ (p5 ∧ ((True ∨ (p2 → p4)) → p2))))) ∨ (False ∧ (p1 → ((p3 → p3) → True)))) ∨ (p4 ∨ ((True ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590637863921110049391514882757 : (((((p3 ∧ ((((True → p4) ∧ p1) → (((p3 ∨ (p3 ∨ (p1 → p2))) ∨ (p1 ∧ ((p5 → p3) ∨ p3))) ∧ False)) ∨ p1)) → p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116162231030808704475881696829 : (((p4 ∨ (p4 → p4)) ∧ ((p1 ∨ ((p2 → ((((p5 ∧ p3) ∨ True) ∨ (((p3 → False) ∨ False) ∨ p3)) ∧ p1)) ∨ p1)) ∨ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206075234902186677641186645235 : ((p3 ∧ ((p5 ∨ p5) ∧ (p1 ∧ p2))) ∨ ((((True → ((True ∨ p1) → (p5 ∧ p3))) → p3) → p4) ∨ (((p4 → p1) → (p1 → p1)) ∨ p1))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178754502623920861873575134648 : ((((p3 → False) ∧ p2) ∧ ((((False ∨ False) → p1) → p5) ∧ (p3 ∧ False))) ∨ (p4 → ((((p3 ∧ p3) → (False ∧ p2)) ∧ (p1 ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684348071987683780751410065247 : ((((((False ∧ p2) ∧ ((p4 ∨ (p4 → (True ∨ p4))) ∨ p5)) ∧ (p3 ∧ (False ∧ (True → p1)))) ∨ ((p1 ∧ p2) ∨ ((p5 ∨ p4) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174380333681585728124763723814 : ((((((p2 ∨ p5) → False) ∧ p2) ∧ (p3 ∧ p2)) ∧ ((True ∨ p2) ∨ (True ∨ True))) → ((p4 ∧ ((p3 → p5) ∧ ((p2 ∧ p2) ∨ p5))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h19 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h20 := h6 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h22 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h23 := h6 h22
      -- False on the left can always be used.
      apply False.elim h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h28.left
  let h32 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h35 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h36 := h29 h35
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h38 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h37
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h39 := h29 h38
      -- False on the left can always be used.
      apply False.elim h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h42 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h43 := h29 h42
      -- False on the left can always be used.
      apply False.elim h43
    case inr h44 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h45 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h46 := h29 h45
      -- False on the left can always be used.
      apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h1.left
  let h48 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h49 := h47.left
  let h50 := h47.right
  -- Conjunctions on the left can always be decomposed.
  let h51 := h49.left
  let h52 := h49.right
  -- Conjunctions on the left can always be decomposed.
  let h53 := h50.left
  let h54 := h50.right
  -- Disjunctions on the left can always be decomposed.
  cases h48
  case inl h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h54
      -- One of the premise coincides with the conclusion.
      exact h54
    case inr h57 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h57
      -- One of the premise coincides with the conclusion.
      exact h57
  case inr h58 =>
    -- Disjunctions on the left can always be decomposed.
    cases h58
    case inl h59 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h54
      -- One of the premise coincides with the conclusion.
      exact h54
    case inr h60 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h54
      -- One of the premise coincides with the conclusion.
      exact h54
  -- Conjunctions on the left can always be decomposed.
  let h61 := h1.left
  let h62 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h63 := h61.left
  let h64 := h61.right
  -- Conjunctions on the left can always be decomposed.
  let h65 := h63.left
  let h66 := h63.right
  -- Conjunctions on the left can always be decomposed.
  let h67 := h64.left
  let h68 := h64.right
  -- Disjunctions on the left can always be decomposed.
  cases h62
  case inl h69 =>
    -- Disjunctions on the left can always be decomposed.
    cases h69
    case inl h70 =>
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h71 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h68
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h72 := h65 h71
      -- False on the left can always be used.
      apply False.elim h72
    case inr h73 =>
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h74 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h73
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h75 := h65 h74
      -- False on the left can always be used.
      apply False.elim h75
  case inr h76 =>
    -- Disjunctions on the left can always be decomposed.
    cases h76
    case inl h77 =>
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h78 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h68
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h79 := h65 h78
      -- False on the left can always be used.
      apply False.elim h79
    case inr h80 =>
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h81 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h68
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h82 := h65 h81
      -- False on the left can always be used.
      apply False.elim h82



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147015698936404919459061386904 : ((((((p2 → p4) → (((((False → p5) → p5) → p4) ∨ False) ∧ p5)) → (p5 → p4)) → (p3 ∨ p1)) ∧ p2) ∨ (False → ((p5 ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196743227048856680492675768629 : (((((True ∨ False) → False) ∧ (p5 ∨ p3)) ∧ p5) ∨ (((p2 → (True → ((p5 → p3) ∧ (p3 → p3)))) ∨ True) ∨ (p2 ∧ ((p4 → p2) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668840486477817392398402357027 : (((((((True ∧ ((p2 → p5) ∧ p3)) ∧ p3) ∨ (True → ((((p2 ∨ p2) ∧ (p2 ∨ p2)) ∧ p5) → False))) ∨ True) ∨ (p5 ∨ (p3 ∧ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184553113077112808426523429263 : ((((True → (p4 → (p3 → (False ∧ p4)))) → True) → (p5 ∧ False)) ∨ ((p5 ∨ ((((p4 ∧ p5) → p4) ∨ p5) ∨ p4)) ∨ ((p2 ∨ p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



