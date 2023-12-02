variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184672094655005827869472283822 : (((True ∧ (False ∧ (False ∨ (p2 ∨ p3)))) ∨ ((True ∧ p5) ∧ p5)) ∨ ((((p4 ∧ (p1 ∧ (p1 → False))) ∨ p3) ∧ (p5 ∨ (p1 → p1))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317959311089552848411177815333 : (p4 ∨ ((True → (((p3 ∨ (p1 ∨ (p3 → ((p3 ∨ True) ∧ (True ∧ p3))))) → (True → ((p3 ∧ (True → (p3 ∨ p3))) ∨ p4))) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114237627576088703184713650473 : (((True ∨ (((p3 → (True ∧ True)) → (p1 ∨ ((p4 ∨ p3) ∧ (p5 → (p5 ∧ (p5 → p5)))))) ∧ p2)) → (p5 ∧ (True ∧ p3))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340887785963146724289281565144 : (p2 → ((((p4 ∧ p3) ∨ ((p3 ∧ True) ∧ (((p4 ∧ p3) ∨ (False → p2)) → False))) ∨ ((p3 ∨ True) ∨ ((False → p4) ∧ (True ∨ False)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_153341457613946545954867781725 : ((p2 ∨ ((((False → (p1 ∨ True)) ∨ ((p2 ∨ p4) ∧ p5)) → (p2 → (((True ∧ p3) ∧ p4) → p3))) → False)) → (((p4 ∧ False) ∨ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((False → (p1 ∨ True)) ∨ ((p2 ∨ p4) ∧ p5)) → (p2 → (((True ∧ p3) ∧ p4) → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h4
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (((False → (p1 ∨ True)) ∨ ((p2 ∨ p4) ∧ p5)) → (p2 → (((True ∧ p3) ∧ p4) → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h28
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h35 := h20 h21
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172981293436330818136439822421 : ((p4 ∧ (p5 ∨ ((((p3 ∨ False) → p1) → p2) → (((False ∧ False) ∨ p4) ∧ p3)))) ∨ (p5 → ((((p4 ∧ p4) → False) ∧ (False ∧ p4)) → p4))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136442894068364077948484939915 : (((True ∧ ((p3 ∧ True) → p4)) → (p2 → (((p3 ∧ (p3 ∨ (((p2 ∨ p2) ∧ p3) → p1))) ∧ p4) ∧ (True ∨ p4)))) ∨ (True ∨ (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186906340023849534738332933591 : ((((p5 → False) ∧ p5) ∧ (True ∧ (True ∨ (False ∨ (p2 ∨ True))))) → ((((p3 → p2) ∧ p2) → (p1 ∨ (p2 ∧ (p2 → p4)))) ∨ (p1 ∧ p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h19 := h4 h18
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711411119864274267909601813200 : ((((p3 ∨ (((p4 ∨ p4) ∨ False) → p2)) ∧ (p1 → (((p5 → ((p1 ∨ ((p3 ∧ False) ∨ (p1 ∨ p2))) → (False ∧ p2))) → p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341711668312741674830725423847 : (p2 → (((((p4 ∧ (p4 ∧ ((p4 → p2) ∧ p1))) ∧ (p4 ∧ True)) ∧ p4) ∧ (True ∧ (False ∨ (p1 ∧ (p2 ∨ (p1 → True)))))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175910849381573560970207718280 : ((((p1 ∧ p3) ∨ (((p5 ∧ p1) ∧ False) → (p4 ∨ (False ∨ p1)))) ∨ p3) ∧ (((((p3 ∨ True) ∧ p2) ∨ (True → (p5 ∨ True))) ∨ True) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310363321593681033652310546414 : (p2 ∨ ((((p3 ∨ True) ∧ p4) ∨ ((p4 ∨ p3) ∨ True)) ∧ ((((p4 → (p1 ∧ (p5 ∧ True))) → p4) ∧ p1) → ((p3 ∨ p1) ∧ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137125106346569361571256791045 : ((True ∧ ((p3 ∧ False) ∨ ((((False ∧ (p3 ∨ p1)) → ((False ∧ p1) ∧ (False ∨ False))) → False) → ((p2 ∨ p4) ∧ False)))) ∨ ((p5 ∨ p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p3 ∨ p1)) → ((False ∧ p1) ∧ (False ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((False ∧ (p3 ∨ p1)) → ((False ∧ p1) ∧ (False ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- False on the left can always be used.
    apply False.elim h15
    -- Conjunctions on the left can always be decomposed.
    let h17 := h12.left
    let h18 := h12.right
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h11
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115955016670215370928565049070 : (((p1 → ((p2 → p2) → False)) ∨ ((p5 ∨ (p3 → (((p5 ∨ True) → p5) ∨ ((p1 → (True ∧ p3)) → p1)))) ∨ (p1 → True))) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_987112661846312949532182388609 : (((p2 ∧ (p3 ∧ ((p2 → False) ∧ ((((((True ∧ p2) ∨ ((p1 ∧ (p3 ∨ p2)) → False)) ∨ (p5 ∨ p4)) ∨ p5) ∧ p1) ∨ (p2 ∨ True))))) → p4) ∧ True) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h16 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h17 := h6 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h19 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h20 := h6 h19
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h23 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h24 := h6 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h26 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h27 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h28 := h6 h27
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h31 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h32 := h6 h31
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h34 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h35 := h6 h34
      -- False on the left can always be used.
      apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120844333993701880703755881785 : (((((p3 → p4) ∨ ((p5 ∨ (False → (False ∧ (p2 ∨ p3)))) ∧ p4)) ∨ (p1 ∨ (p5 ∨ (False ∨ ((p4 ∧ p2) → p1))))) ∨ p5) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40559740508038983156812279017 : ((((p2 → ((False ∧ (p4 ∧ (((True → (p1 → True)) ∧ (p4 ∧ p1)) ∧ p5))) ∨ (p3 ∨ ((p2 ∧ (p4 → p2)) ∧ True)))) ∨ p2) ∨ p5) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655127022842425824312418356231 : (((((p5 ∨ (((p2 → ((((p1 ∨ p3) → False) ∧ True) ∧ p1)) ∧ (p3 → p3)) ∧ (True ∨ (p1 ∧ (True → p1))))) → p2) ∨ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137060551376996777394152415343 : (((p2 → p4) → ((p2 ∧ ((p5 ∨ (True ∧ p5)) → (p5 → ((False ∨ True) ∧ ((p3 → (False ∨ p4)) ∧ True))))) ∨ True)) ∨ (True ∧ (True ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159304013888706915410727746874 : ((p5 → ((p2 ∧ (False ∨ ((p5 ∨ (p4 → (False → ((False ∧ True) → True)))) → (p2 → p4)))) ∧ True)) ∨ (((p2 → True) ∨ p5) ∨ (p3 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262307325874211544952953536354 : (True ∧ ((((((p4 → (p2 → (p2 → False))) → p1) ∨ p1) ∨ (p5 → p1)) → (p4 ∨ (p1 ∨ (p5 → ((p1 ∨ p4) → (False → True)))))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199225971024176273335101416251 : (((p5 ∨ (((p2 → p3) → p4) ∧ p1)) ∧ p2) → ((((p3 ∨ p5) ∨ p2) → (p2 ∧ False)) → (((True ∧ ((p1 ∨ True) → False)) ∧ p5) ∨ p1))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 ∨ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652302632943689871130559384239 : ((((p3 ∧ ((p2 ∨ False) ∨ (((((True ∨ (((p5 ∨ False) → p3) ∧ p5)) ∨ (p1 → (p2 ∧ p4))) → p3) ∨ p5) → p4))) ∧ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149277002059547188621946548232 : (((p1 → False) ∨ (p4 → (((p1 ∧ (((p3 → (p3 ∧ (p1 → False))) ∧ p1) ∨ p3)) → (p3 ∧ p2)) ∧ p1))) ∨ (False → ((p4 → True) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67339486357254990812159635168 : ((p1 → (((((p1 ∧ p3) ∧ ((p1 ∨ True) → p3)) → ((p2 ∨ p4) ∧ p4)) ∧ ((p3 ∧ ((p1 → p5) ∧ False)) → (p5 ∧ p4))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119935642714706753783982146615 : ((((((p5 → p2) ∨ (p3 ∨ ((False ∨ p2) ∨ ((p1 ∨ p5) ∨ (True ∨ (p2 → False)))))) → True) ∨ (True → (True → p5))) ∧ p5) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
theorem thm_5_vars_343153949084033898592678997089 : (p2 → (((p5 ∨ p4) → p5) ∨ ((((False ∧ (p5 ∨ (((p1 ∧ (p1 ∧ ((p5 → True) ∧ p2))) ∧ (p2 → False)) ∧ p1))) → p5) → False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226449099782308568681837516116 : (((p1 → p2) ∨ p5) ∨ (((p2 ∧ (p3 ∧ ((p4 ∧ (((False ∨ p3) → p3) ∧ p1)) → p3))) ∨ False) → (p2 → (((p2 ∨ p1) ∨ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612757494704345523892054249659 : (((((((p3 → p1) → (p4 ∧ p2)) → (((p5 ∨ p4) → (p4 ∨ (p4 → (p4 ∧ p2)))) ∧ (p4 ∧ (p1 ∨ p5)))) ∨ (p4 ∨ p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_57931087366750535851080089293 : (((True → (False → p1)) → ((p3 → ((((p4 → (True → p3)) ∨ True) ∨ (((p2 ∨ (p5 ∨ True)) ∨ p3) ∨ (p4 ∨ p4))) ∨ False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758244811181647096079155168212 : (((p1 ∧ (p5 → (p1 ∨ (p1 ∨ ((((p2 ∨ ((True ∨ (p4 ∧ (False ∨ (p2 ∧ p5)))) ∧ p1)) ∨ ((True ∨ p1) → p3)) ∨ False) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157501356176270866406038714963 : ((((p1 ∧ False) ∨ (((True → (p1 ∨ True)) → (p1 → p1)) → (False ∧ (p3 ∨ p2)))) ∨ (p3 ∧ p5)) ∨ ((p1 ∧ p3) → ((p2 ∨ p3) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318655786051468631760562531055 : (p4 ∨ ((p3 → (((True ∨ (p2 ∨ ((True → p3) ∧ True))) → False) → (p2 ∨ (((True ∧ p4) ∧ (False ∧ (True ∨ True))) ∧ p2)))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56717764749623222910246721356 : ((((True ∨ p5) ∨ p2) ∧ (((((p3 ∧ (p4 ∨ p1)) → (p2 ∨ (p4 → p5))) ∨ p4) ∨ (p2 → (((p2 ∧ p1) → False) ∧ False))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666254609116434845145707289550 : ((((((p3 → (((p2 ∧ p3) ∨ False) ∧ ((p5 → (p4 ∧ (p2 ∧ p4))) → p1))) ∨ (p5 → p2)) → (p2 → False)) ∧ ((False ∧ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774538229454219218307531061164 : (((False ∨ (((p5 ∧ (((False ∨ (False ∨ p5)) ∧ (p1 → (p3 ∨ p3))) ∧ p3)) → False) → ((p5 ∨ (False → p3)) → ((p4 → True) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47784612905252684716847577902 : (((((((False ∨ (p5 ∧ p2)) → (p1 ∨ p1)) → (p1 → (p4 → (p1 ∨ ((False → False) ∨ (p1 → False)))))) ∧ p2) → False) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139080008393561900430000421725 : (((((True → (((((p3 ∧ p5) → p3) → p5) ∨ True) ∧ ((False ∨ False) → p5))) ∨ (p5 → p3)) ∨ (p2 ∨ p1)) ∨ p4) → ((p1 ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_54470303819210764455677823543 : (((((p3 → (p2 ∧ p4)) → p3) ∧ (p2 ∧ False)) ∨ (((p1 ∧ (p5 ∧ p4)) ∨ ((p3 ∨ (p3 ∧ p3)) ∨ p2)) → (p3 ∧ (p1 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218773398703869767220384881876 : ((p1 ∧ ((True → p4) ∨ False)) → (False ∨ ((((p4 → ((p5 ∨ ((p1 ∧ p2) ∨ p4)) → (p5 ∧ False))) ∨ p5) ∧ (p4 ∨ (False ∧ True))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218069968567137276990947378643 : (((p4 ∨ p5) ∧ (p2 ∧ True)) → (((p5 ∨ (((p2 ∨ (p2 ∨ p5)) ∨ (p1 → (p1 ∧ p3))) ∧ p5)) → (p3 ∨ p4)) ∨ ((p1 ∧ p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149806980838066355257295459637 : ((False ∨ (p5 ∨ (((((p1 ∧ (p5 → p5)) ∨ (p4 → p1)) → ((p2 ∨ p3) ∧ p4)) ∧ (True ∨ p4)) → p1))) ∨ (((p3 ∨ p2) ∧ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621189449674472051035556270461 : ((((True ∧ (((False ∨ ((((p1 ∨ (((((p1 ∨ p4) ∨ p2) ∧ (p4 ∧ p2)) ∧ p1) ∧ p1)) ∨ False) → True) → p4)) ∨ p2) ∨ True)) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61140314827809606338682952716 : ((False ∧ (((((p1 ∨ p3) → False) ∨ p5) ∨ p2) ∨ (p4 → (((False → True) ∨ (p2 ∧ False)) → ((p5 ∨ (p3 → p5)) ∨ (False ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213911203954756137878871157532 : (((p5 ∨ (p3 ∨ p1)) ∨ p1) ∨ ((p3 ∨ ((((((p5 ∧ False) ∨ (p2 ∨ p2)) ∧ p5) → ((p2 → p3) ∨ True)) → (False ∨ False)) ∨ True)) ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64066573471919642450570887458 : ((False ∨ (((p4 → True) → ((p1 ∨ ((p2 → ((False ∧ True) ∧ (True → p3))) ∧ False)) ∨ p3)) ∧ ((p3 → True) ∨ (p4 → (False ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200653521409321855395600344832 : ((p1 ∧ (((True ∨ (p5 ∧ p5)) ∧ p4) → p2)) → (((p1 ∧ p3) → False) ∨ (((p4 → p2) → (False ∧ False)) → ((p4 → (p3 ∨ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166133845276609895465108976904 : ((True ∧ ((p2 ∧ True) ∧ ((p1 ∧ (p4 → p5)) ∨ ((p3 ∨ (False ∧ p4)) ∧ (True → p3))))) ∨ (((True → p3) ∧ (p3 ∨ True)) → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204921913532852295548897283454 : ((((p5 ∨ True) ∨ (p5 → p1)) → p5) ∨ ((((((p2 → p2) ∧ (p5 ∧ p5)) → p3) ∨ p1) ∧ (p5 → p2)) ∨ (True ∨ ((p1 → True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116799016783379426865074124648 : (((p2 ∨ p4) ∨ (((p1 ∨ ((p1 ∨ p2) ∧ p2)) → (p1 → (p4 ∧ (False → ((False → (False → p5)) ∧ p1))))) ∨ (p4 ∧ True))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825063799752507276796566211151 : ((((((p4 ∨ True) → True) → ((((False → p2) → ((p1 ∧ (p2 ∧ ((p1 ∧ p4) ∧ False))) ∨ p2)) ∨ (p3 ∨ True)) ∧ (True → False))) ∧ True) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721163690522345220561930668492 : (((((p4 → p1) ∨ (p1 ∨ p1)) → ((p3 → (((p3 ∧ ((p5 ∧ (((True ∨ (p3 → True)) ∧ p2) ∧ p5)) ∨ p3)) → p4) ∨ p3)) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60638866191440793234421082926 : ((True ∧ (((((p2 ∨ (False → (False → p3))) ∨ p5) → ((True ∨ True) → (p4 → (p5 ∨ (True → p1))))) → p2) ∨ (p2 → (True ∧ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47028231075655777329791110128 : ((((p3 → ((((p2 ∧ True) ∧ ((p2 → (p4 ∨ p4)) → (True ∨ ((True → p1) → (False ∧ True))))) ∨ p3) ∨ p1)) → p4) ∨ (p4 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55524227813416630966860005794 : ((((p5 → p3) ∨ ((p1 → p2) ∧ p3)) → (((p1 ∧ (False ∨ p1)) → (p3 ∨ (p2 ∧ ((False → False) ∧ (p1 → (False ∨ p3)))))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41474138880985489595994075678 : ((((((p1 ∧ ((p4 ∨ p3) ∧ (p5 → True))) ∨ p4) ∧ (False ∧ False)) ∨ (False → (((p2 ∨ (p2 → (p3 ∨ p2))) → p2) ∧ p4))) ∨ p5) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115166608010161373592730343295 : ((((((p1 ∧ p5) → ((p3 → p2) ∧ False)) ∧ p1) ∨ p5) ∧ (True ∧ (p4 ∨ (((p2 → True) ∨ ((p1 ∨ p1) ∧ True)) ∧ p1)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54179125040161232836029277798 : (((((p3 ∧ p3) → (True ∨ (False → p1))) ∧ p5) ∧ ((True → ((p2 ∧ (p4 ∨ p4)) ∧ ((False ∧ p4) ∨ p4))) ∨ ((p3 ∧ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186150779379654925197234159552 : ((((p3 ∨ p5) ∧ ((((False ∨ True) ∨ False) ∧ p1) → True)) ∨ True) → (p2 ∨ ((p2 → p3) ∨ ((True ∨ (((p5 ∧ p2) → p2) ∧ p1)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
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
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
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
theorem thm_5_vars_207081215995436573914506607852 : (((p4 ∧ (p5 ∨ (False ∨ True))) ∧ True) → ((p5 ∨ ((p5 ∧ p3) ∨ (((True ∨ (((p3 ∧ (False ∧ p4)) → p5) ∧ p1)) → p5) ∧ p1))) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225820673720739379113123571895 : (((True ∧ p3) ∨ False) ∨ (((True ∨ p3) ∧ (True → (((((p1 ∧ p4) ∧ (((p4 ∨ False) → p3) → p5)) → (p2 ∨ p5)) ∨ p2) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43236207067561229427788844685 : ((((p2 ∨ (p5 → (((p5 → p3) ∧ True) → (True ∨ (((p1 → False) ∨ p2) → (p5 ∧ (((p1 ∧ p4) ∧ p2) → False))))))) ∧ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49315080806388236452858360289 : (((p2 ∨ (p3 ∧ (((p2 ∨ True) ∧ ((p5 ∧ p1) ∧ p3)) → ((p3 ∨ p5) → ((False ∨ (False → p1)) ∨ True))))) ∨ ((p2 ∨ p2) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612689127941423736357215419078 : (((((((p4 → (((True ∨ p4) ∧ p3) ∧ p1)) → (p3 → (False ∨ p4))) ∨ ((p3 ∨ (p5 → p1)) ∧ (p2 ∨ False))) ∨ (False ∧ p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_628621542928015931385592830448 : (((((p3 ∨ ((p1 ∨ (p3 ∨ ((((False ∧ (p5 ∧ (p1 ∨ p3))) → ((p3 → (p5 → False)) ∨ p2)) → p5) → p4))) ∨ p1)) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241837994250467532392221977679 : ((p1 → p1) ∧ ((((((((p1 → p5) ∨ (p4 → (True → p5))) → p1) → (p4 ∨ p3)) ∨ True) → p1) ∨ True) ∨ ((p2 ∨ (p4 → p3)) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_67446044242688194807878535962 : ((p1 → ((((((False ∨ p1) ∧ (p5 ∨ (p5 ∨ (p4 → ((p2 ∧ p3) ∨ (p4 → p1)))))) → False) → p3) ∨ False) → ((True → False) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54046132873253881238363011058 : ((((True ∧ ((p5 ∨ p1) → p5)) ∧ (p2 → (p3 ∧ p2))) → (((p3 → p1) → (p4 → (p4 ∧ True))) → ((p3 ∨ False) → (False ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307243784963132185158353286395 : (p1 ∨ (p2 ∨ ((True ∧ ((p2 ∧ ((p3 → (p1 ∨ (p5 → True))) ∧ p1)) ∨ (True → ((p3 ∨ True) ∨ (False ∨ ((p4 ∧ p4) → True)))))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206432007441470312046479431441 : ((p4 ∨ ((p3 ∧ (p5 ∧ False)) ∧ p5)) ∨ (p4 → ((((True ∨ (p2 ∧ p5)) ∧ (True ∨ p1)) ∨ ((p5 → True) → ((p4 ∧ p2) ∧ False))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309215118026555260671053841638 : (p2 ∨ ((((((p3 → (False ∧ (p3 ∧ False))) ∨ False) ∨ True) ∧ (((p5 ∨ (True ∨ p3)) ∧ (False ∨ p1)) → p1)) ∨ (p2 ∨ False)) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137643134085121762804920544090 : ((False ∨ (((p2 ∧ (p4 ∨ (p3 ∨ (p2 ∨ p5)))) → True) ∧ (False ∧ (p5 ∧ ((p4 ∧ p4) ∧ ((False → p5) ∧ p1)))))) ∨ (False → (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174513032045333506065361823408 : (((p5 ∧ ((p2 → p3) → (True → p4))) ∨ ((p1 ∧ ((p2 → p1) → p1)) ∨ True)) → (((True → p3) → (p2 ∨ p3)) → ((p1 ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669535220391926826548634736741 : (((((True ∨ (((p1 ∧ p1) ∧ (((p2 ∨ ((True ∧ (p2 → p4)) → p1)) ∨ p4) ∨ True)) ∧ p1)) → (p5 ∨ p5)) ∨ (p4 ∨ (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716662989969325329394228063558 : (((((p1 ∨ True) → (p2 ∨ p3)) ∧ (p2 ∧ ((p3 → (p3 → (p1 ∨ ((p2 ∧ (p2 ∧ p2)) ∨ True)))) ∨ (p5 ∨ ((p4 ∨ p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60498610571120895354806767003 : ((True ∧ (((((p1 ∨ ((p2 → (p5 → (p4 ∨ p3))) ∨ p1)) ∨ p5) ∨ True) ∨ (p2 ∧ ((p3 → p1) → ((p1 → p2) ∧ False)))) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_181033496298253575906626606748 : (((p2 → p5) ∨ ((((p4 ∨ (False ∧ p5)) → p3) → p1) ∨ (p2 ∧ p2))) → (p3 ∨ ((p3 ∧ ((p3 ∨ (False ∨ p5)) ∧ p1)) → (p3 ∨ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161456628506398831628084866731 : ((p3 ∧ ((True ∧ (p5 ∨ ((((p5 ∨ True) ∨ True) → ((False → p4) ∨ p1)) ∨ (p2 → p5)))) ∨ p2)) → ((p5 ∨ (p4 ∨ p5)) ∨ (p3 ∧ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655708203829469145123540295069 : (((((p4 ∧ (((((((p1 → False) ∧ (True ∧ (True ∨ p3))) ∧ p1) → False) ∧ True) → p2) → p4)) ∧ ((p2 → p2) ∨ p4)) ∨ (p1 → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193308270078577062749220631303 : (((p5 ∧ (p4 ∧ p2)) ∨ ((p4 → (False ∨ p5)) ∨ p5)) → ((p1 ∧ (p3 ∧ ((p4 → p1) ∨ ((p4 ∧ True) → p3)))) ∨ (p3 → (False → True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688883776695115686324767315741 : ((((((((p4 ∨ (p2 → True)) → True) ∨ p2) → (p5 ∧ ((p5 ∧ p5) → p5))) ∧ p1) ∨ ((((False ∨ p3) → p3) ∨ (False ∨ p3)) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306035138940481362312438225690 : (p1 ∨ ((((p1 ∨ False) ∨ p1) ∨ p1) → (p3 ∨ (((p5 ∨ ((p4 → ((p3 ∧ p5) ∨ (p3 ∧ (p1 ∧ p2)))) ∨ p5)) ∧ p5) → (p4 ∨ p1))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301148553845922306702568640579 : (False ∨ (((p5 → (p1 ∧ (p1 → True))) → (True → False)) ∨ (((p2 ∧ (p3 → (((p3 ∨ True) → p2) ∧ p2))) ∨ ((p5 ∨ p2) ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174330653290812824512685361259 : (((p5 → ((((True ∨ p1) → p2) → (True → p4)) ∧ p1)) ∨ (False ∨ (p2 ∨ False))) → ((True → False) → ((((False ∧ p4) ∧ p5) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676359298470676107195967103633 : (((((p4 → p1) ∧ (True ∧ ((p4 ∧ (False ∨ (p2 ∨ ((p1 → (p3 ∨ (p5 ∧ p2))) ∧ True)))) ∨ p2))) ∧ (False → (p2 → (p5 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891041735984867351084956593936 : ((((p4 ∨ (p1 → ((True → ((p2 ∨ False) ∧ ((p1 ∧ True) ∨ (p5 ∨ (p2 ∧ p3))))) ∨ ((p3 ∧ (False → p3)) ∨ p1)))) → (False ∧ True)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (p1 → ((True → ((p2 ∨ False) ∧ ((p1 ∧ True) ∨ (p5 ∨ (p2 ∧ p3))))) ∨ ((p3 ∧ (False → p3)) ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210162376600156575187309220883 : ((((True ∨ False) ∨ p1) ∨ False) ∧ ((p4 ∨ ((p1 ∨ p1) ∧ p3)) ∨ (p4 ∨ ((((((p3 ∧ p4) ∨ p2) → (True ∨ p2)) ∨ p1) → False) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∧ p4) ∨ p2) → (True ∨ p2)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923779732441306218634387999698 : (((((p4 → (p3 ∨ p4)) → (True ∧ (((p1 ∨ p4) → p2) ∧ p5))) ∧ ((p3 ∨ p1) ∨ ((p1 ∧ ((p5 ∨ p3) ∧ (False → False))) → False))) → p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p4 → (p3 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p4 → (p3 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (p4 → (p3 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h18
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347061281926612830212665367958 : (p3 → ((True → (p4 ∧ ((p1 → ((True → (p5 ∨ p2)) ∧ True)) ∧ (p4 ∧ (True ∧ p2))))) → (True ∧ ((p5 → (False ∧ (True ∨ p2))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130188997155335065545808036528 : (((True → ((((((p2 → (p2 ∨ p3)) ∧ p3) → p2) ∧ True) ∨ p5) ∧ ((p1 → p2) → (p1 ∧ p4)))) ∨ (p3 ∨ True)) ∧ (p4 ∨ (True ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_859949198929133951471256884657 : ((((((True → (((p2 ∨ False) → (p4 ∧ True)) ∧ (p5 ∧ ((True ∨ False) ∧ (True ∧ (p4 ∧ (p1 ∧ p2))))))) → p1) ∨ (True → False)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → (((p2 ∨ False) → (p4 ∧ True)) ∧ (p5 ∧ ((True ∨ False) ∧ (True ∧ (p4 ∧ (p1 ∧ p2))))))) → p1) ∨ (True → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716524579965560989047277279518 : (((((p3 ∨ True) ∨ (p3 ∧ True)) ∧ (p3 ∨ ((((p1 ∧ p1) ∨ (p2 → (True ∧ False))) → ((p3 ∧ (p5 ∧ True)) → p1)) → (False ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113206226794107078069067370177 : (((((((p4 ∧ ((True ∧ (p3 → (p4 ∧ (True → True)))) ∨ False)) ∨ p1) ∨ p4) → ((p1 ∧ True) ∧ p2)) ∨ p3) ∧ (p3 ∨ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146565909947367863688395682120 : ((p5 ∨ (False ∨ (((p1 ∨ (True ∨ p3)) ∨ p1) → (p4 ∨ (((p4 ∧ p3) ∧ p4) → (p3 ∨ (p5 → p5))))))) ∧ (p5 → ((False ∨ True) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27
  -- Implications on the right can always be decomposed.
  intro h28
  -- Implications on the right can always be decomposed.
  intro h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230647688807435344547281659743 : (((p3 → False) ∧ p3) → ((((True ∧ (p2 ∧ ((p4 ∧ (p2 ∧ p1)) → p5))) ∧ ((True ∧ p5) ∧ (((True → False) ∨ p1) → True))) → False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140296417974067762777788970452 : (((((p2 ∧ False) ∨ p5) → (False → ((((False → False) → ((p1 → p1) ∨ p1)) → p4) ∨ p1))) ∧ ((p2 → p1) ∨ False)) → (p4 → (p1 ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67296069437630523469499645587 : ((p1 → ((((p3 ∨ ((p1 → (p5 → (p1 ∨ (p1 → True)))) ∨ (p4 ∨ (p1 → p5)))) → (p3 ∧ p4)) ∧ (True ∧ (p5 ∨ True))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156688181046476504659548397329 : ((((False ∨ (p1 ∧ (p5 ∨ ((True ∨ True) ∨ ((p5 → (p4 → False)) ∨ p3))))) → (p4 ∧ p1)) ∧ False) ∨ (((p1 ∨ (p1 → p1)) ∨ False) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215296533221097537977749197962 : ((p1 ∧ ((p3 ∧ p5) ∨ p2)) ∨ (False ∨ (((p2 ∧ (((p1 → ((((False → p4) ∧ p1) ∨ p2) ∧ p2)) ∧ True) ∧ p2)) → (False → True)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692281108547325060172618575688 : (((((p5 → (((p3 ∨ (p3 ∧ p4)) ∧ (p5 → (p2 → False))) ∨ True)) ∨ p2) ∧ (False ∨ (((p5 ∧ (p2 ∧ p2)) ∧ (p2 ∧ p4)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



