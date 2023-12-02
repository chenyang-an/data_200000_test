variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46297233233630491309611509900 : (((((p5 ∨ ((((((False → p4) → p3) ∨ (True ∧ p5)) → (p2 ∧ p5)) → p1) → False)) ∨ p4) → ((p5 → True) → p2)) ∧ (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178221709998123136650803835860 : (((False → (((p3 ∧ (p3 ∧ p5)) ∨ (True → (p2 ∨ p2))) → p1)) → p5) ∨ ((False ∧ (((p3 ∧ ((p5 → p5) → p3)) → p2) ∧ p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226616569864769859339409957443 : (((p5 → p4) ∨ p3) ∨ (p1 → ((((p4 ∨ p4) → (p5 ∧ ((p3 ∨ p2) ∧ (p1 → (p2 → (((True ∧ p3) ∨ True) → True)))))) ∨ p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48337933252750511008515174473 : (((p2 ∨ (((p5 ∨ False) ∨ (p1 → True)) ∧ (((p5 ∧ (p2 → False)) ∧ (p5 → ((False ∨ True) ∧ (True → p5)))) → False))) → (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66853551694025636023272413842 : ((True → (p5 → (((((p1 ∨ p3) ∨ (p3 ∧ (False ∨ (p1 ∧ (p1 ∨ False))))) ∧ True) → False) → ((p4 ∨ ((p4 → p2) ∧ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677524844920739854663351236601 : (((((p1 ∧ (((True ∧ (p3 ∨ p5)) → (p2 ∨ (p3 → p5))) → ((p3 ∧ p1) ∨ (p1 → p3)))) ∨ p3) ∨ (((p5 ∨ False) ∨ p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191124964856680314390257065955 : (((p1 → (False ∨ p2)) ∧ (((p5 ∨ True) ∧ p2) ∨ p4)) ∨ ((True ∨ (True ∧ (p2 ∨ (p5 → (((False ∧ (True ∨ p2)) ∧ p5) ∨ p2))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596407583609125179736544016849 : (((((p1 ∧ (True ∧ (p3 ∧ (p5 ∧ (p3 ∧ False))))) ∨ (p1 → ((p2 ∧ p1) ∨ (((p4 ∧ ((p1 ∧ p2) → p2)) ∨ p2) ∨ True)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349950338538269797949339973413 : (p4 → (((((p5 ∨ p3) ∧ (((((p5 ∨ p1) ∧ p4) → (p3 → (p3 ∧ p2))) → (p1 → p4)) ∧ True)) → ((p5 ∧ True) ∧ p2)) ∧ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213557400379272742196543911927 : ((((True ∨ p1) ∧ False) ∨ p1) ∨ ((p2 ∨ ((p4 ∨ (((p3 ∧ True) ∨ True) ∨ False)) → (p5 ∨ True))) ∨ ((p3 ∧ True) ∨ (True ∨ (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91173546409195426537130352901 : (((p5 → p3) ∧ (((p3 ∨ ((p1 ∨ (p3 ∧ (p5 ∨ p2))) → (False ∧ (p4 → p3)))) ∧ (True ∨ p3)) ∧ (((p3 ∧ p3) → False) ∧ p5))) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h8
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h5.left
      let h16 := h5.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : (p3 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h14
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h5.left
      let h22 := h5.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h23 : (p1 ∨ (p3 ∧ (p5 ∨ p2))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h24
        -- One of the premise coincides with the conclusion.
        exact h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h26 := h19 h23
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h5.left
      let h30 := h5.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h31 : (p1 ∨ (p3 ∧ (p5 ∨ p2))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h28
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h32 := h19 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70239026906968069113743665287 : ((((((p4 → p1) → (p2 ∨ (p3 ∧ ((((p5 ∨ True) ∧ ((p3 ∨ p2) ∨ p1)) ∨ True) ∧ (True → False))))) ∧ p1) ∧ (False → p5)) ∧ p1) → p2) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h23 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h24 := h16 h23
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- One of the premise coincides with the conclusion.
            exact h25
        case inr h26 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h28 := h16 h27
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h33 := h16 h32
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- One of the premise coincides with the conclusion.
            exact h34
        case inr h35 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h36 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h37 := h16 h36
          -- False on the left can always be used.
          apply False.elim h37
    case inr h38 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h40 := h16 h39
      -- False on the left can always be used.
      apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192334935942310563362025829682 : (((p1 ∨ (p4 ∨ ((True ∧ p1) ∧ (False ∧ p3)))) ∧ p5) → (((((p3 ∧ p1) ∧ p2) ∨ p5) ∧ ((((p3 ∨ False) ∧ True) ∨ True) ∧ p4)) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597982381498942735756438230652 : (((((p4 ∧ (True ∧ p4)) ∧ (((p5 → ((False ∧ False) ∧ False)) ∧ ((((((p1 ∨ p4) → True) → p2) → p4) ∨ p2) → False)) ∨ p2)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219522210876107091998304807424 : ((p5 ∨ (p3 ∧ (p2 ∨ p4))) → ((((p3 ∨ (p3 ∧ (False ∧ ((p1 → (p4 → ((p4 ∧ p2) → p3))) → False)))) → p3) → p1) → (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∨ (p3 ∧ (False ∧ ((p1 → (p4 → ((p4 ∧ p2) → p3))) → False)))) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∨ (p3 ∧ (False ∧ ((p1 → (p4 → ((p4 ∧ p2) → p3))) → False)))) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- False on the left can always be used.
          apply False.elim h24
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125035585404956373213095048119 : ((((True ∨ p5) → False) ∧ (True → ((p1 → (p5 ∧ p2)) ∨ (((p4 ∨ p1) → True) ∨ ((p4 → (True ∨ (p2 → p2))) ∧ p5))))) → (p5 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217096334640541625578715071547 : ((((p3 ∧ p3) ∨ False) ∨ p5) → (((p3 ∧ ((False ∧ p2) → p2)) ∧ (p2 ∧ (p1 ∨ p3))) ∨ (p3 ∨ (((p4 ∨ p4) ∨ (True ∧ p3)) ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656905253317696372501874506501 : ((((((p1 ∨ (p3 ∨ p5)) → p1) ∨ ((p2 ∧ p5) → ((((p2 → p5) → False) ∧ False) ∨ (p3 → (False ∧ (p4 → True)))))) ∨ (False → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64088385878322223741353684950 : ((False ∨ ((((p4 ∧ True) ∨ (((p1 ∧ p1) ∧ True) ∧ p3)) ∧ (True ∧ p4)) ∨ (p3 → ((p2 → p5) ∨ ((p1 ∨ p3) ∧ (False → p1)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128190913594808918814508088804 : ((p2 → (p2 → ((p2 ∧ p1) → (p1 ∨ ((((p4 ∧ (p4 → p2)) → p1) → (p3 ∧ ((p3 ∧ (p4 ∨ False)) ∧ p4))) ∧ p2))))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306451218988643599951482240556 : (p1 ∨ ((p2 ∨ p4) ∨ ((p3 ∨ (((True ∨ True) → p1) ∨ (False ∧ (((p2 ∨ p4) ∧ p3) → False)))) ∨ ((((True ∨ p3) ∨ False) ∨ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16797311257958853421519832196 : ((((p4 ∧ ((p1 ∨ (True ∨ p4)) ∧ (True ∨ False))) → ((p2 ∨ p1) ∧ ((p1 → p1) ∧ ((p3 → True) ∧ p5)))) ∨ ((False → p1) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39733785287592389134965713442 : (((p5 ∨ ((True → p5) ∨ (True ∧ (((p3 ∨ p5) ∧ (((p4 ∧ ((p4 ∧ (p4 → p1)) → True)) ∧ True) → True)) → (False ∧ False))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314406464116140882969592813778 : (p3 ∨ ((((((p5 ∧ p4) ∨ ((p2 ∨ p3) ∨ True)) ∨ p4) → ((p4 ∧ p1) ∨ (p1 ∧ (p5 ∧ p3)))) ∨ p2) ∨ (p3 ∨ ((p4 ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625941281114249118762117553256 : ((((p2 → ((p2 ∨ ((((p5 → p5) ∨ p2) → ((p4 ∨ True) ∨ p1)) → ((False → False) ∧ (False ∧ (True ∧ p1))))) → (p5 ∧ False))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40951756851741164861567979035 : ((((((p4 ∨ (((False ∧ False) ∨ (True ∨ True)) ∧ (((True ∧ (p5 → p4)) → p4) ∨ p2))) ∨ p1) → (p4 ∧ p2)) ∨ (True → p1)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56238518415390626695551090867 : (((p5 ∨ (p4 ∧ (p3 ∧ p5))) ∨ (p5 ∨ ((p3 ∨ (True ∧ p1)) → ((p5 → (p4 ∨ (p1 ∨ False))) ∨ (((p3 ∧ p2) ∧ p3) → p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191937928107801810133965087448 : ((True → (((False → p1) → p5) → (p2 ∨ (p3 → p1)))) ∨ (((p4 ∨ p1) → (((False ∨ p4) ∧ (False → ((p2 ∨ p3) ∧ p3))) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250167364567319517465485380734 : ((True → p5) ∨ (((p5 → p4) → ((p2 → True) → p4)) → (p4 ∨ (p5 → (((p2 → True) ∨ p2) ∧ ((((p1 → p3) ∧ p5) ∨ p5) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218254489680024390020067736943 : (((False ∨ p3) ∨ (True ∨ False)) → ((((p2 ∨ (((p2 ∧ p5) ∧ (p4 ∨ False)) ∧ True)) ∨ (True ∨ (((False ∧ p4) ∧ p5) ∨ p5))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305428931957908883248029346791 : (p1 ∨ ((((p1 ∧ ((p5 ∧ p3) ∨ (p4 → p5))) ∨ (p3 ∧ (False ∨ (p1 → p3)))) ∨ True) → (p5 ∨ ((False ∨ (p1 ∨ (p3 ∨ p2))) ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184723198458549574376205268559 : (((p1 ∨ (((p5 ∨ p2) ∧ False) → p5)) → (False ∧ (True → p5))) ∨ ((((p1 ∧ p2) → (p2 → (p4 ∨ ((True ∧ False) ∨ p1)))) ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59670854474579085394227115337 : (((True ∧ p2) → ((((False → ((((p5 → p4) → p1) ∨ False) ∧ ((p3 ∧ (p4 ∧ p4)) ∨ p4))) → ((p5 ∨ True) → p3)) ∨ True) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_64980637771822496365569442431 : ((p2 ∨ ((p5 ∧ ((p3 ∨ p3) ∨ p1)) ∨ ((((p5 → (p2 → (p2 → p3))) → (p3 ∨ (p1 ∧ False))) → p3) ∧ ((False ∧ False) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112700927701494106799615418075 : ((((p2 → (p4 → (((p2 ∧ (p5 ∧ p5)) ∧ (p5 ∧ (False ∧ p3))) ∧ (p5 → True)))) ∨ ((p3 → (p1 ∧ p3)) ∧ p3)) → p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657315727588199224711968469178 : (((((p5 ∧ False) ∧ (p4 ∨ ((p2 ∧ p5) ∨ (((((p4 ∧ p2) → ((True → p1) ∨ (p2 → p1))) ∨ p5) → False) ∨ p3)))) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_139649846327997772849297597164 : ((((((False ∧ False) ∧ False) ∨ (p1 ∧ p1)) → (False ∨ ((p5 ∧ True) ∨ (True ∧ (p5 ∨ ((p5 ∨ True) → p4)))))) → True) → ((True → p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792636730714304724781619275917 : (((True → (((p5 ∧ (p3 ∨ p3)) ∧ (p4 ∨ p1)) ∨ ((True → (((True → p1) → ((p5 ∨ False) ∨ p2)) → ((p1 ∧ p2) ∧ False))) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731399245789631387551482287934 : ((((p5 ∨ (True → True)) → ((((p1 ∨ False) ∨ (p2 ∨ p5)) ∧ (p2 → ((p1 → (False ∧ p5)) → ((p3 → p5) → p2)))) ∨ (True ∨ p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606944537297099851241889776720 : (((((((True → ((p3 ∧ (False ∧ p4)) ∧ (((p5 ∨ p2) ∧ False) ∨ p4))) ∨ (p5 ∧ p2)) → (p5 ∧ (p4 ∨ (p1 ∨ p3)))) ∧ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_183368766478587076995599439717 : ((True ∨ (False ∧ ((p4 ∨ (((p4 ∨ p1) ∧ True) → p4)) ∧ p2))) ∧ ((p2 ∧ (((p4 → False) ∨ (True → False)) ∧ (p4 ∨ p5))) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39686503895377273292169907228 : (((p4 ∨ ((((True → True) ∧ True) → (p3 ∨ ((p3 ∧ (p5 ∨ p3)) → False))) → ((p2 → (True ∧ ((p1 ∧ p2) ∧ p4))) ∨ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244938668469223713887522564182 : ((p1 ∧ p3) ∨ (((True ∧ (p1 ∧ p2)) ∨ ((False ∨ (p5 → True)) ∨ (True → (p2 → p4)))) ∨ (True ∨ (((p4 ∨ (p3 ∧ p3)) ∧ False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178503303880769818298839664046 : (((p5 ∨ (((p4 ∧ True) ∨ p1) ∨ (p2 ∧ p2))) ∨ (p1 ∨ (True ∨ p1))) ∨ (False → (((True ∨ False) ∧ (p4 → True)) → (p2 ∨ (p5 → p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302682962638856360174529476862 : (False ∨ (p3 ∨ ((p5 → ((((p3 ∧ (p4 → p3)) ∨ (p4 ∧ p5)) ∨ ((p4 → p2) ∧ p1)) ∨ (p5 → (((p3 → p3) → False) ∧ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611857739776465889580881275800 : (((((p4 → ((True ∧ ((p4 ∧ False) → (((p2 ∧ True) → (False ∧ True)) ∨ (p2 ∨ (True ∨ (p4 ∧ True)))))) ∧ (True ∨ False))) → p1) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226300800963139620372820113419 : (((p4 ∨ p4) ∨ p2) ∨ (p1 ∨ ((p2 ∨ ((p3 ∧ (((p2 ∧ ((p4 ∨ p3) ∧ False)) ∧ p5) ∨ (p2 → p5))) ∧ p3)) ∨ (True ∨ (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149639168549439172348512950513 : ((p4 ∧ ((((p3 ∨ p5) ∨ p2) → (((((p1 → p3) → p5) → (False ∧ p1)) → p5) → p4)) ∧ (False → p1))) ∨ ((False ∨ p1) → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242331363932862732184635857427 : ((p2 → p2) ∧ ((p5 ∨ ((p1 ∨ (p4 ∨ (p3 → p4))) → p1)) ∨ ((p1 ∧ False) → ((True ∧ ((False ∧ p1) ∨ p2)) ∨ (p1 → (p5 → p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182006264767823383009726455593 : ((((((p4 → (p1 ∧ p3)) ∧ p1) → False) ∨ (p1 → False)) ∨ True) ∧ ((True ∨ (((p5 → (p3 ∨ ((True → True) → p1))) ∨ True) → p2)) ∨ True)) := by
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
theorem thm_5_vars_773401572936129420795744911728 : (((False ∨ ((p5 → ((p4 ∧ ((True ∨ (((((p3 ∨ False) → p2) → p4) ∨ p1) ∧ True)) → ((p2 ∨ (p5 → p3)) → p2))) ∧ p3)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_583846854360292702655953529171 : (((p5 → ((((True → (p1 ∨ p5)) → (p2 → p3)) ∨ (False → p2)) → (p4 → (((((p5 ∨ False) ∨ True) → (True → True)) → p2) ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351832423272885987850112933906 : (p4 → ((p5 ∨ (((p1 → p5) ∨ (p2 → (p3 → p2))) → (p4 ∧ False))) ∨ (p4 ∧ (p2 ∨ (((p2 → (False ∧ (p3 ∧ p5))) → True) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317632233455428260860627844925 : (p4 ∨ ((((((((True → p1) ∧ p5) ∧ (p5 → p1)) → p4) ∨ p1) ∨ (p4 → ((p3 ∧ ((p2 → p5) ∨ True)) → (p1 ∧ True)))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3205491544428687514249110283 : ((p4 ∧ p4) ∨ ((p4 ∧ (((((((p1 → False) → p5) → p1) ∧ (p1 → p2)) ∨ (p5 ∨ True)) ∧ (p3 ∧ p5)) ∨ False)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49187145760227778453976224480 : ((((p2 ∧ ((p4 ∨ p3) ∨ p1)) → ((True → (True ∧ p1)) ∨ ((p2 → p1) ∧ (((p5 ∨ p1) ∧ False) → p4)))) ∨ (p1 ∨ (p2 → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219767939309837728165819355718 : ((p2 → ((p4 → p4) ∨ False)) → ((p2 ∧ p4) ∨ (((p5 ∨ (p3 ∧ (((p5 ∨ p1) ∨ True) ∨ p1))) ∨ (p5 → ((p1 ∧ True) ∨ True))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33837608944937239493772331443 : ((p5 ∨ (((p5 ∨ (False ∧ p2)) ∨ ((((True ∨ (p1 ∧ p5)) ∨ p3) ∨ p5) ∨ (p2 → p4))) → ((p1 ∧ (p4 → True)) ∨ (True ∨ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1516872912646815511146723917 : ((((False ∨ p1) ∧ (p4 → ((p2 → p5) ∧ p1))) ∨ (p3 ∨ ((((p5 → (False ∨ False)) ∨ True) ∨ True) ∧ (False → p2)))) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156976701377803125403178639602 : (((((p2 ∧ p5) → (((False ∨ p3) ∨ p4) ∧ False)) ∧ ((((True ∧ p2) ∨ p4) → p3) → p5)) ∨ p1) ∨ (p3 → (((p4 → p5) → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50273875188862698747585770405 : ((((((p4 → ((True → (True ∨ ((p1 ∧ p4) ∧ p5))) → p4)) ∨ p1) ∧ (p1 ∨ p2)) ∨ (p1 ∨ p3)) ∨ (p3 ∧ (False ∧ (p3 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691580306033572986912821754682 : ((((p1 ∧ ((p5 ∨ False) ∨ ((((p3 ∨ False) → p2) ∨ p4) → ((p5 ∧ p5) ∨ p1)))) → (((p3 ∨ (p4 ∨ (False ∨ p3))) ∨ True) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336110517143264980096388299037 : (p1 → ((((((p2 → False) ∧ (p2 → (True ∧ p1))) ∨ ((p4 ∧ p4) ∧ (False ∧ ((((p2 ∧ p1) ∨ p1) ∨ p1) → False)))) ∨ p1) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116192459002148693801204554497 : ((((p3 ∧ p5) ∧ p2) ∨ (p4 ∧ (False ∧ ((((False → (p2 ∨ True)) → (True ∧ ((True ∧ True) ∨ p4))) ∨ p1) → (p2 → p3))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692373550996665002716120152577 : ((((((True → False) ∧ (((p2 ∨ True) → ((p1 ∧ p2) ∨ True)) ∨ p1)) → p4) ∧ ((p1 → (p3 ∨ False)) → (((False → p4) → p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319492761883906035611080920465 : (p4 ∨ (((False ∧ p3) ∨ (((True → p3) → ((True ∧ p1) → p2)) ∨ True)) → (p3 → ((p2 → (p2 → p1)) ∨ (p3 → ((False ∧ p3) → p5)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60234492500269787551804186017 : (((True → p4) → (((False ∨ ((((p2 → p1) → True) ∨ p4) ∧ (p4 → (p5 ∧ ((p3 ∧ p3) ∧ False))))) ∨ (p3 ∨ p3)) → (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60771535112696623219520209935 : ((True ∧ ((p4 ∨ p2) ∨ (((p5 ∧ p5) → (p2 → p2)) → ((((p2 ∧ False) ∧ p3) ∨ p1) ∨ ((((p4 ∨ p1) ∧ p2) ∨ p2) → True))))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254635959566764682418746252911 : ((p3 ∧ p2) → ((((p1 ∧ p2) ∧ p4) ∧ (p5 → ((((p5 ∨ False) ∧ p5) → ((p2 ∧ ((True ∧ False) ∨ p4)) ∧ p4)) ∧ (p2 ∨ False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307266293172658293904390293828 : (p1 ∨ (p2 ∨ ((((((False → p3) ∨ p2) ∧ True) → p2) → p1) ∨ (((((True ∨ ((True → p4) → p3)) ∨ p3) ∨ p3) → False) → (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∨ ((True → p4) → p3)) ∨ p3) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55621860337927380787961279610 : (((p4 → ((p5 ∧ (p2 ∨ True)) ∧ True)) → (((True → p2) → (p3 ∧ ((p2 → ((p3 ∧ (p4 ∧ False)) ∨ True)) → (p3 ∧ p5)))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147114380166159785990633389832 : ((((p1 → False) ∧ (((p4 → (p4 → p2)) ∨ p5) → (((p2 ∨ p2) ∧ False) ∧ (False ∨ (True → p1))))) ∧ p2) ∨ (((False ∨ False) → p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149105903704609112690405061358 : (((p1 → (p5 → True)) → ((p4 ∧ (p1 ∧ ((False ∨ p3) → p2))) ∨ (((p5 → (False ∧ p1)) ∧ p3) → True))) ∨ (((p1 ∨ p1) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44569543798229995871061822716 : ((((p3 → ((((p2 → True) ∨ p1) → p2) ∧ p4)) ∧ ((False ∨ (p2 ∨ (False ∧ True))) ∨ (p2 ∨ (p1 ∨ ((True ∧ False) ∨ p5))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189561309490979759321089787840 : ((True ∨ ((False ∨ (False → ((True ∨ p4) → p3))) → p4)) ∧ ((((p3 → (p1 ∨ p2)) → p1) → (p1 → p5)) → ((p3 → (False ∧ True)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244768783875987451208388500550 : ((p1 ∧ False) ∨ ((True ∧ p1) ∨ ((p1 ∧ ((p5 ∨ (p4 ∨ p2)) ∨ (False ∧ ((False ∨ (p2 → (True → p4))) ∨ p1)))) → ((p5 → False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775210262957494770482158475652 : (((False ∨ ((p1 ∧ p1) → (p4 ∧ (p3 ∨ ((p4 → ((((p1 ∧ p3) ∧ False) ∧ ((p2 ∨ p3) ∨ p4)) ∨ ((p5 ∧ True) ∧ p4))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591790464835801622631822000615 : ((((((p1 ∨ ((((((p5 ∧ (False ∧ p4)) → True) ∧ p4) ∨ p1) ∨ (False ∨ (p5 ∨ p4))) ∧ False)) ∨ (p2 ∨ p3)) ∨ (p1 ∧ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61163561338549091984967486935 : ((False ∧ ((True ∧ (p3 ∨ p1)) ∧ (((False ∨ ((p5 → (p2 ∧ p2)) ∨ ((True → (p5 ∧ (p1 ∧ p1))) ∨ p4))) → p4) ∧ (True ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43714267611649992272393931572 : ((((((False ∨ True) → p1) ∧ ((False ∧ (((p5 ∧ p5) ∨ p3) ∧ (p4 ∨ ((p3 ∧ (p1 ∨ False)) → (True ∨ True))))) ∧ p5)) → p2) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683917217978341998013628173174 : (((((((p4 → (p2 → (p3 ∧ False))) ∨ ((((True → p3) ∧ False) ∨ p5) ∧ True)) ∧ True) → p2) ∨ (((p5 ∨ False) → (p3 → p5)) ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215766683124384400572305025550 : ((p1 ∨ ((p3 → p4) ∨ p1)) ∨ ((False ∧ (((True ∨ p4) ∨ (p3 ∨ p2)) → (p3 ∨ ((p1 ∨ p3) ∧ (p1 → ((True ∨ True) → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116566614105498196614598469557 : (((p2 ∨ p3) ∧ (True ∧ (((p2 ∨ p4) → ((p2 ∨ (((p4 ∨ p5) ∧ p1) ∨ ((p5 → (p1 ∨ p4)) → p2))) ∨ False)) ∧ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328530799785787007765627033055 : (True → ((False ∧ (p2 → (((p3 ∨ (((p4 ∨ p4) ∨ p4) → (p3 → False))) ∨ p5) ∧ p2))) ∨ (True ∨ ((False ∧ (False → (p1 ∧ p2))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186533223794855210944566229111 : ((((False ∨ ((p1 ∧ True) ∨ (p5 → p1))) → p2) ∨ (False ∨ p1)) → ((p1 → p2) → ((True → ((p1 ∧ (p5 → p1)) → (p1 ∧ p2))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758480676784193112790452319985 : (((p2 ∧ ((False ∨ (((False ∧ p4) ∨ p1) ∨ (((p2 ∨ (((((p1 ∧ (True ∧ p4)) ∧ p5) → p4) → p2) ∨ p4)) → p1) → False))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611974281941234971494803092935 : (((((((((p4 ∨ p5) ∧ (((p3 → (True → p3)) → p4) → True)) → p1) ∨ ((p4 → (True ∨ p3)) → p1)) ∨ p1) ∧ (p4 ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_895299813561867607403803720 : ((p3 → ((p3 ∧ ((True → p3) → (False ∨ (p2 → ((((((p3 → p3) → False) ∨ (False ∨ p4)) → False) ∨ p4) ∧ p4))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666076680720210629587194155322 : ((((((((True ∧ False) ∧ p2) ∧ ((p2 ∨ p5) ∧ (((True ∨ p4) → p3) → False))) ∧ (p2 → p4)) ∧ (p5 → p3)) ∧ (False ∧ (False ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147354086441899201784533958888 : (((((p1 ∧ (((p3 ∨ (True ∧ False)) → p5) → ((False ∧ False) ∨ p3))) ∧ False) ∨ ((True → p3) → p1)) ∨ True) ∨ ((True → (True ∧ p1)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264083687996566699663642299404 : (True ∧ ((p5 ∨ ((p5 → False) ∨ ((p1 ∨ p2) ∧ (True ∧ p2)))) ∨ (((p1 ∨ (((((p2 ∨ p5) ∨ False) ∧ p2) → p4) ∧ p4)) ∧ p1) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777353171313500412044653299116 : (((p1 ∨ ((p5 ∨ (((p1 → p2) ∨ False) ∨ (p2 → (((p4 ∧ (True ∧ (p1 → True))) ∧ p1) ∨ p5)))) ∨ (p1 → (p2 ∧ (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738782241264571418567872874186 : ((((p2 ∧ p4) ∨ ((((((p5 → True) ∧ p5) → ((((False → True) ∧ (p4 ∨ p2)) ∧ p4) ∧ (p3 → p4))) ∨ (True ∧ True)) ∨ p4) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610135541895164332595995506857 : ((((((p5 ∨ (False → ((p5 ∨ ((((((p1 → p3) → p3) ∧ ((p2 ∨ True) → p3)) ∧ False) ∧ p1) → p1)) ∨ p2))) ∧ p2) → False) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753227595878162477200570888257 : (((False ∧ ((((p5 ∨ (p4 ∨ ((True → (True ∨ (True ∨ (True ∧ False)))) ∧ p3))) ∧ ((p2 ∧ p3) → p5)) ∨ (p5 → p5)) ∨ (False → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43091985118907603327609730796 : (((((((False → p2) ∧ (p5 → (((p4 → p2) → ((p2 ∨ True) → False)) ∧ True))) ∨ (True ∨ (p4 ∧ False))) → (False ∨ p3)) ∧ p5) → p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False → p2) ∧ (p5 → (((p4 → p2) → ((p2 ∨ True) → False)) ∧ True))) ∨ (True ∨ (p4 ∧ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115369275806450740531917552084 : ((((p1 ∨ ((p3 ∨ (p3 → False)) ∧ p5)) → p5) ∧ ((p2 ∨ p1) ∧ ((((p1 ∧ p5) → p2) ∨ (p2 → p3)) ∧ (True → p1)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60493635074969161322283499837 : ((True ∧ ((((((p3 → (False ∨ p2)) ∨ p1) → p3) ∨ (((p1 ∧ p5) ∨ (True ∧ p2)) → (p4 → (p1 ∨ p4)))) → (p5 ∧ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150316265523774903907911545461 : ((p4 → (p4 ∧ (True → (p4 → ((((p4 → (p2 ∨ p3)) → (p5 → p3)) ∧ ((p5 ∧ p2) ∨ p2)) ∨ p4))))) ∨ (False ∧ ((p5 ∨ False) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116324741051432929579129781448 : ((((p5 ∧ p1) ∧ p1) → (p4 ∨ (((p5 ∨ ((p3 → (((p4 ∧ (p5 ∧ True)) ∧ p3) → True)) ∧ (p1 → p1))) → False) ∨ p1))) ∨ (p1 ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



