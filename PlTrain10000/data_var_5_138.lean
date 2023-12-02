variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300795885333298052322504232528 : (False ∨ ((p1 ∨ ((p3 ∧ (p2 ∧ (p3 ∨ ((p2 ∨ (p4 ∧ p1)) ∨ p3)))) ∨ (p1 ∧ p2))) ∨ (p1 → (True ∨ (p3 ∧ (p4 ∧ (p2 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185742254820111970962984754643 : ((p3 → (((p5 → p4) ∧ p4) → ((False ∧ (False ∧ p5)) ∧ p2))) ∨ (((p4 ∨ (True → ((False ∨ p4) ∧ True))) ∨ (p4 ∧ p3)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197296035474476691557133376530 : ((((p2 ∨ (p5 → False)) → (False ∧ True)) → p3) ∨ ((p3 ∧ ((((p5 → False) ∨ (True ∨ (False → True))) → True) → (p4 → (p5 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820609175112150310851782410397 : ((((((p2 ∧ (((((p5 ∨ p1) ∧ False) ∨ (p2 ∧ p1)) ∨ ((p1 → True) ∨ p5)) ∨ p4)) ∨ p1) → (((p5 → False) ∨ p5) ∧ p1)) ∧ p2) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ (((((p5 ∨ p1) ∧ False) ∨ (p2 ∧ p1)) ∨ ((p1 → True) ∨ p5)) ∨ p4)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244376478758250927853767270095 : ((False ∧ p1) ∨ (((p4 → ((p3 ∨ ((p3 ∨ True) ∨ ((False ∧ p4) ∧ True))) ∨ (((False ∧ (p1 → p5)) ∨ True) ∧ (p4 → True)))) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p3 ∨ ((p3 ∨ True) ∨ ((False ∧ p4) ∧ True))) ∨ (((False ∧ (p1 → p5)) ∨ True) ∧ (p4 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247823271961719982868659939329 : ((p1 ∨ p1) ∨ (p3 → (((False ∨ p5) ∧ (p1 → ((p1 ∧ p3) → True))) ∨ ((p5 → ((((p4 → False) ∧ False) ∨ (p4 ∧ p2)) ∨ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229700984155518602048362702264 : ((p4 → (False ∧ False)) ∨ (((p5 ∨ p3) ∨ True) ∧ ((p2 ∧ p2) ∨ ((p3 → p3) ∨ ((p5 → (p5 ∧ True)) ∨ ((p4 → p4) ∧ (p4 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210395259680718271134534563619 : (((p1 ∨ (p3 ∨ True)) ∨ p1) ∧ ((p3 ∨ (True ∧ True)) ∧ (((True ∨ (p5 ∨ p3)) ∧ (p2 → (p1 ∨ (p4 ∨ (p3 ∨ True))))) ∨ (p1 ∧ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174408880611548585172988549270 : (((((p2 → (True → (p4 ∧ p3))) → p5) → False) ∨ (p5 ∨ ((p2 → p1) → True))) → (False ∨ ((p5 → (True → p2)) ∨ (p3 → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731100732492638541173969760400 : ((((p1 ∨ (p1 → p4)) → (((True ∨ (p3 ∨ (p1 → p3))) ∧ p4) ∨ ((((p4 → True) → (p2 ∨ p4)) → p5) ∨ (p5 → (p5 ∨ p4))))) ∨ p5) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1783512215981047051272467897 : ((((True ∧ (((((True ∨ p1) ∧ True) ∧ ((p5 → p5) ∧ p4)) → True) ∨ p3)) ∨ p3) → (p3 → (p3 → p1))) ∨ ((True ∨ p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232058769814340455188782670203 : (((p4 ∨ True) → p2) → ((p1 → p3) → (False ∨ ((p4 → (p3 → (p1 ∨ ((p2 → False) ∨ p2)))) ∨ (((True → True) → (p2 → False)) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309809461016043733197829011271 : (p2 ∨ (((p1 ∨ p3) → (((p1 → p3) ∧ (p5 ∧ p5)) ∧ (False ∨ ((p2 → p4) ∧ ((p4 → p4) → p3))))) ∨ ((p4 ∨ p3) → (False → p5)))) := by
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
theorem thm_5_vars_192629023444699332305859677716 : ((((((p2 ∧ True) ∨ (p1 → p2)) ∧ p2) ∨ True) → False) → ((p2 ∨ p5) → (False ∧ (((p4 ∧ p1) → p2) → ((False ∧ True) ∨ (p5 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((((p2 ∧ True) ∨ (p1 → p2)) ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : ((((p2 ∧ True) ∨ (p1 → p2)) ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : ((((p2 ∧ True) ∨ (p1 → p2)) ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h13
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679969821175700474384333516197 : ((((((((p2 → p4) ∨ p1) ∧ (p4 → (p2 ∨ (True ∧ p5)))) → (True ∨ (p3 ∧ (p4 ∨ p3)))) → p5) → (True ∧ (p2 → (False ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53086593943369565711742461117 : (((False ∨ ((p2 ∧ (p1 → (False → p4))) ∨ ((p3 → p1) → p1))) ∧ (((((p3 ∨ p4) → p5) ∨ (False → p4)) ∨ (p5 ∨ p5)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234069808035320935447916474951 : ((True → (False ∧ False)) → ((p5 ∨ (((False ∨ ((p1 ∧ p5) ∨ p2)) ∧ (p3 ∨ (False → (p2 ∧ (p2 ∨ p3))))) ∨ (True → (p1 ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116540753678132462342526368994 : (((False ∨ p1) ∧ (((True ∧ (p1 ∨ (True ∧ ((p1 ∧ True) → (p4 → (p3 ∨ p3)))))) ∨ ((p3 ∧ p1) ∧ p3)) ∧ (False → False))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614674268060457142692301465409 : ((((((p5 ∨ (p4 → (p5 ∨ (((p5 ∨ (p5 ∨ (True ∨ p4))) ∧ (p1 ∧ p5)) ∨ p2)))) ∧ p5) ∨ (True ∧ (p5 ∧ (p4 → False)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_173571250566182858077908914476 : ((((False ∨ p2) ∨ ((((p2 ∧ (p5 ∨ (p4 ∨ p3))) ∨ p1) ∧ p2) ∨ p2)) ∧ True) → (p5 ∨ ((p3 ∧ True) → ((p2 ∨ p1) ∨ (p5 ∨ p4))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616167199649054744809403843278 : (((((((p3 ∧ True) ∧ p4) ∧ (((False → p2) ∧ (p5 ∨ p1)) → p1)) ∧ ((p1 ∧ p2) ∧ ((True ∨ p2) ∧ (p3 ∨ (p3 → True))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_833435079394174889518272203202 : ((((((((((True → p3) ∧ p5) → p3) ∧ p1) → (False ∧ ((p3 ∨ (p1 ∨ p2)) → p5))) ∧ ((p3 ∨ True) ∧ (p1 ∨ True))) ∧ p1) ∨ p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : ((((True → p3) ∧ p5) → p3) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h11
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : ((((True → p3) ∧ p5) → p3) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h18
        -- We need to get the left conjuct of h22 based on <expert-advice>.
        let h23 := h22.left
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h25 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h26 : ((((True → p3) ∧ p5) → p3) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h27
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h31 := h28 h30
          -- One of the premise coincides with the conclusion.
          exact h31
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h32 := h5 h26
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h35 : ((((True → p3) ∧ p5) → p3) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h36
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h39 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h40 := h37 h39
          -- One of the premise coincides with the conclusion.
          exact h40
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h41 := h5 h35
        -- We need to get the left conjuct of h41 based on <expert-advice>.
        let h42 := h41.left
        -- False on the left can always be used.
        apply False.elim h42
  case inr h43 =>
    -- One of the premise coincides with the conclusion.
    exact h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58903864576659147576281361667 : (((False ∧ p5) ∨ ((p2 ∨ False) → (((True ∧ p1) ∨ (((p1 ∧ (((p5 ∨ p5) ∨ (p1 ∧ p5)) → (p5 ∨ p3))) ∧ p3) ∧ p1)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624928784337571311453545739525 : ((((p5 ∨ ((p2 ∨ p3) ∨ (False ∨ ((p4 → p4) ∧ ((p5 → p2) → ((False ∨ (True ∧ (p5 ∧ p1))) → (p1 → (False ∧ p2)))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_135363097164180815174868052682 : (((p3 → ((True → (((False ∨ (p1 ∨ p1)) ∨ (p1 → (p1 ∨ p4))) ∧ p2)) ∧ (p3 ∧ True))) ∧ (p5 ∨ (p3 → p4))) ∨ (p4 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44853123990386511679826652531 : ((((p2 ∧ (p4 ∧ p3)) ∨ (((True → (p1 → (p2 ∨ p5))) → (p3 ∨ p4)) → (p5 → (((p2 → p3) ∧ (p4 → False)) ∧ p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52584101343932978118087416933 : (((((p2 ∨ p4) ∧ (p2 ∨ (p1 ∨ (p1 ∨ False)))) ∧ ((True → True) ∨ p1)) ∨ (((p4 ∧ p5) ∧ (p5 ∧ ((p1 ∨ True) → p3))) → p4)) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260458850713507115860298066217 : ((p3 → False) → ((((True ∨ (p5 ∧ p4)) → (((p4 ∨ p1) ∨ p1) ∨ ((((p2 ∧ (p4 ∨ p1)) → p4) → False) → p3))) ∨ (False → p4)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639478962429535425102036579476 : ((((((p2 ∨ p1) ∧ p5) ∧ (((((((p2 → True) ∨ (False ∨ p4)) ∧ p5) → (True ∨ p5)) ∧ (p3 ∧ p1)) ∨ False) → (p5 ∧ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315115418644013373369482581383 : (p3 ∨ (((((p2 ∧ p2) ∧ p1) → p5) → p2) ∨ ((((p2 ∧ (p1 ∧ (((p3 → True) → True) → True))) ∨ p3) ∧ p1) ∨ (False → (p2 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174665099949206380715644802125 : (((p3 ∧ (True → True)) ∧ (((p5 ∨ ((p4 → p5) ∨ (p3 → p4))) → True) → False)) → (((p2 ∧ p1) ∧ p2) ∨ (p3 ∧ ((p2 ∧ p1) ∨ p3)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157408849991208800900309327065 : ((((((p3 → p4) → True) → (False ∨ ((p1 ∨ True) ∧ p2))) → ((p2 → p3) ∧ p4)) ∧ (p4 ∧ p2)) ∨ (p3 ∨ (p5 → ((False ∨ p3) → p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654526260707728488592037972426 : (((((p4 ∧ (((p5 ∨ p1) → ((False → True) → (((p1 ∧ (False ∧ p5)) ∨ False) ∨ ((p3 ∧ True) → p5)))) ∧ False)) ∨ p5) ∨ (True ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713209297163334294039613228836 : ((((p2 ∨ ((p2 ∨ (True → p4)) ∨ p3)) ∨ ((p5 ∧ ((p4 ∨ (p2 ∨ p1)) ∧ (p1 ∧ (p2 ∧ p3)))) → (False ∨ ((p1 ∧ True) → p3)))) ∨ p4) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h5.left
      let h25 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48989037052233665207797956674 : (((((True → False) ∨ (((p3 → (False → (p2 → p4))) → (((True → p2) ∨ p1) ∧ p2)) ∧ (p1 ∧ p2))) ∨ p4) ∨ ((p4 → p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231868198082038396353215298243 : (((True ∨ False) → p3) → ((p5 ∨ ((True ∨ p5) → (((False ∧ p3) ∨ p4) ∨ (True → p3)))) ∨ ((p4 → ((p3 ∧ (p5 ∧ p1)) ∧ p5)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43358654903860436616319663785 : ((((((p1 ∨ ((p4 ∧ ((p1 → ((p1 ∧ True) ∧ True)) → p3)) → ((p2 ∧ False) ∧ (False → p2)))) ∨ p4) ∨ (p2 ∧ False)) ∨ p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670696040629146212633132296487 : (((((p5 → False) → (p2 ∧ (((p4 → p3) ∧ ((((True ∨ p1) ∨ True) ∧ (False → p2)) ∧ (p2 → p1))) ∧ p1))) ∨ (False → (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111909574338103375141482598405 : ((((((p1 ∨ p3) ∨ p3) ∧ (((False ∧ p5) ∧ (p2 ∧ True)) → p5)) ∧ (p5 ∨ ((p3 ∨ ((p2 ∧ p1) → p1)) ∧ p4))) ∨ True) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191828444555411567908920907689 : ((p3 ∨ ((((False ∨ p2) ∨ p4) ∨ (p2 ∧ False)) ∨ p1)) ∨ (((((False → False) ∨ p5) ∧ (p3 ∨ True)) ∨ (((False ∨ p2) ∨ p3) ∧ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354600908565969505753202460631 : (p5 → ((((((True ∧ (False ∨ (p1 ∧ True))) ∧ (((False → p3) → ((False ∨ p3) ∨ (p2 ∧ (p3 ∨ False)))) ∨ p3)) ∧ p3) ∨ p2) ∨ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53814994724302525978975583754 : (((((p4 → False) ∨ (p1 → (p3 ∧ p2))) ∧ (p3 ∨ True)) ∨ (((((True → p5) ∨ p4) ∨ False) ∧ ((p2 ∧ p5) → (p1 ∨ p4))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172473779014015492084780811901 : (((((True ∧ False) → p1) ∨ p5) → (p2 → (((p1 → p3) ∧ (p4 ∨ p4)) ∨ p2))) ∨ ((False → False) ∧ ((p5 ∧ p1) ∧ ((p2 ∧ p3) → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654830125534911815636379908830 : (((((((p4 → (p3 ∨ ((p3 ∨ True) ∨ ((True → p5) ∨ p2)))) ∧ ((False → p1) ∧ (False ∨ p3))) → (p3 ∨ p5)) → False) ∨ (True ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_38088829866338116686947665308 : ((((p5 ∧ (((((True ∨ (False ∨ (p3 → (p3 ∧ p4)))) → p4) ∧ p3) → p2) ∧ ((p4 → (p5 → p2)) ∧ p5))) → (p3 → p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264210770025480398995770591947 : (True ∧ ((p5 ∨ (p1 → (((True → p2) ∧ p3) ∧ p3))) → ((((p1 ∧ (p3 → p1)) → False) ∧ (p2 ∨ ((p1 ∨ p3) → True))) → (p1 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∧ (p3 → p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h9
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : (p1 ∧ (p3 → p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227684772726697435331729101079 : ((False ∧ (p5 → p3)) ∨ ((p1 ∧ p5) → (True ∧ ((p1 → ((p5 → p2) → (False ∨ (True → ((p1 ∨ True) ∧ (p4 ∧ (False ∧ True))))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50290128899865908392837536017 : (((((p2 ∧ (p3 ∧ ((p2 ∧ (False ∧ (p2 ∧ p3))) → (p3 → True)))) ∨ False) ∧ (p3 ∧ (p2 ∨ p5))) ∨ ((p3 ∨ p4) → (p2 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257595013964454885583652893063 : ((p3 ∨ p1) → (p3 ∨ ((((p4 → (False ∨ p4)) → False) ∧ ((p2 ∧ (p2 ∧ (p4 → ((p5 ∧ True) → False)))) ∧ True)) ∨ (p1 → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67777399669088040357229186070 : ((p2 → ((p4 ∧ ((p3 ∧ (True → (p5 → (p3 → ((p4 ∨ p4) ∧ p2))))) ∧ (((False ∨ (True ∨ p2)) ∨ True) ∨ (True → p5)))) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167288732696252657876271663280 : ((((p2 ∧ ((True ∧ False) ∨ (((p4 ∨ (True ∧ p4)) ∨ (True → p4)) ∧ True))) ∨ True) → p2) → (((True ∧ p5) ∨ ((p1 → p1) → p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ ((True ∧ False) ∨ (((p4 ∨ (True ∧ p4)) ∨ (True → p4)) ∧ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8979491341019834688015120193 : ((((((p3 ∨ p5) ∧ (p3 ∨ ((True → p4) ∧ p4))) ∨ ((p1 ∨ p2) → (p3 ∨ True))) ∨ ((False ∨ (p2 ∨ True)) → (p4 ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697978799255753365578536731234 : (((((p5 → ((p2 ∨ (p5 ∧ p3)) ∨ ((False → p1) → False))) ∧ p1) ∨ ((True ∨ (((True ∨ ((False → True) ∨ p1)) ∨ p1) ∨ p1)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626552339979691900335939447552 : ((((p4 → ((p2 → ((p4 ∨ p2) → p2)) ∧ (p3 → (p2 ∨ ((False ∨ True) ∧ ((p3 ∧ False) ∧ ((p5 ∨ (False ∨ p4)) ∨ p3))))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697107739325450884050774422352 : (((((((p3 → p3) → p3) ∨ p3) ∨ ((False ∨ (True ∧ p1)) ∨ False)) ∧ (False → (((p2 ∧ p4) ∨ p3) ∧ (((p4 ∨ True) → p4) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55650772438059551782074750390 : (((((p1 → p5) → p3) ∧ p2) ∧ (((p5 ∧ p5) ∨ (((p1 ∨ p2) ∨ p4) → (False ∧ p3))) ∨ ((p2 ∨ True) → (p4 → (p3 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37443270204841452086165879359 : ((((((p3 ∧ (p4 ∨ p4)) ∧ ((p1 ∨ p2) → (p1 ∨ ((False ∧ p5) ∨ p3)))) ∧ (p4 ∨ (True → ((True ∨ True) → p2)))) ∨ p2) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330498545452970188374613727049 : (True → (p4 ∨ ((((((False ∨ p5) ∧ p1) ∨ (p2 → (p3 → p2))) ∧ (p2 ∨ p4)) ∨ True) ∧ (p3 → ((p5 → (p4 ∨ p3)) ∨ (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593769142684645019630941629310 : (((((p1 ∧ (((True ∨ (True ∨ (p2 ∧ True))) → ((p1 ∨ False) ∧ p4)) ∨ ((p4 ∧ True) ∧ p1))) ∧ (False ∧ ((p4 ∧ p4) → p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115124348184132733490829162866 : ((((p1 ∧ (p5 → (p3 → (p4 ∨ p1)))) ∨ ((p4 ∧ True) ∨ p4)) → ((p2 → p5) ∨ (p4 → ((p5 ∧ (False → p3)) → True)))) ∨ (p3 ∨ p4)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
theorem thm_5_vars_265059637063137593128562652717 : (True ∧ (True ∧ ((False → p1) ∧ (((((False ∧ (p2 ∧ p3)) → p1) ∧ p2) ∧ (p5 ∧ (((p5 ∨ (p3 → False)) ∨ False) ∧ (p5 ∨ p3)))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228714765776210196319614870806 : ((p2 ∨ (True → p4)) ∨ (p5 ∨ (((p4 → ((p2 ∨ p3) ∧ (p5 → True))) ∧ ((True → ((p1 → (False ∧ False)) ∧ False)) ∨ (p1 ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113171693005283507521632669705 : (((p5 → ((p2 ∧ p5) ∧ ((((False → False) ∨ (p1 ∨ p2)) → (p1 ∧ p4)) → ((p3 → p1) ∨ ((p5 ∨ p1) ∨ p3))))) → p2) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596218217323584645964775771583 : (((((((p4 → p3) ∨ p1) ∨ (True ∧ (p3 ∨ False))) ∧ ((p5 → ((p1 ∧ p3) ∨ ((p5 → p1) ∨ True))) → ((p4 ∨ p4) ∨ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300102399221716793617244842504 : (False ∨ ((((p1 → (((False → False) → p4) ∧ ((p5 ∨ p3) ∨ (p4 → False)))) → p5) ∨ ((True → p5) → (p5 ∨ (p4 ∧ p3)))) ∨ (False ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141130751805718654209702463518 : (((((True ∨ p1) → (False ∧ True)) ∧ True) ∧ (((p2 → False) ∨ p2) → (p2 → (True ∧ (p3 ∨ (True → (p3 ∧ p5))))))) → (p4 → (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46882625903648643379726471128 : (((((p4 ∧ ((p2 ∧ (p2 ∨ (p3 ∨ (False ∧ (p2 ∧ (((False ∨ p2) ∧ (True → p2)) ∧ True)))))) ∧ p2)) ∧ p4) ∨ True) ∨ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47131981892661007093515105888 : ((((p1 ∨ ((((p3 ∨ (p1 ∨ p2)) ∨ p4) ∨ ((p5 ∧ p5) ∧ ((p1 ∨ p1) → p4))) ∨ p1)) → (False ∧ (True → True))) ∨ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152399818419474585074952772283 : ((((p2 ∧ p5) ∨ (False → True)) → ((p4 ∨ False) ∨ ((p2 ∧ p1) ∨ ((p1 ∨ p3) ∧ (p4 ∧ (p3 ∨ p1)))))) → ((p1 → (p2 ∨ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p5) ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h15.left
        let h23 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199297116945294793658260443335 : ((((((p1 → True) ∧ p2) ∨ p5) ∨ p2) ∨ True) → ((p1 → ((p2 ∧ p4) ∨ p5)) ∨ (False ∨ ((((p4 ∨ (p3 → False)) ∧ p2) ∧ p2) → p2)))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h31 =>
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649724308782512634871679398178 : ((((((((p3 ∨ False) ∧ False) ∨ (((((p4 ∧ ((p4 ∨ p3) → p5)) ∧ p3) → p2) ∨ p5) → p4)) ∨ p3) → (p4 ∨ False)) ∧ (p4 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214737317896085854837873058547 : (((p3 ∧ p2) ∨ (p1 ∨ p4)) ∨ (p1 → ((((((p2 ∨ p2) ∨ (True → (p1 ∧ (True ∧ p4)))) ∨ True) → (p5 → False)) ∨ True) ∧ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64805095480172627462489135984 : ((p2 ∨ ((p4 ∨ ((((p3 → False) ∨ (p5 ∧ p5)) → ((False ∨ ((p1 ∧ p1) ∧ p1)) → (((p3 ∧ p2) → p4) ∧ p3))) ∧ p2)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1874879650402832738917390296 : ((p3 ∧ (((p5 ∧ (p5 ∧ False)) → p1) ∨ ((True ∨ (p2 ∨ ((p3 ∧ False) → (False → (p1 → p4))))) ∧ p2))) → ((p1 → p2) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57868800823848602995753281457 : (((p1 ∨ (False ∧ p3)) → (((False ∨ p5) ∧ ((p3 ∨ (False → p3)) → False)) ∨ (False → ((p5 ∨ p4) → (p4 ∧ ((p4 ∧ True) ∧ p2)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47342035576319697139037712815 : ((((p4 ∨ True) ∧ ((((p1 ∧ (p4 ∨ (((p2 ∧ (p3 ∨ p2)) → (p3 ∨ p1)) ∨ False))) ∨ p2) ∨ True) → (False ∨ True))) ∨ (p1 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152307099167809322256293997403 : (((((True → False) ∧ True) ∨ False) ∧ (p4 → ((p2 ∨ ((p1 → p5) ∧ ((p3 ∧ (p3 ∨ p3)) ∨ p3))) → p3))) → (p3 → ((True ∧ False) ∨ p4))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117121184798956210672389424348 : (((p3 → p5) → (p1 → (p3 ∨ ((p4 ∧ (p2 → p4)) ∨ (((((False ∨ p1) → (p1 ∨ p1)) ∨ p5) → (p1 ∨ p4)) ∨ p5))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148579179504853468242945112298 : (((((((p1 ∧ False) ∨ p2) ∨ (p1 ∧ p3)) → p4) ∨ p4) ∨ ((p3 ∧ p5) ∧ (((True ∧ p2) ∨ p3) ∨ p5))) ∨ (((p1 ∨ False) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350151468212951350270686426457 : (p4 → (((((False ∨ (p2 ∧ p3)) ∧ p5) ∧ ((p3 ∧ True) → p3)) ∨ (False ∨ ((((p5 ∨ (False ∨ (True ∨ p5))) ∧ False) → p5) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174025207363413080480924190972 : (((True ∨ (p3 ∨ ((((p1 ∧ (p4 → p4)) → p4) ∧ p4) ∧ (False ∨ p2)))) → False) → ((p3 ∧ (p4 ∧ ((p5 ∧ p2) ∧ p4))) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p3 ∨ ((((p1 ∧ (p4 → p4)) → p4) ∧ p4) ∧ (False ∨ p2)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183949565968098232699945509773 : (((p4 ∨ ((True → ((p5 ∨ p4) ∨ (False ∨ p4))) ∧ True)) ∧ True) ∨ (((True ∨ p3) ∨ p4) ∧ (((p3 → p4) ∨ (True ∧ False)) → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234297086739306824578864542141 : ((False → (p5 → p3)) → (((((p4 ∧ p2) → p5) ∨ ((p1 ∨ ((((False ∨ (p1 → False)) ∧ p1) ∧ p3) → p4)) ∨ (False ∧ True))) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158488993346877055526574248777 : (((p2 ∧ True) → (((p4 ∨ ((p4 ∧ ((p4 ∧ (p3 ∨ p1)) ∧ True)) ∧ p1)) ∧ p5) ∨ (True ∧ True))) ∨ ((((True ∨ True) ∧ p3) ∨ p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669358806796299258097864244175 : (((((p4 ∧ (((((p4 → p3) ∨ (False ∨ p2)) → (p5 ∧ True)) → p3) ∨ (p5 ∨ (p4 ∨ p5)))) ∧ (p3 → p4)) ∨ ((p2 → False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113254758657860600562948465040 : ((((((p5 ∧ (((p1 ∨ (p5 ∧ p4)) ∨ (p4 → ((p5 ∧ p2) ∧ True))) ∧ False)) ∧ p2) → True) → (True ∧ False)) ∧ (p5 ∧ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165495612758832181010887239765 : (((False ∧ (True ∧ ((p3 ∧ ((p4 → True) → p2)) ∧ p5))) ∨ ((p5 ∨ True) ∨ (p2 ∨ p4))) ∨ (((p5 ∧ ((p3 ∧ True) ∨ p2)) ∨ p3) → p2)) := by
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
theorem thm_5_vars_647094455384413736741976971827 : ((((p3 → ((False → (p1 → (((p5 ∨ True) ∧ p1) → p5))) ∨ ((p3 ∧ ((((False → False) ∨ p5) → (p2 ∧ p2)) ∨ p4)) ∨ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78796682462716352960573984065 : (((((p4 ∨ p1) ∨ (p3 → (p2 ∨ p4))) → ((p1 ∧ True) ∧ (False ∧ (p2 → ((True → (p4 → (True ∧ p3))) → False))))) ∧ (p1 ∨ p1)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∨ p1) ∨ (p3 → (p2 ∨ p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∨ p1) ∨ (p3 → (p2 ∨ p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64526550419421724542683815236 : ((p1 ∨ (((p4 → False) → (p3 ∧ (p4 ∨ ((True ∨ True) ∧ p1)))) → (False ∧ ((p5 ∧ False) ∨ (p1 ∧ (p4 ∨ ((True ∧ p3) ∨ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801803914807673899371229562744 : (((p2 → (((p3 ∨ p3) → p4) → (False ∧ (p4 ∨ (((False ∧ ((False → p4) ∨ p1)) ∧ (p5 ∨ ((True → p5) ∨ (p1 ∨ p3)))) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38433885680318817837433119415 : ((((((((False → p4) ∧ p4) → (p4 → p2)) → (p2 → p3)) ∨ (p5 ∧ False)) ∨ ((False → p1) ∨ ((False ∧ (p1 ∧ p2)) → False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44622233230170718751926474289 : ((((((False ∨ (p2 ∧ p1)) → p2) → p1) ∧ ((((False ∨ True) → (p3 ∨ (p2 ∧ False))) ∧ ((False → p4) ∨ False)) ∨ (p4 ∧ p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38215104583671271765799741521 : (((((((p3 ∧ True) → p1) ∨ p4) ∧ ((((((p3 → False) ∨ p4) ∧ (p5 ∧ False)) → p3) → p5) ∨ p3)) → (p3 ∨ (p5 ∧ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137703121689547517588962389918 : ((p1 ∨ ((p4 → (True ∧ ((((p3 ∧ p2) → (p4 → (p2 → False))) ∧ True) → (p5 ∨ p3)))) → ((True → p2) ∧ p1))) ∨ (p3 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53320308216049069040284749317 : (((p3 → (((((False ∨ False) ∧ p2) → (False ∨ p3)) ∧ p5) ∨ p5)) ∨ (p1 ∨ ((True ∧ (p2 ∧ p3)) ∨ (((p5 ∨ p1) → True) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725770668864159676715584788560 : (((((p3 ∨ True) ∧ p5) ∨ ((False ∧ p3) ∧ ((False ∨ (((p1 → (p1 ∨ True)) ∨ p2) ∧ True)) ∧ ((p2 ∧ True) → (p3 ∨ (p4 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142454919784914102442043436177 : ((p5 ∧ ((p1 ∨ (((p1 ∧ ((p5 ∧ False) ∧ ((p4 → True) → p4))) ∧ ((p4 ∨ (p5 ∧ p1)) ∨ False)) → p4)) → p4)) → (p4 ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ (((p1 ∧ ((p5 ∧ False) ∧ ((p4 → True) → p4))) ∧ ((p4 ∨ (p5 ∧ p1)) ∨ False)) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147521136921742181855699632871 : (((p5 ∨ (((p1 ∨ ((p3 ∨ p4) ∨ False)) → ((p3 → (p5 ∧ True)) ∨ False)) ∨ ((p5 ∧ p2) ∧ False))) ∨ True) ∨ (((p2 ∧ p4) ∨ p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695682107023743129170076139202 : (((((True ∨ ((p1 ∧ p4) → True)) ∧ ((p3 ∨ p2) ∧ (False → (p4 ∨ p4)))) → (((p5 → p4) ∧ ((p2 → p3) → (p5 ∨ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



