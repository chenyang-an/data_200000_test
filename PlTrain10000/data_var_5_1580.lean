variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191023766056423044006888113594 : (((((p3 → p4) ∧ p1) ∧ p5) → (False ∧ (p2 ∧ p3))) ∨ (p1 ∨ (((p4 → (True ∧ True)) ∧ True) ∨ (((True ∨ p4) ∧ (True ∧ p5)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55979335198123848237566499401 : ((((True ∧ (p1 ∧ p1)) ∧ p1) ∨ (((((p2 ∧ (p4 → p3)) ∧ p1) → p5) → (True → ((True ∧ (p4 ∧ (True → p2))) → False))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_515017095074276557006739637506 : ((((p5 ∨ p4) ∨ (((p5 → p2) → (((False → (True ∨ False)) ∧ ((p5 ∨ p3) ∨ p2)) → (p2 ∧ True))) ∨ (((p1 ∧ p2) → p1) ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255256435972688935154845769300 : ((p4 ∧ p5) → (((p3 → (False ∧ True)) → ((((True ∨ p2) → p5) ∧ p2) ∨ ((p1 ∨ ((p5 ∨ p2) → False)) ∨ p5))) ∧ ((False ∧ p2) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1939531646932756618217195125 : (((p1 ∧ (((p5 → True) → ((((p4 ∧ (False ∨ False)) ∧ True) → p4) ∧ p5)) ∧ (p1 → p5))) ∧ p1) ∨ (p1 → ((p2 ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56777645655654352490043462606 : ((((p2 ∧ False) → p2) ∧ (True → (((((p5 ∧ (p5 ∧ (p3 → (p5 ∨ p2)))) ∨ p1) → p3) → p5) ∧ ((p3 → p2) ∨ (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31544361361081046904380240426 : ((False ∨ ((((p1 ∧ False) → p4) → (((p3 ∨ p2) ∧ p2) → (((((p1 ∧ p5) ∧ p4) ∨ (p5 → False)) ∧ (False ∧ p5)) ∨ p2))) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115598803746591628141016190479 : (((True ∧ (True → (False ∨ (True ∨ p1)))) ∧ ((((True ∨ (True ∨ p4)) ∧ (p1 → (p3 ∧ False))) ∧ p2) → ((p1 → False) ∨ p2))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157552508645151031826768378227 : ((((((p5 ∨ p4) → (((p2 ∧ p1) ∨ (False → p3)) → p3)) ∧ p4) ∨ (True → p4)) → (True ∧ False)) ∨ (((p4 ∧ (False ∧ False)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664241246036833423226767535183 : ((((p1 ∨ (((p3 ∨ (((False → (p3 ∨ p4)) → True) ∨ (False ∨ (p2 ∨ p5)))) ∨ p5) ∨ (((True ∨ p1) ∧ p3) ∧ p4))) → (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147245426246618537265944675909 : ((((((p2 ∨ (p4 ∧ False)) ∧ p2) → ((p4 ∧ ((((p4 ∨ p5) ∨ p5) ∧ p3) ∧ False)) ∨ p5)) ∧ p2) ∨ p1) ∨ (True ∨ ((p4 ∧ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40266661661844784949468027594 : ((((p4 ∨ ((p1 → p4) ∨ ((((False → (p1 ∧ (True ∧ p1))) → (False → (p4 ∨ (p1 ∧ (True → p1))))) ∨ p1) ∧ False))) ∧ False) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157176322388273255671449525715 : (((((((True ∨ p5) → ((p4 → False) ∧ p4)) ∨ p3) ∧ (p4 → ((p2 → True) ∧ False))) → p5) → p5) ∨ ((p4 ∨ (p1 → p2)) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58344001751386346463661231486 : (((False ∨ p4) ∧ ((((((True → p2) ∧ p2) → p2) ∧ (p2 ∨ p2)) → (True ∧ ((((True ∧ p5) ∧ (p5 ∨ p5)) ∨ p5) ∨ p2))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172306149267276860740919841315 : ((((True → (p5 → p2)) → (False → (True ∨ p1))) → (p2 → ((p1 ∧ p1) ∨ False))) ∨ ((p4 → (p2 → (((True ∨ p1) → p2) → p4))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715080380824659532792946802700 : ((((p3 ∨ ((p4 ∨ p2) ∨ (False ∨ True))) → (((((((p4 ∨ True) ∨ (p4 ∧ p2)) → p1) → (False ∨ (p4 → p1))) → p3) ∨ p3) → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h8 : ((((p4 ∨ True) ∨ (p4 ∧ p2)) → p1) → (False ∨ (p4 → p1))) := by
            -- Implications on the right can always be decomposed.
            intro h9
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h11 : ((p4 ∨ True) ∨ (p4 ∧ p2)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h12 := h9 h11
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h13 := h3 h8
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h15 : ((((p4 ∨ True) ∨ (p4 ∧ p2)) → p1) → (False ∨ (p4 → p1))) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h18 : ((p4 ∨ True) ∨ (p4 ∧ p2)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h17
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h19 := h16 h18
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h15
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : ((((p4 ∨ True) ∨ (p4 ∧ p2)) → p1) → (False ∨ (p4 → p1))) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
            have h27 : ((p4 ∨ True) ∨ (p4 ∧ p2)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h26
            -- We have shown the premise of h25, we can now drive its conclusion.
            let h28 := h25 h27
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h29 := h3 h24
          -- One of the premise coincides with the conclusion.
          exact h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h31 =>
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h35 =>
          -- One of the premise coincides with the conclusion.
          exact h30
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56706408695575621315697196049 : ((((p3 ∧ p4) ∨ p4) ∧ (p2 ∧ (False ∧ ((p3 ∨ (p2 ∨ ((p1 ∧ (p5 ∧ (True ∨ p2))) → ((p1 ∨ p1) → (False ∨ p2))))) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597096044920019357268870141849 : (((((p5 ∧ (p3 ∧ ((p2 → p5) ∨ p5))) → (((((False ∨ (False ∨ False)) ∧ (p5 → p2)) ∨ p5) ∧ True) ∧ ((True ∧ p4) ∨ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199080534428101955821143412070 : (((((p5 → True) → (True ∧ p1)) → True) ∧ p5) → (((True → ((p1 ∧ p2) ∧ p1)) ∨ p3) → ((True → (True ∧ (False ∧ p2))) → (p2 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h22 := h3 h21
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h29 := h3 h28
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- We need to get the left conjuct of h30 based on <expert-advice>.
    let h31 := h30.left
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716649349192091813134782836803 : (((((True ∨ False) → (True ∨ p4)) ∧ (((p3 → ((((p2 → p3) ∨ p3) ∧ (True → True)) ∨ False)) → p1) ∧ ((p1 → p4) ∨ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179052158264168590365234952819 : (((p4 → True) → (((p5 ∨ (p3 → (p4 → p3))) ∨ False) ∧ (p1 ∧ p5))) ∨ (p1 → ((((True ∨ p1) ∧ (p2 → True)) ∨ p4) ∨ (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615625571812291277757470046236 : (((((((((p4 ∨ False) → False) ∨ ((p3 ∨ p3) ∨ (False ∧ p2))) → p2) ∧ p2) ∧ (p4 ∨ (p4 → ((False ∧ p1) ∧ (False ∧ p5))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_769502210654501999295959091789 : (((p5 ∧ (p3 ∧ ((((p1 ∨ (True ∧ (True ∧ (True → (True → p5))))) ∧ True) ∨ (p5 ∨ p3)) ∨ (True ∨ ((False ∨ False) ∨ (False → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726240930105132894610057752125 : (((((False ∨ p1) ∨ p5) ∨ ((False ∨ False) ∨ (((((p1 ∧ p4) → (p2 → p3)) ∧ p5) → p2) → (p1 ∧ (p4 → (p5 ∧ (p4 → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149994187274112035915250761753 : ((p4 ∨ (p5 ∨ (False ∧ ((p5 ∨ ((True → p5) ∧ (p5 ∧ p4))) ∨ (((False ∧ p2) ∨ False) ∨ (p1 ∧ p5)))))) ∨ (p1 → ((p1 → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358036950437295245594393836143 : (p5 → (p1 ∨ ((p4 ∧ ((p2 ∧ ((p5 ∧ (p4 ∨ (p5 ∨ False))) ∨ p4)) → (((p1 → False) ∨ ((True ∧ False) ∧ p2)) ∧ (p5 → p2)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116821440240578428890407654271 : (((p4 ∨ p4) ∨ ((p5 → ((False ∨ p1) ∧ False)) ∧ (p1 ∨ ((p3 ∧ ((p2 ∧ p5) → True)) ∨ (p3 ∨ ((True ∨ True) ∨ p1)))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659530833981843464159705747694 : ((((((((p2 → False) → (((p3 ∧ p1) → ((((p4 ∨ p2) ∧ False) → p2) → p5)) ∧ p4)) ∧ p1) → (True → p2)) ∧ p5) → (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166181169703379160966074140997 : ((p1 ∧ ((False ∨ ((p2 ∨ ((False ∨ (p3 ∨ True)) ∧ ((False ∧ p5) ∧ p4))) ∧ p1)) ∧ p5)) ∨ (p5 ∨ (True ∨ (((p4 → True) ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53825093642925673737024777673 : ((((p3 → (((False ∨ p4) ∧ False) ∨ False)) ∨ (p1 ∧ False)) ∨ (((p4 → (p5 ∨ (p3 → True))) ∧ ((p4 → (p5 ∧ p2)) → p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350990755251092466869707196784 : (p4 → ((False ∧ (p3 ∧ (((((False ∧ (p4 ∨ (p1 ∨ False))) → p4) → p3) ∧ p3) ∨ ((p3 ∨ False) → ((p1 → p3) → True))))) ∨ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134577933890732780532431828286 : ((((True → (((p5 ∨ False) ∨ p1) → (p1 → (((False ∨ (p4 → p2)) ∧ (False → p2)) → False)))) ∧ (p1 → p5)) → p4) ∨ (True ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825656542639985667805971027902 : (((((p1 → False) ∧ (p3 ∨ (((False → False) ∧ (p2 ∨ ((p4 ∧ (((True ∧ (p2 → p3)) → p5) ∧ p5)) → False))) → (p3 → p3)))) ∧ p1) → p3) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351009593575868163104070377494 : (p4 → ((p5 ∨ (False ∧ (p2 ∨ ((((p3 ∨ (True ∧ (((p2 ∨ p2) ∨ p2) ∧ p5))) ∨ ((p2 ∨ p5) → p5)) ∨ p1) ∨ p3)))) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241564371842929442776332032392 : ((False → p3) ∧ (p5 ∨ (p2 ∨ (p5 ∨ ((p2 ∧ p1) ∨ (p5 → ((p2 → p3) → (p5 ∧ (p1 → (p2 ∨ ((p4 → p2) → (p5 ∧ p5)))))))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111674712725147725128258061084 : ((((p4 → (((p2 ∧ ((((True ∧ False) ∨ False) → (p1 ∧ p3)) ∧ p5)) → (p1 ∨ (p3 → (p4 → False)))) ∧ False)) ∨ False) ∨ True) ∨ (False ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57313499470806835065082927227 : (((True ∧ (True → p3)) ∨ (((((p1 ∨ ((((p1 → p5) ∨ ((p3 → p3) ∨ p1)) ∨ p4) ∨ (False ∧ p4))) → p1) ∨ False) → p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778223120604993998147945309788 : (((p1 ∨ ((p4 ∨ p2) → ((((False ∧ (p5 ∨ p5)) → ((False → p4) → p2)) ∨ p4) → (p1 ∨ ((False → p3) ∨ (p3 ∨ (p4 ∧ True))))))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606709285654480247599443247255 : ((((((((p3 → p1) ∧ ((p2 ∨ p4) ∧ ((((False ∧ (p2 → p3)) → (p2 → p5)) → p2) ∧ p2))) ∧ p1) ∨ (p3 ∨ False)) ∧ p1) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60224208701686922142760002383 : (((True → p2) → (((((p4 → (p2 ∨ False)) → p4) ∨ p3) ∨ True) ∧ (True ∧ (p4 → (True → ((p4 ∧ (p4 ∨ (p3 → True))) ∨ p4)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118120258887413298804451931974 : ((False ∨ ((False → ((True ∨ (False ∧ (p1 ∧ p1))) → (False ∨ ((((True ∨ True) → False) ∧ ((p2 ∧ p5) ∨ p4)) → p5)))) → p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151155191823835739736430910992 : (((((p2 → (p2 ∧ (False ∧ p4))) ∧ (p4 ∧ (((p5 ∨ p5) ∧ p5) ∨ p4))) ∨ ((p5 ∨ p2) ∧ p1)) → True) → (((p1 → True) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206878833502398028656421403953 : ((((True ∨ (p5 → p3)) ∧ p2) ∧ p3) → (((p2 ∨ (((p2 → ((p3 ∨ ((True ∧ (False ∧ False)) → True)) ∨ p4)) ∧ p2) ∨ p3)) → False) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ (((p2 → ((p3 ∨ ((True ∧ (False ∧ False)) → True)) ∨ p4)) ∧ p2) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∨ (((p2 → ((p3 ∨ ((True ∧ (False ∧ False)) → True)) ∨ p4)) ∧ p2) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355991493091566024408494222885 : (p5 → (((p1 ∧ p3) ∨ ((p5 ∨ (((False ∧ ((p5 ∧ False) ∧ p4)) ∨ True) ∧ (True ∧ (p2 ∧ True)))) → True)) ∧ (False ∨ ((p2 ∨ p2) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102766791840071236519137914933 : ((((((p1 ∨ (p5 ∧ (((p5 ∨ p1) ∧ (p1 ∨ ((p4 ∨ p1) ∧ False))) ∨ False))) ∧ (p4 → (p1 ∨ p1))) → True) → p1) ∨ True) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299969080056911048381317572972 : (False ∨ ((((p2 → (True → (p3 ∧ (p5 ∨ (p4 ∧ True))))) ∨ (p5 ∧ (((p4 ∨ False) → p1) → (p4 ∨ p2)))) ∨ (True ∨ True)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46883498124333890906147835434 : (((((p5 ∨ (p5 ∨ (((((True ∧ (p2 → p3)) → p5) ∧ (True ∨ p1)) ∨ (p4 ∧ p5)) ∨ (p3 ∨ p2)))) ∧ False) ∨ True) ∨ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76286772056765023192127259297 : ((((((True → (False ∨ ((((False ∧ p5) ∧ True) ∨ (p1 → ((p5 → p4) → p1))) ∧ p3))) ∨ p2) ∨ (False → p2)) ∨ (p5 ∧ p3)) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → (False ∨ ((((False ∧ p5) ∧ True) ∨ (p1 → ((p5 → p4) → p1))) ∧ p3))) ∨ p2) ∨ (False → p2)) ∨ (p5 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671750654372551414615465841715 : (((((((p2 ∧ (((p3 → (p2 → (p1 → False))) → p2) → p5)) → p5) → (p2 ∧ (p4 ∨ (p4 ∧ p5)))) ∧ p5) → (p5 → (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134107707936889028337640105778 : ((((((p3 → (p4 ∨ ((p3 ∧ p4) ∧ (p2 → ((p5 ∨ p4) → p5))))) ∨ p5) ∨ (p4 ∧ p3)) ∧ (p1 ∨ True)) ∨ p3) ∨ (True ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157768743045136612783596228248 : (((p2 → ((p5 ∨ ((((p3 ∨ p3) ∧ p4) ∨ True) ∧ p2)) ∧ True)) ∧ ((p3 ∨ True) ∧ (True ∨ p5))) ∨ ((p2 ∧ p1) → (False ∧ (p5 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721654962268417555083847127609 : ((((True ∨ ((p4 → p5) → True)) → (((p2 → (((p4 → (False ∧ p1)) ∨ p1) ∨ (((p3 ∨ p4) ∧ False) ∧ (False ∧ p4)))) ∧ p1) → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46854472479793591336310727061 : (((((True → p1) → ((True → ((p1 → (p5 ∨ p3)) ∧ ((True ∧ p3) → True))) ∨ (False ∨ ((p4 ∧ p2) → p2)))) ∧ p1) ∨ (True ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45117277114390594437081509122 : ((((p5 ∨ True) → (((p5 ∧ (p1 ∨ p5)) → (((((p2 ∧ ((p3 ∨ True) → (p1 ∨ p1))) ∧ True) ∨ p4) → p3) → p2)) ∨ p1)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38614487770212091972829349545 : ((((False ∨ ((((p3 → p5) ∨ p4) ∧ p1) ∧ p2)) ∧ ((p5 ∧ ((False ∧ False) ∨ ((p5 → ((p4 ∧ True) ∨ p4)) → p2))) → p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123760950480226002183175307301 : (((p2 → (p2 ∧ ((p3 ∨ (p2 ∨ ((p4 → (True ∨ p4)) ∨ p5))) ∧ p5))) ∧ (p2 → ((False → ((p4 ∨ p5) → True)) → p4))) → (p2 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214549608083271561506781368245 : (((False ∨ p2) ∧ (p4 ∧ False)) ∨ ((((p3 → (False → (p5 ∧ p4))) ∨ (p1 → p4)) → True) → (p4 ∨ (p4 → (False → ((p1 ∧ p3) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321375973531563559648225524065 : (p4 ∨ (True → ((p4 ∧ ((p5 ∧ ((p1 → False) ∨ p2)) ∧ (p4 → (p1 → True)))) ∨ ((((p5 → False) ∧ (True ∨ p5)) ∧ (p2 ∨ p5)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18050503715658108025596382908 : (((p1 ∧ (((((p2 ∧ p4) ∨ (p2 → True)) → (p5 ∨ p5)) ∧ ((p4 ∨ (p3 ∧ True)) ∧ p2)) ∨ p3)) ∨ (p3 → (False → (p5 ∧ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775096285290067216219027591069 : (((False ∨ ((p5 ∨ p1) ∧ (((p3 → p5) ∧ True) → ((p2 → ((p4 → p3) ∨ (True ∧ p5))) ∧ (p3 ∨ (((p2 ∧ p5) ∧ p2) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206175442084572250226655700163 : ((p5 ∧ ((p2 → p2) → (False ∨ p5))) ∨ ((((p1 → p4) ∨ p1) → (False ∨ (((p5 ∨ p3) ∧ ((p5 ∨ False) → p1)) ∨ True))) ∧ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172710382689106893439580001422 : (((p2 ∨ p3) ∨ ((p5 → (p3 → ((p4 ∧ p2) ∧ False))) → (p3 → (p2 → p4)))) ∨ ((((p4 ∧ (False ∧ (False ∧ p5))) ∨ True) ∧ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184581950363177027866756965028 : (((p4 ∧ (((p1 ∧ p4) → False) → (p4 ∨ p4))) → (p5 ∨ p1)) ∨ (True ∨ (True → ((p3 → p4) ∧ (p3 ∧ (((True ∧ False) ∧ p4) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323816657964254571165521994034 : (p5 ∨ ((((p4 → True) → ((p1 → ((p4 → p5) ∧ p5)) ∨ (p5 ∨ (p1 ∧ (True ∧ p3))))) ∧ p2) → (((p3 → (p3 ∧ p1)) ∧ p3) → p1))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233398352026315329756874213767 : ((False ∨ (True ∨ p4)) → ((((p3 ∧ (False → p1)) ∨ (((((p2 ∧ (True ∧ p4)) → (p3 ∧ True)) → p3) ∧ p4) → p5)) ∧ p3) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59031070683252996414349437433 : (((p4 ∧ False) ∨ ((False ∨ (p1 ∨ (True → ((p1 ∧ (False ∨ (False ∨ True))) ∨ (p3 → (((p5 ∨ p1) ∧ False) ∨ p4)))))) ∨ (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118666656347231074354511984180 : ((p4 ∨ (p5 ∨ ((p4 ∧ ((p1 ∨ p2) ∨ (p1 ∧ (p2 ∨ p2)))) → ((p3 ∨ (p4 → (True ∧ p4))) ∨ ((p1 ∨ p4) ∧ p2))))) ∨ (p4 ∧ p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252768571771102312421352254699 : ((True ∧ True) → ((p1 → ((p1 ∧ (p3 ∧ (((p2 → p3) ∧ ((True → p3) ∨ p4)) ∧ p3))) ∧ (False ∧ (p4 ∨ False)))) → ((p1 → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114040253078492750807116983866 : (((((p4 ∧ (p1 → p3)) ∧ ((((p4 ∧ p4) ∧ False) → p3) → ((p5 → False) ∨ p1))) ∧ (True ∧ p5)) ∨ (p5 ∨ (True ∨ p2))) ∨ (p2 ∨ p5)) := by
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
theorem thm_5_vars_197799080853382053514990665916 : ((((p1 ∧ p5) ∨ False) ∨ ((True ∨ p2) → p1)) ∨ (True ∨ (((False ∨ p2) ∨ p2) → (True ∧ ((p1 ∨ (False → (p3 ∧ (p5 ∨ True)))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631446929288358252094459773563 : ((((((((p1 ∨ (p4 → ((False → True) ∨ ((p2 ∨ p5) ∧ p3)))) ∨ (((p1 → p4) ∧ p4) ∨ p3)) ∧ True) → (p3 ∧ True)) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961611675124736687232865369854 : ((((p3 ∨ p1) ∧ ((((p2 → p2) → (p4 ∨ (p4 ∨ (p4 → ((p3 ∨ p4) ∧ ((False ∨ (p4 → (p5 → p4))) → p3)))))) ∨ True) → False)) → p4) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 → p2) → (p4 ∨ (p4 ∨ (p4 → ((p3 ∨ p4) ∧ ((False ∨ (p4 → (p5 → p4))) → p3)))))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (((p2 → p2) → (p4 ∨ (p4 ∨ (p4 → ((p3 ∨ p4) ∧ ((False ∨ (p4 → (p5 → p4))) → p3)))))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197894720569975494429139557571 : ((((p2 → True) → p3) → ((p5 ∨ p3) → p2)) ∨ ((p1 ∧ p4) → ((p1 ∧ p3) → (p5 → (False → ((((False ∧ True) ∧ False) ∧ p3) ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655829035804625370284592808806 : ((((((p1 ∧ (((p3 ∨ ((False ∨ True) ∧ p4)) ∨ p4) ∧ (p2 ∨ (False → (False ∨ p1))))) ∨ p5) → (p3 ∧ (p3 → False))) ∨ (p5 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_63199955294708318390345764044 : ((p5 ∧ ((True → (p4 ∨ (p5 ∨ (p2 ∨ (((p3 ∨ (((p5 ∨ True) ∨ p1) → False)) ∨ (p4 ∨ False)) ∧ p4))))) → ((p4 ∧ p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43020924388828591104696069337 : (((((True → (((p1 → p2) ∨ (p4 ∨ p5)) → ((p4 ∨ ((p3 → (p4 → (p4 → p5))) → (True → False))) ∧ False))) ∧ p5) ∧ p2) → p3) ∨ False) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 → p2) ∨ (p4 ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45848248161070121068063065108 : (((p2 → (True ∨ (p1 → (p5 ∨ ((p4 ∨ (((p4 ∨ (p3 → p1)) → (p1 ∨ (((p5 ∧ p1) ∨ p3) ∨ p3))) ∧ True)) ∨ p1))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185911443521006599740707768767 : (((((p5 → (p5 → p2)) ∨ True) ∨ ((p4 → p5) ∧ p1)) ∧ p1) → (True ∧ ((p1 ∧ ((p5 ∧ (True → (p2 ∨ p3))) ∨ (p3 → p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225104928606364046396843249507 : (((p2 ∧ p1) ∧ p5) ∨ (((p2 ∧ (p3 ∧ False)) ∨ ((((p2 ∨ False) ∨ p4) ∨ p3) ∨ (p2 ∨ ((p3 ∨ p1) ∧ (True ∧ (p2 ∧ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610081187069573756468450763195 : (((((((p5 ∨ (False → p1)) ∧ (p2 → ((p4 → p3) ∧ ((False ∨ ((p5 → p4) ∨ (p5 ∧ p5))) ∧ (p3 ∨ p4))))) ∧ True) → p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228185861006948973089307650278 : ((p5 ∧ (p3 ∧ p4)) ∨ (((p3 ∧ ((((True ∧ p1) ∧ p3) → p4) ∨ (p4 → True))) → p2) → (True ∧ (p2 ∨ (p1 → ((False ∧ p5) ∨ p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715332199380620163285497305969 : ((((p4 → ((p3 → False) → (True ∨ p1))) → (((((True ∧ True) ∨ (p3 ∧ p5)) ∨ ((p4 ∨ True) → p3)) → (False ∨ True)) → (p2 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190108234780901268668890415324 : ((((p4 → (p4 ∨ (p5 → p2))) → (p4 ∧ p4)) ∧ p5) ∨ (p1 ∨ (p3 ∨ (((p2 ∧ (p5 ∧ p1)) → (((p1 ∨ p3) → p4) → True)) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646784856808403784891708645035 : ((((p2 → ((p2 → ((((False ∨ ((p1 ∨ p5) → False)) → False) → False) ∧ (True → (False ∨ (False ∨ False))))) → ((p2 ∨ False) ∧ p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309647137922673691408574244349 : (p2 ∨ ((p1 ∧ (((((p4 → (p1 → True)) → (False ∧ (((False ∧ p5) ∨ p3) ∧ p2))) ∨ True) ∧ (p3 → p1)) ∨ True)) ∨ (p2 ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_596715896904690362087377417223 : ((((((p3 ∧ p2) → ((p1 ∨ False) ∨ p2)) ∧ (((p5 ∨ p1) → (p5 ∧ ((False ∨ True) ∧ p4))) ∨ (p5 → (p1 ∨ (True ∧ p5))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613416491883080942950643134378 : (((((p5 ∧ ((p2 → (p5 → ((p1 → False) ∨ p5))) → (p2 ∨ ((((p5 → p1) ∧ p3) → p5) ∧ (p3 → p4))))) → (p1 ∧ p3)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57915635300371113263250816814 : (((p5 ∨ (p5 ∧ p5)) → ((p1 → (((p1 ∧ ((False ∨ ((p2 ∨ p1) ∧ (p2 ∨ True))) ∧ p4)) ∨ p3) ∧ (p3 ∨ (p4 → p2)))) ∨ True)) ∨ p4) := by
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
theorem thm_5_vars_266181687848875024137662439077 : (True ∧ (p4 → (((((p4 ∨ (False ∨ p4)) ∧ (p5 → p1)) ∧ (p1 ∨ True)) → (p4 ∧ (((False ∧ (p1 ∧ p4)) ∧ p3) ∨ (p4 ∨ p5)))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47362976742157776788337975866 : ((((p3 ∨ False) ∨ ((p4 ∧ (((True ∨ True) ∨ p5) → p2)) ∨ (p5 ∧ (((p1 ∧ (p4 ∧ p5)) → p3) → (p1 ∧ p4))))) ∨ (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149235317041104922505656748270 : (((p5 ∧ p5) ∨ (((p4 → (((True ∨ p5) ∨ p1) ∧ ((False ∧ p2) ∨ False))) ∨ False) ∨ ((True ∨ p4) ∧ p1))) ∨ ((p5 → (p2 ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44624207454478810650189728226 : ((((((p4 ∧ True) ∧ p2) ∧ (p2 → p5)) ∧ (False ∨ (p4 → ((True → (p4 → (p1 ∨ (p5 ∨ ((p1 ∧ p5) ∨ p4))))) ∨ p5)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229524970851634320616997317823 : ((p2 → (p3 ∨ p5)) ∨ ((p1 → ((((p3 → False) ∧ True) → p5) → ((p1 ∨ p4) ∧ p3))) → (p2 ∨ ((p3 → (p5 ∨ False)) ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178158954763243109538584900799 : ((((p1 ∨ p4) ∧ ((p4 ∧ ((p3 ∨ p5) ∨ (p1 → False))) ∧ p1)) → False) ∨ (p3 → (((False ∧ p3) ∧ p1) → (p4 → ((p1 → False) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134112123922106614142336904865 : (((((p2 → p4) ∨ (p1 → (((p1 → ((False ∨ True) ∧ p2)) ∧ (p1 ∧ (True ∧ p3))) ∨ p2))) ∧ (p1 → False)) ∨ p1) ∨ (True → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191940350873159955363366900637 : ((True → ((p1 ∨ p1) ∨ ((p1 ∨ p4) ∨ (p2 ∨ False)))) ∨ ((True ∨ True) ∨ ((((True ∨ p1) ∧ (p5 → (p5 ∧ p3))) ∨ p2) ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804076842859910426869078397381 : (((p3 → ((((((False ∨ ((p5 ∨ ((p4 → p5) → False)) ∨ p1)) ∨ p1) → p5) ∨ (p4 ∧ p2)) ∧ False) ∧ ((p4 ∧ False) → (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156720902513478481904171865580 : (((((p4 → (p2 ∧ p5)) → ((p5 ∨ p5) → True)) → ((p3 ∧ p1) ∧ ((p4 ∨ p1) → p1))) ∧ p3) ∨ ((p4 ∨ p4) ∨ ((False → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209558709133214545567771693001 : ((p5 → ((False ∧ (False ∧ p5)) ∨ True)) → (p2 ∨ (((p1 → ((p5 ∧ p2) ∧ p4)) ∨ False) ∨ (p3 → (True ∨ ((p5 ∧ (p4 ∨ p2)) ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193284902898776020251717506025 : ((((p5 ∧ p1) ∨ p2) ∨ ((p5 ∨ True) ∧ (p4 ∨ p4))) → ((p2 ∨ p4) ∨ (True → (True ∧ ((p5 → ((p2 ∨ p3) → True)) ∧ (True ∧ p1)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18



