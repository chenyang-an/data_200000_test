variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116020135379138418962615195406 : (((True ∧ (p1 ∧ (p1 ∨ p4))) → (((p4 ∧ (False → p1)) ∨ (p2 ∨ p1)) → ((p2 ∧ p1) → (((p5 ∨ p5) ∧ p1) ∨ p2)))) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50415152415824860931196760888 : (((p1 ∧ (p4 ∨ ((p1 ∧ p5) ∨ (p4 → (p2 ∧ ((p1 → ((p3 → p5) → p5)) ∨ (p1 → False))))))) ∨ ((True ∧ (p5 ∨ False)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244543706831266569197335195657 : ((False ∧ p3) ∨ (p3 → (((p2 ∨ (p3 → False)) ∨ (p2 ∨ ((False → (True ∧ p4)) ∨ (p1 → (((True ∧ p3) ∧ p2) ∨ True))))) ∨ (p4 ∧ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258897455568762421015092169696 : ((True → p2) → (((p4 ∨ (p1 → p1)) ∧ (((p2 → (p2 ∨ (p3 → p1))) → ((((p5 ∨ p1) → p2) ∧ p3) → p1)) ∧ p2)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305166842021560391914926337621 : (p1 ∨ (((p2 → (((True ∧ (((p1 ∧ (True ∨ (p2 → p3))) ∧ (p2 ∧ True)) ∨ True)) ∧ True) ∧ p5)) → False) ∨ ((p1 → (p4 → p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152179804956016730663414839334 : ((((p2 ∨ (p3 ∨ (False → (p5 ∧ False)))) → p5) → ((((p5 → (p1 → False)) ∨ p2) → p4) → (True ∧ p3))) → ((True ∧ (p5 ∨ p5)) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143084066180679983194269893893 : ((False → (p3 ∧ (p3 ∧ ((p1 → ((p5 ∨ (True ∨ (p4 ∧ (p2 ∨ ((p2 ∧ True) ∧ (p4 ∧ p2)))))) → p5)) → p1)))) → ((p3 → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159570254323581337951402513399 : (((p4 ∨ ((p3 → True) ∨ (((p2 ∨ (((p5 → True) → p2) ∧ False)) ∨ p3) ∨ (p3 ∧ p4)))) ∧ p3) → (((True → True) → (p4 ∨ p5)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717375391895622432911527776418 : ((((True → ((p1 ∧ True) → True)) ∧ (p2 ∧ ((True ∨ p4) → (p5 ∧ (((True ∧ ((((True ∧ p4) ∧ False) ∧ p4) → p1)) → p3) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179255561804168914449800782836 : ((p5 ∧ (p3 ∧ ((((p5 → p1) ∧ ((p1 ∨ False) ∧ p2)) ∨ p1) ∨ p4))) ∨ ((p1 ∧ (((True ∧ (False → (p1 ∨ p4))) ∨ p5) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47152017853054060518470996048 : ((((p5 → (p2 ∧ ((((True ∧ (p4 ∧ p4)) ∨ p4) ∨ (p4 ∧ p2)) ∧ (False → p4)))) ∨ ((p2 ∨ p3) ∧ (False ∧ p2))) ∨ (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165091595145419032144877955280 : (((p3 ∨ ((p3 ∧ (p4 ∧ (False → (p1 → ((p4 ∧ p5) ∨ p2))))) → (False ∧ p1))) → False) ∨ ((p4 → (p4 ∧ (True ∧ (p4 ∨ p4)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39398049001904595308017993344 : (((p4 ∧ (((p2 ∨ p4) ∨ (((p3 ∧ p4) ∧ ((((True ∧ (p3 ∨ (p1 ∧ p4))) → (p5 → False)) ∧ p1) ∨ p5)) ∧ True)) ∨ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936616695484483611921384919445 : (((((p3 → ((p1 ∧ p4) ∧ False)) ∧ p3) ∧ (((((p4 ∧ (((p1 ∨ False) → True) ∨ False)) ∨ (p3 → p3)) ∨ (p2 ∧ False)) ∨ p1) → True)) → False) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50732229135151874241252456064 : (((True ∧ ((True → False) ∧ (((p1 → ((((p2 → p2) ∧ p5) ∨ p5) ∧ (p2 ∨ False))) ∨ p3) → False))) → (p2 ∧ ((p2 ∨ True) ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680704894860958346565353017095 : (((((p5 ∧ ((p1 → p4) → p5)) ∧ ((True ∧ True) ∧ (((p2 ∧ p4) ∨ True) ∧ ((p4 → p2) ∨ p4)))) → ((p5 → p1) ∨ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192427791064430648186993894313 : (((((p5 ∧ ((p3 → p4) ∨ True)) ∧ True) → False) ∨ p1) → (((False ∨ (p3 ∨ (p2 → True))) ∧ (True → ((True → (p1 ∧ False)) ∧ p3))) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h10 := h4 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h23 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h31
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- We need to get the right conjuct of h35 based on <expert-advice>.
        let h36 := h35.right
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185080313161379140275178138468 : (((False ∨ p5) ∨ (((True ∧ True) ∨ p5) → (False ∧ (p1 → True)))) ∨ (((False → p5) → (p5 ∨ (p5 ∨ (p5 → ((p4 ∨ True) → True))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56543492428123666414596177814 : (((p2 ∨ ((p2 ∨ False) ∧ p5)) → (p1 ∨ (True ∧ ((((False ∧ ((p5 ∨ p4) ∧ False)) → (p1 ∧ (True ∧ p4))) → p4) → (p2 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116491682142706061028083820532 : (((p2 ∧ p5) ∧ ((((False ∨ ((((p4 → (p5 ∧ p4)) → (p5 ∨ p1)) ∨ (p5 ∨ False)) ∧ p1)) ∧ p2) → (p2 ∧ p5)) ∨ p1)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113237347383292394491273955709 : ((((False ∨ (((True ∧ ((p1 ∧ p4) ∧ p5)) ∨ p2) ∨ (((p1 ∨ p5) → p2) ∨ (p4 ∧ (False ∨ p5))))) → p1) ∧ (p4 ∧ p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299317503631295475449049062183 : (False ∨ (((((False → p1) ∨ True) → (p5 → p2)) ∨ ((p3 ∧ ((((True ∨ p5) ∧ p2) ∨ p1) ∨ (p1 ∧ p3))) ∨ ((True ∨ p4) ∨ p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51522048259859505817886908655 : ((((p5 ∨ p5) ∨ ((((p4 ∨ p3) ∧ p1) ∨ (p1 ∧ p2)) ∨ ((p5 → p1) → (True ∧ False)))) → (p5 → ((p2 ∧ False) ∨ (False → p5)))) ∨ p3) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219149780236211370250547009848 : ((True ∨ (p4 → (p5 → p1))) → ((((p1 ∧ True) ∨ (True → p1)) ∨ (p4 → p1)) → (((p2 → p1) ∧ (((False → True) → False) ∧ True)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h20 := h14 h19
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h25 := h6 h23
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h27 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h29 := h6 h27
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707732484508848370318361721162 : (((((p3 ∨ p2) → ((False → (p1 ∧ p2)) → p4)) ∨ (p5 ∨ ((p3 ∧ ((p3 → (p5 ∨ p2)) → ((p3 ∧ (p4 ∨ p1)) ∧ p1))) → p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_744801203952918881860597793777 : ((((p3 ∧ p3) → (((((p4 ∧ ((True ∨ (p5 ∨ (False ∨ ((p2 ∧ p3) ∧ (p4 → True))))) → p1)) ∨ (True ∧ p3)) ∨ False) → False) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248830535489709360386485376529 : ((p3 ∨ p4) ∨ (((((p1 ∨ p5) ∧ False) ∨ False) ∨ p5) ∨ ((False ∧ (((p1 ∨ (p2 → p5)) ∧ False) ∨ True)) → ((False → (p3 → True)) ∧ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67615204199718801653877722719 : ((p1 → (p3 ∧ ((p2 ∨ p3) → (p4 → ((((((p2 ∨ (p4 ∨ p3)) → (p4 ∨ True)) ∨ True) ∧ p5) ∨ p1) ∧ (p3 → (p2 ∧ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110891851345472784343984732778 : ((((((p2 → (p1 ∨ p5)) ∨ (p2 → False)) ∨ ((((((False ∨ False) → (p1 → p2)) ∧ p1) ∧ p3) ∨ p5) ∨ p1)) → False) ∧ p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299165444057054144982702971436 : (False ∨ (((((False → (p5 → (False ∧ ((p3 → p4) ∨ p2)))) → ((True → True) → (((p1 ∧ p5) → True) ∨ (False ∧ p5)))) ∨ p1) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337346902210404946729514149921 : (p1 → (((False ∧ ((p5 ∧ ((p2 ∨ p1) → True)) ∧ (p5 ∧ (p5 ∨ ((p2 ∨ ((p3 ∧ p4) ∨ p2)) ∧ p4))))) ∨ p1) ∨ (p1 ∧ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84111607444535554132139328587 : ((((True ∨ True) ∧ (((True ∨ (p4 ∧ ((p4 ∧ (p2 ∨ p4)) → p5))) → p1) ∧ True)) ∧ (((p1 ∨ (True ∨ (p5 → p5))) → True) ∨ p2)) → p1) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ (p4 ∧ ((p4 ∧ (p2 ∨ p4)) → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h13 : (True ∨ (p4 ∧ ((p4 ∧ (p2 ∨ p4)) → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ (p4 ∧ ((p4 ∧ (p2 ∨ p4)) → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h22 : (True ∨ (p4 ∧ ((p4 ∧ (p2 ∨ p4)) → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h23 := h16 h22
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337595447191708338482964393111 : (p1 → ((True ∧ ((True ∨ (p3 → (((p1 ∨ p3) ∧ False) → (p4 → p5)))) ∨ (p2 ∨ (True ∧ (p2 ∧ p4))))) → (((p2 ∧ p5) ∨ p4) ∨ True))) := by
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
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302698753643811619600474300153 : (False ∨ (p3 ∨ ((((p4 → p3) ∨ p3) → ((p4 ∨ ((((p4 ∧ True) → True) → True) ∧ p1)) ∨ True)) ∨ ((((p5 → p5) ∧ False) ∨ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60490998992517305566642329482 : ((True ∧ (((p5 → (p3 ∧ (((p4 ∧ False) → ((True ∧ (False → p1)) → p5)) → ((False ∨ (p2 → p3)) ∨ (p4 → True))))) → p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599041448300892876001476373221 : (((((p4 ∨ p5) ∧ (((p5 ∨ ((p3 → False) ∨ False)) ∧ (p5 ∧ p3)) → (((p1 ∨ p4) ∧ (((p1 ∧ p1) ∧ p2) → p2)) ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793791495617528970716982851016 : (((True → (p1 → (True ∧ (((True ∧ p2) ∨ ((False → p2) → (True → (p5 ∨ (p5 → False))))) ∨ (((p3 ∨ p1) ∨ p3) → (p2 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238298409110726684073811876426 : ((False ∨ True) ∧ (((p4 ∧ ((p2 → (((False ∨ ((p3 → False) ∧ False)) ∨ ((p1 ∨ p1) → p2)) → p2)) → p4)) ∧ (True → (p1 → p4))) ∨ True)) := by
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
theorem thm_5_vars_678744637900395511508245738430 : (((((p1 ∨ p1) → ((p5 → ((((p1 → p3) ∨ p4) ∨ ((p4 ∧ p1) ∨ p2)) ∨ p1)) ∨ (p4 ∧ p2))) ∨ ((p4 ∨ False) ∨ (p1 ∧ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613841384448069165490780940255 : ((((((((p2 ∧ ((p3 → p1) ∧ p3)) ∨ True) ∧ ((p5 ∨ (((True ∧ False) ∧ p5) ∨ p3)) → p4)) ∧ p5) ∨ (p3 → (p5 ∨ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175107329776586087910663067304 : ((p4 ∧ ((True ∧ ((p2 → (p4 ∧ p4)) → ((p4 ∧ True) ∧ p5))) ∨ (p3 ∨ p1))) → (False ∨ (((p5 ∨ p2) ∧ (False → False)) → (p5 ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
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
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50329194424036088049653351970 : (((((p4 ∨ False) ∧ ((p3 ∧ (False ∨ True)) → p4)) ∧ (False ∨ (p2 → (p2 → (True ∧ (p3 ∨ p1)))))) ∨ ((True ∨ (p2 ∧ True)) ∨ p4)) ∨ p5) := by
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
theorem thm_5_vars_53270714822056680954437577929 : (((False ∧ ((p2 ∧ p5) ∧ ((False ∨ p1) ∨ ((p4 ∨ p2) ∧ p1)))) ∨ (((True → p2) → (p1 → p3)) ∧ (((p5 ∨ p4) → False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46241669662445288317913300604 : (((((p1 ∨ True) → (p3 ∨ (p1 ∧ ((((p1 ∨ p1) → p1) ∨ ((True ∧ p3) ∧ (p2 → False))) ∨ p5)))) ∨ (p2 → True)) ∧ (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92657375282787331972527103647 : (((p1 → p1) → (((((((p4 → False) → (True → p2)) ∨ p4) ∨ p5) → (((p2 ∨ p5) → p5) → True)) ∧ (p5 → False)) ∧ (False ∨ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46902446568299125174835205859 : (((((p4 ∧ (((p5 → p1) ∧ (p3 ∧ False)) ∨ ((p5 → ((True ∧ p4) ∨ (p5 → p5))) → p3))) ∨ (p1 ∧ p4)) ∨ False) ∨ (p3 → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252266306695042985235731304318 : ((p4 → p5) ∨ (((((p3 → p5) ∧ p3) → (((p1 ∧ (True → ((p1 ∨ p2) ∨ p4))) ∨ (p4 ∧ p5)) ∧ p1)) ∨ (p5 ∨ (True ∨ p5))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_134404867215251131795736585318 : (((p1 → (((p3 ∨ ((True ∨ p3) ∨ ((False → (p1 → False)) ∨ p5))) ∧ (((p1 → False) ∨ p5) ∨ p4)) ∧ True)) ∨ p3) ∨ ((p5 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111709354229063831347687437032 : ((((((p5 → ((p4 → ((p5 ∧ True) ∨ p1)) ∨ ((p4 ∧ True) ∧ p2))) ∧ True) ∨ ((True ∧ (p2 → p3)) ∧ p1)) → p5) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52017502943316212331704564827 : (((p5 ∧ (p4 → ((((p3 ∧ p5) → p4) → (p1 → (p3 ∨ (True ∨ True)))) → False))) ∨ (p3 → ((True → (p3 ∨ True)) → (p5 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167989486748368144913395025374 : ((((True ∨ p3) → (False ∨ (False ∧ p1))) ∧ (p1 → (((p5 ∨ p2) → True) → (True ∨ p1)))) → (False ∧ (((p1 ∨ (p2 → p4)) ∧ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h25 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h26 := h22 h25
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215257056807814401763597908869 : ((False ∧ (p3 ∧ (p4 ∨ True))) ∨ ((((p5 ∧ (((p5 ∧ ((p2 → (p3 ∨ p4)) ∧ p4)) ∧ False) → True)) ∧ p1) ∧ (True → (p4 ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61232554510413343212769977293 : ((False ∧ (p2 ∧ ((p1 ∧ (p1 ∨ p4)) → ((p5 ∨ (p1 ∧ p5)) ∨ ((p4 ∧ p3) → (((p1 → ((p5 → p1) ∨ p2)) ∧ p5) → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167503377284932409371944014685 : (((((True ∧ ((p2 → False) ∨ (p5 ∧ False))) ∨ p1) ∧ (p4 ∨ (True → p3))) ∧ (p2 ∨ True)) → ((p4 → ((p5 → p1) ∨ p4)) ∨ (p3 → p4))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h12 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h13 := h9 h12
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h17 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h18 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h19 := h9 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h28
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h33
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h35
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174104314026481466104452906388 : ((((False ∧ p3) ∨ (p5 → (((p5 → p5) → (p5 → p2)) ∨ p5))) ∧ (p1 → p1)) → ((((False ∨ (p2 ∧ (p3 → False))) ∧ p4) ∧ p5) → p2)) := by
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
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776711143082818700042453450927 : (((p1 ∨ ((((((p3 → (False ∧ False)) ∧ (((p2 ∨ p4) → (p1 → False)) ∧ True)) ∧ ((p5 ∨ True) ∨ (False ∨ p2))) ∨ p2) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755657537144089365453922243703 : (((p1 ∧ (((p3 → ((p2 ∧ ((p1 ∧ True) ∧ (p5 ∨ (((p5 ∧ p2) ∨ p5) ∨ (p1 → p3))))) ∧ p1)) ∨ ((p3 → p4) ∨ p5)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56230466818976034386180189699 : (((p4 ∨ ((p5 → p4) ∨ p5)) ∨ (p2 → (p1 ∨ ((p5 ∨ (p3 → p1)) → (p3 ∨ (p3 → ((((p5 ∧ True) ∧ p2) ∨ p4) → p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649658767866361011572363171937 : (((((True ∧ ((False ∨ (p2 → p3)) ∧ ((True ∨ p5) ∧ ((p5 → (False → p5)) → ((p4 ∧ p5) ∧ p4))))) ∨ (p2 → True)) ∧ (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124399785674379115787271763945 : (((p3 ∨ (p1 → (((True ∧ False) → p1) ∨ p4))) ∨ (((p4 → p5) ∧ p3) ∨ (p2 ∨ (p5 ∧ (((True ∨ p4) ∧ p1) → False))))) → (p4 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16149703614768517184767290369 : ((((((p4 ∧ True) ∨ (((p5 ∧ False) ∨ ((p1 ∧ (p5 ∧ p5)) → (p1 → p1))) ∨ p3)) ∨ (p4 ∨ p3)) ∨ p4) ∧ ((False ∧ p3) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137343136537342048221841034922 : ((p2 ∧ (p3 → ((((p2 ∧ (False ∨ ((p1 → p3) ∧ False))) ∨ False) → p1) → (((p1 ∧ (p2 → p5)) ∨ True) ∧ p5)))) ∨ ((p1 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699106312184711816753512624648 : ((((p5 ∨ ((p1 ∨ (p4 ∧ (p5 ∧ (p1 ∧ False)))) ∨ (p2 ∨ p2))) ∨ (p3 ∨ (True → (False → (p4 ∨ ((p5 ∨ p3) → (p1 ∧ False))))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123396582695822151144375458790 : (((((((((p1 ∨ ((p4 ∧ True) ∧ (p2 ∨ True))) ∧ False) ∨ p4) → p3) → p2) → p1) → p3) → ((p4 ∧ False) ∧ (p2 → p1))) → (p3 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((((p1 ∨ ((p4 ∧ True) ∧ (p2 ∨ True))) ∧ False) ∨ p4) → p3) → p2) → p1) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788332287260339284137262889154 : (((p5 ∨ (((p4 ∨ ((p1 ∨ True) ∧ ((p2 ∧ ((p5 ∨ ((False → p2) → (p3 ∧ p3))) → (True ∨ (p1 ∧ False)))) ∨ p4))) ∨ True) ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51392144278336663168247366473 : ((((False ∨ (((p3 ∨ p3) ∧ (p5 ∧ (p3 → p2))) → ((p1 → (p3 → p4)) ∨ p4))) ∨ p2) → (((p1 ∨ True) ∨ False) ∧ (p2 → p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230540137267533158634933553741 : (((False → p2) ∧ p2) → ((((True → (p5 ∧ (p3 → (p5 ∧ p5)))) ∨ (p3 → (p1 ∧ p2))) ∧ ((p3 ∧ (p1 → (False → p5))) ∧ p5)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134089543827523010839823124269 : (((((p4 ∨ p4) ∨ (((((p3 → p1) ∧ (((p2 ∧ (p4 ∧ p3)) ∧ p1) ∧ True)) ∨ p2) → p4) ∨ p4)) → p3) ∨ True) ∨ (p3 ∧ (True → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979930210344186688628622907 : (True → ((((((p4 ∨ (False → (p5 ∨ False))) ∧ p5) ∨ p3) → (p1 ∨ ((p3 ∨ p2) ∨ (True ∧ (True ∧ True))))) ∨ (p3 → (p5 → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62708855172530693206926937441 : ((p4 ∧ (((p3 → (p5 → False)) ∨ (p3 ∧ (((((p4 ∧ p5) ∨ (p3 → ((p3 ∧ p4) ∨ p2))) ∨ (p1 ∧ p1)) → p2) ∧ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603835904031304427391732506452 : ((((p4 ∨ (True ∧ (((p4 ∨ (p2 ∨ p1)) → p3) ∨ (((True ∨ p1) ∧ p5) → (False ∨ (p3 ∧ ((p4 ∨ False) ∧ (p4 ∧ True)))))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343557072502520805982663488230 : (p2 → ((p3 ∨ p1) → ((p4 ∧ p1) ∨ (p4 ∨ ((((p3 ∧ ((((p1 → (p3 ∧ (True ∧ p3))) → p2) → p2) ∧ True)) → True) ∧ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172887345366095843702080255713 : ((p1 ∧ (p3 ∧ ((p3 ∧ (((p2 ∧ (p5 ∧ p4)) → False) ∧ p3)) ∧ (p4 ∨ p2)))) ∨ ((True ∨ p3) ∨ (((p2 ∨ True) ∨ (p2 ∧ p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15384122215433438647451950462 : (((((p4 ∧ ((p5 → p1) → (False ∨ False))) ∨ ((((p5 ∧ (p5 → (p3 ∧ p2))) ∧ (p2 ∨ p1)) ∨ p4) → p4)) ∨ False) → (p1 → p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585339378342190960478672985268 : (((((((False ∧ (p5 ∨ (((p3 ∧ p5) ∧ p5) → (False ∧ (((False ∧ (p2 ∧ p2)) → p1) ∧ p3))))) ∧ (p4 ∧ p5)) ∧ False) ∧ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126887596990246247160379900869 : ((p5 ∧ (True → (True → (True ∧ (((False ∧ (p3 ∧ ((False ∨ ((p1 ∧ True) → (True ∧ p1))) ∧ p2))) → (False → p4)) ∧ False))))) → (p4 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205089169681349753995513948828 : ((((p5 ∧ False) ∧ p3) ∧ (p2 ∨ p3)) ∨ ((((p4 → (p4 ∨ ((p3 → p5) → ((p2 → (p5 ∧ (p3 ∨ p1))) ∧ p3)))) → False) ∧ False) → p1)) := by
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
theorem thm_5_vars_724842030594289908248571674464 : ((((p4 ∨ (True → False)) ∧ ((((False ∧ p2) ∨ (((p4 ∧ p1) ∨ (p4 ∨ ((True ∨ p5) ∧ (p4 → p5)))) ∨ (p3 ∧ p5))) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147243065066255763246358156181 : (((((p4 ∨ (((p4 → p5) ∨ (p5 → False)) ∨ p1)) ∨ (p5 ∧ (p5 ∧ (p2 ∨ (p2 → p3))))) ∧ True) ∨ p4) ∨ ((p1 → (p4 → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685879146673621398933478882349 : (((((p5 ∧ ((((p1 → (True ∨ p4)) ∨ (p3 → p2)) ∧ ((False ∨ True) ∨ p1)) ∧ True)) → p2) → (((p2 ∨ p4) → (False ∨ p3)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63958639681163612748575763502 : ((False ∨ ((p4 → (((((((True → False) ∧ (p5 ∨ (p5 → p2))) ∧ (p3 → True)) ∨ (p5 ∨ True)) ∨ p4) ∨ (False ∧ False)) → p5)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185306413539997795885241415453 : ((p3 ∧ (((((False ∨ p4) ∨ p3) ∨ (p1 ∨ p3)) → p1) ∧ p5)) ∨ (p2 → ((((p5 → p2) ∧ p4) → p4) ∨ ((p4 ∨ p5) → (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96385977505786254389004946719 : ((False ∨ (((p3 ∨ (((((p4 → (p4 → (False ∨ (False ∧ p3)))) ∨ (p2 ∨ False)) → p5) → p5) ∨ True)) ∨ (p3 ∨ p3)) → (False ∨ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∨ (((((p4 → (p4 → (False ∨ (False ∧ p3)))) ∨ (p2 ∨ False)) → p5) → p5) ∨ True)) ∨ (p3 ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64726342195837122631758328212 : ((p1 ∨ (p5 → (((p1 → p5) → (p1 ∧ (((p3 ∨ p2) → (p2 ∨ p1)) ∧ (p2 ∧ (True → (False ∧ ((p4 ∨ False) ∨ p3))))))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210287947400734591118169295528 : ((((p5 → p1) → p3) ∨ True) ∧ ((((p2 ∧ (p2 ∧ p4)) → (True → p5)) ∨ (True ∧ (False → (p5 ∨ p5)))) → (p1 → ((p5 → p3) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181002669645554307878810353897 : (((True ∨ p3) ∨ ((p1 ∨ ((False ∨ p4) ∧ p2)) ∧ (True ∨ (False → p3)))) → (((p5 ∧ ((p4 → p1) ∨ p2)) → ((False ∨ p5) ∨ p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38109195258513798501044499061 : (((((((p2 ∧ p2) → ((p5 ∧ (p3 ∧ (p5 ∧ p4))) → (p4 ∨ (p2 ∧ (True → p3))))) → False) ∨ p5) ∧ ((p5 ∨ p2) ∧ p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382260667722210224833556335210 : ((((((p1 ∨ ((p2 → ((((p3 ∨ ((p2 ∧ (False ∨ p2)) → False)) ∨ p4) ∧ False) ∨ p5)) ∧ p1)) ∨ (p3 → (True ∨ False))) ∨ p4) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351515597730872543940597061868 : (p4 → (((((False ∧ True) ∧ (((p3 ∨ p1) ∧ p4) → (((p3 ∨ p4) → p3) → p1))) ∨ False) ∧ True) ∨ (p5 ∨ (p1 → (p1 ∧ (p1 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178294623006702792464445823594 : (((p5 ∨ (((p5 ∧ p1) ∨ (p5 ∨ p5)) ∧ (p3 → True))) ∧ (p2 → p1)) ∨ ((False ∨ (False ∧ p4)) → (p2 → (((False → p5) ∧ p5) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645859972529500717381194705498 : ((((True → (((((p1 → (p1 ∨ True)) → (p5 → True)) → p3) ∧ (((p5 ∨ p3) ∧ (True → True)) ∧ (p3 ∨ (p1 → False)))) ∧ False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625683536564248336152764472939 : ((((p1 → (((((p4 ∧ p1) ∧ p1) ∧ (p1 → (p5 → (False → p4)))) → (False ∧ (False ∧ p5))) ∨ (True ∧ (p1 ∧ (p3 ∨ True))))) ∨ p2) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241819831461227049295520123232 : ((p1 → p1) ∧ ((((p2 ∧ (True → (p2 → (((True ∨ True) ∨ p3) → ((True ∧ p2) ∨ (p1 ∨ ((True ∨ p4) ∧ p1))))))) → p1) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254073737852243531198404312191 : ((p2 ∧ True) → (p4 ∨ ((p5 ∨ p1) ∨ (((p3 ∨ p4) ∨ ((((True ∧ ((p2 → p5) → p4)) ∧ ((p1 ∧ p1) → p3)) → p2) ∧ True)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115851436941045969836996538966 : (((p2 ∨ (p3 ∨ (p4 ∨ False))) ∧ ((p3 ∨ ((p2 ∨ p5) ∧ False)) ∨ (p5 ∧ ((p2 → ((p1 ∨ p1) ∧ p2)) → (p3 → p1))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37440226767221834438028922685 : ((((((p5 ∨ (((p5 ∨ p1) → (True ∧ p5)) ∨ True)) ∧ (p1 → ((p5 → p1) ∨ p3))) → ((p3 ∧ p4) ∨ (p3 ∨ p4))) ∨ p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615344013483879362684408240092 : (((((((p1 ∧ p4) ∨ (p2 → (((p3 ∧ False) ∨ p1) ∨ True))) → ((p3 → False) ∨ True)) ∨ ((p4 → (p2 → (False ∧ p1))) ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185191919695739286696775835499 : ((True ∧ (((((p5 → (p1 ∨ True)) ∨ p5) ∧ p3) ∧ p3) → False)) ∨ ((p2 ∧ (p5 → ((p3 ∧ (True → p3)) ∨ p5))) → ((True ∨ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_173354506307034297860808527288 : ((p3 → ((((p1 ∧ (p1 ∨ (p2 ∧ p3))) ∧ (p5 ∧ True)) ∧ p4) ∨ (p3 ∨ p4))) ∨ ((True → (((False ∧ p1) → True) ∨ p3)) ∨ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115820900692763294657319650505 : ((((p2 ∧ p3) ∨ (p5 → p5)) ∧ (False ∨ ((((p3 ∧ ((False ∨ False) ∨ True)) → p1) ∨ (p5 ∧ ((False ∨ p4) ∧ p3))) ∨ p2))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



