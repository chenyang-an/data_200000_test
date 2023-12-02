variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191201175070966684868098384993 : ((((p1 → p3) ∨ p5) → (False ∨ (p4 → (p1 ∨ p3)))) ∨ ((False → ((p2 ∧ False) ∧ p1)) ∨ ((p2 ∨ (p5 ∨ ((p4 ∨ p1) → p2))) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_200784089289609804714987322433 : ((p4 ∧ (p4 ∧ (p4 ∨ ((p4 ∧ p5) → True)))) → (False ∨ (p5 ∨ (((((False → (p2 → p2)) → p5) → (p5 ∧ p1)) ∨ p3) ∨ (p3 ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178653671018166080203062791956 : (((((True ∧ False) ∨ False) ∨ False) ∧ (((p1 ∧ (p4 → p3)) ∨ False) → False)) ∨ (False → (((((False → (p1 ∧ True)) ∧ p5) → p5) ∧ p4) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660078588472446570760854925740 : ((((((((True ∨ p3) → True) ∨ (p1 ∧ ((p5 ∧ (False → ((p3 ∨ (True ∧ p5)) → False))) ∧ p2))) → (p4 ∧ p1)) ∨ True) → (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58328949233921199039684183692 : (((False ∨ p1) ∧ (((((((p5 ∨ p1) ∨ (p2 ∧ True)) ∨ True) → True) → p4) ∨ p3) ∧ (p2 ∧ ((p5 ∨ (p3 ∧ (True → p5))) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341672303007107024029107715709 : (p2 → ((((((p3 → p4) ∧ (p1 ∨ p5)) ∨ ((p1 ∧ (((False ∨ False) ∨ p1) → p2)) ∨ p3)) → (False ∧ (p3 ∨ p4))) ∨ p3) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329099879606003122367341973552 : (True → (((p4 ∧ (p4 ∨ p5)) ∧ False) ∨ (False ∨ (p3 → (False ∨ ((((False → (True ∨ (((p2 → p2) ∧ True) ∨ p4))) ∨ False) → True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178239934168141549825935159451 : (((((((p2 → p1) ∨ p2) ∧ (True → True)) ∨ p2) ∧ p2) ∧ (p4 ∧ p2)) ∨ (((True ∧ (False ∧ (p3 ∧ True))) → (True ∧ p4)) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231777543741776450136854495794 : (((p3 ∧ p5) → p2) → (((p4 ∨ p2) ∧ p1) → ((((p2 ∨ (p5 ∧ p4)) ∧ p4) ∨ p2) ∨ (p3 → ((p1 ∨ ((True → p2) ∨ False)) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204245261054842800722971025227 : ((((p4 ∨ p1) ∧ (p3 → True)) ∧ False) ∨ (((p3 ∨ ((p2 ∨ p1) ∧ (((False → p4) → p3) → (p3 ∨ False)))) ∧ p5) ∨ (True ∨ (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55163839925781153671517795928 : ((((p3 ∨ (p4 ∧ (p3 → p2))) ∨ p2) ∨ ((p3 ∨ (p2 ∨ ((p5 ∨ p2) ∨ True))) → (p4 ∨ ((p4 ∨ (p4 ∧ (True → False))) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318583232457989400054566757762 : (p4 ∨ (((p1 ∧ (((p2 ∧ p3) ∧ True) ∨ ((((p1 ∨ p3) → p5) → ((p5 ∨ False) ∧ (p2 ∧ p3))) ∧ p3))) → (p2 ∨ p2)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62776774121474249289223457330 : ((p4 ∧ (((p2 → (p2 ∨ (((p4 ∨ p5) ∨ (False → p2)) ∨ (p4 ∨ (p5 ∧ p1))))) ∧ (p2 ∧ p5)) ∧ ((False ∨ (p1 → p1)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52281957209361141037491431835 : (((p3 → ((p5 ∧ p3) → (((False → (p5 → (p5 ∨ p2))) ∧ (p1 ∧ False)) ∧ True))) → (p4 ∧ (((p1 ∨ p3) ∨ (p5 ∧ True)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151831756646922088198694033821 : (((p5 ∨ ((((p4 ∨ p3) ∧ (p3 ∨ (p2 → p3))) ∨ p3) ∨ (p2 → p4))) ∧ (((True ∨ p2) ∨ True) → False)) → (((p4 ∧ p4) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h16 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h17 : ((True ∨ p2) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h18 := h3 h17
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h20 : ((True ∨ p2) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h21 := h3 h20
            -- False on the left can always be used.
            apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : ((True ∨ p2) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : ((True ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h26
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112034325556742469440946448475 : ((((p1 ∧ (p1 → p2)) ∨ (p2 ∧ ((p5 ∧ (((p4 ∨ (p1 ∧ p4)) ∧ (p3 ∨ p5)) ∧ (p3 → (p4 ∧ p4)))) ∧ False))) ∨ False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699445371772473061126112406769 : ((((((((p2 → (True ∨ False)) → (p2 ∨ p5)) ∧ p2) → p4) ∨ p3) → ((((p3 ∧ True) ∧ p4) ∧ p4) ∨ (p2 → (True → (p1 ∨ True))))) ∨ p5) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49246033285572002441211951336 : ((((p2 → p4) → ((((p5 → (False ∨ ((p5 ∨ p2) ∧ p2))) ∨ (False ∧ (p2 ∨ p2))) ∨ p4) → (True → p5))) ∨ ((p5 → p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766525830140817168090500214845 : (((p4 ∧ (p3 ∧ (((p1 → True) ∧ ((p5 ∨ (p4 ∨ p2)) → ((p5 → p2) → (p3 ∧ (p1 ∨ p4))))) → ((False ∨ p4) ∧ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208410276747007691840258284658 : (((p1 ∨ False) ∨ ((p2 ∧ False) ∨ True)) → (((p3 ∧ (((p2 ∨ p1) ∧ p1) ∧ p2)) ∨ (True ∧ (False → (((p4 → True) → p1) ∨ True)))) ∨ False)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630007513625281192874081722428 : (((((((p3 → (p4 → False)) ∨ False) → ((False ∧ ((p1 → True) ∨ p2)) → ((p5 → p1) → ((p2 ∧ p2) ∧ (p5 ∧ p4))))) ∨ p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983303854114896375321383669546 : (((p1 ∧ ((((p1 ∧ p1) → True) → ((p5 ∨ (True → p5)) ∧ False)) ∧ (((p3 ∨ p2) → (False ∨ ((p4 ∨ p2) ∨ (p3 ∧ True)))) ∧ True))) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791387080587258549674704288718 : (((True → (((p5 ∨ ((False ∧ (p2 ∨ (p4 ∨ ((p2 → p3) ∧ (p3 ∨ False))))) → p4)) → (((p3 ∨ (p2 ∧ p3)) ∧ True) → p3)) ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47055536495036427804701603548 : (((((((((p4 ∧ False) ∨ (p4 → (True ∧ (p5 ∨ (True ∧ (p4 ∧ p3)))))) → p2) ∨ True) → p3) ∨ p1) ∨ (p4 ∧ False)) ∨ (True ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336269496039431743361394558409 : (p1 → (((((False ∧ (p5 ∧ (p4 → False))) ∨ ((p2 → p2) → p5)) ∨ p1) ∧ ((p1 → (p1 ∨ (p4 ∧ (p3 → p2)))) ∨ (p4 ∧ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128130292505725399029856074702 : ((p2 → (((p1 ∧ p3) ∧ (p1 ∨ ((p4 ∨ True) ∧ ((p3 → False) → (p5 → False))))) ∧ ((False → p1) ∧ ((p4 ∨ True) ∧ p5)))) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152732788152469565011041866500 : (((p4 ∨ p3) ∨ (True → (True → (p3 → ((p5 ∨ False) → (p1 → (((p1 → p5) → True) ∨ (p4 → p2)))))))) → (p2 → (p2 ∧ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
theorem thm_5_vars_306045016370668555539945036284 : (p1 ∨ (((p5 ∨ (p5 ∨ p4)) → p5) → ((((p3 → p4) ∧ True) → p2) ∨ (((p4 → ((False ∨ (p4 ∧ p4)) ∨ False)) ∨ p1) ∨ (p4 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475926968336919563705798796561 : (((((p2 ∨ (p2 ∧ (((False → False) → False) ∨ p3))) ∨ True) ∨ ((((p2 ∨ True) → ((True ∧ p2) → p4)) → (p2 ∧ p3)) ∧ (p1 → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249109599543532375879430837722 : ((p4 ∨ p2) ∨ (((True ∧ (p5 ∧ p1)) ∧ ((((p4 ∧ False) ∧ p4) ∧ True) ∧ ((((p5 ∨ (p4 → p3)) ∧ p2) ∧ (p4 ∨ True)) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343578900694081452091947659442 : (p2 → ((False → False) → (p1 ∨ (((p4 ∨ p2) → ((False → True) → p2)) ∧ (False ∨ ((p1 ∨ ((True → (False → p2)) → p1)) ∨ (False ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313322271757455826487096001499 : (p3 ∨ ((p3 ∨ (((False ∧ (p2 ∧ p5)) → (p1 ∨ p5)) → (((((p3 ∧ p3) → (p1 ∨ p3)) → p5) ∨ (p4 → (False ∨ p4))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612958950930648020852219120880 : (((((p2 → (p5 ∨ ((((p4 ∧ (p4 ∨ p2)) ∨ p4) → p5) ∧ (((p2 ∧ ((p5 → p2) ∧ p5)) ∧ False) ∧ True)))) ∨ (p2 ∧ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_134077994208396860077766698305 : ((((((p4 ∨ False) ∧ ((((p5 → True) → ((p2 → p3) → False)) ∧ p4) ∨ p4)) → ((True ∨ True) → p4)) → p5) ∨ p4) ∨ (p4 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791305710314360019702147789432 : (((True → (((p4 ∧ (True → (((p3 ∨ (p5 ∨ (p1 ∧ ((p3 → (p4 ∨ p2)) → (p3 → False))))) → (p4 ∨ p3)) ∨ p2))) ∨ True) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306439989628703535597902193491 : (p1 ∨ ((False ∨ p4) ∨ (((p1 → ((p5 ∨ ((p4 → False) ∧ False)) → p2)) ∧ (False ∧ False)) ∨ (((((p3 ∧ False) ∧ p4) ∧ True) → p4) ∨ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257293607680593699063140244691 : ((p2 ∨ p3) → (True → ((p2 ∨ ((p5 ∨ (((p3 ∧ False) ∨ (False ∧ True)) → p3)) → (((p5 ∨ True) → p2) ∧ ((p5 → True) ∨ True)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313288254442286033474329993080 : (p3 ∨ ((p4 ∧ (((True ∧ False) ∨ (p3 ∨ ((p3 → True) → (False ∧ p5)))) → ((((p1 → False) ∧ (p4 ∧ p3)) → p2) ∨ (p1 ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319030261256410411365339624846 : (p4 ∨ ((((p2 ∧ p4) ∨ ((((p5 → p5) ∧ p3) ∨ p5) → (True → ((True ∧ p2) ∨ (p2 ∧ p2))))) ∨ False) ∨ ((p2 ∧ False) → (p1 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172900573911663342126547541270 : ((p2 ∧ (((((False ∧ p4) ∧ ((True ∧ (False → p4)) → False)) → p2) ∧ p1) → p4)) ∨ ((p1 ∧ False) → ((p5 ∨ p5) ∧ (True → (p3 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594367593637105996508921877841 : (((((((False ∧ p1) ∨ True) → ((p3 ∧ (((p4 → (True ∨ p5)) ∧ p1) ∧ p3)) → p5)) ∧ ((p4 ∨ (p3 → (p2 → p1))) ∨ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37517009901743744369345454995 : (((((p4 ∨ p4) → (p4 ∧ (p4 ∧ (p3 ∧ ((p1 ∨ ((p5 ∨ (False ∧ ((p2 ∧ p2) → (p1 → p3)))) ∨ p5)) ∧ p2))))) ∨ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54553922396111483326707502892 : (((p2 ∧ (((p3 ∨ (False ∨ p1)) → p5) ∨ p3)) ∨ (((((p1 ∧ ((p3 ∧ (p1 ∧ p3)) ∨ (p4 ∨ p5))) ∨ p2) → p4) ∧ p2) → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ ((p3 ∧ (p1 ∧ p3)) ∨ (p4 ∨ p5))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37656730403453323815133629407 : ((((((((p5 ∨ p3) ∧ ((True ∧ False) → p2)) ∧ (((p2 ∧ p2) ∨ (p5 ∨ True)) → (p4 → True))) ∨ (p5 ∧ p4)) → p3) → p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677765969247959790541750676885 : (((((p2 ∨ (((p3 ∨ (p3 → False)) → ((p3 ∧ (p2 ∧ (True ∨ False))) ∨ (p2 ∧ p1))) ∨ p4)) → p2) ∨ (p2 ∨ ((p4 ∧ False) → False))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336106168433234844679270503857 : (p1 → (((((p4 ∧ (p5 ∨ (((p5 → (p1 ∧ False)) → (p4 ∧ (p3 ∨ (p5 ∧ (p3 ∨ p3))))) ∧ p1))) → (True → p5)) ∧ p3) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63335626691950770448476085628 : ((p5 ∧ ((p2 → True) → (True → (((False → (True → p5)) ∨ ((p1 → p2) ∨ (True → (p3 ∧ (((p4 → True) ∧ p3) ∨ p4))))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324094608173254423312431377482 : (p5 ∨ ((True → (((p3 ∨ False) ∧ False) ∧ (((p1 ∨ p1) ∨ False) ∨ False))) ∨ ((p5 ∨ True) → (p2 ∨ (p4 → ((p4 ∧ True) ∨ (p1 ∧ False))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244780083642185156583401220925 : ((p1 ∧ False) ∨ (p2 ∨ ((True → ((False ∨ p2) ∨ (p4 ∧ (True ∨ (((p1 → (p2 ∨ ((True → (p5 → p3)) ∧ True))) → p5) ∧ p2))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304103823862785973704255919670 : (p1 ∨ ((p1 → (((True → ((p1 ∧ (p1 ∧ p4)) ∨ (p2 ∧ p2))) ∧ (p4 → p2)) ∨ ((p1 ∨ (True ∧ ((p3 ∧ p4) ∨ p5))) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321477247052124568888688585352 : (p4 ∨ (p1 → (((p3 → p1) → ((True ∧ ((((False ∧ (False ∨ p3)) → p1) ∨ p1) → (((p5 → p5) → (p5 ∧ p1)) ∨ p2))) ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208263908550253159537161286171 : (((p5 ∧ p3) ∧ (p1 ∨ (p2 ∧ p1))) → (False ∨ (((p4 ∨ ((False ∨ (p2 ∧ True)) → (p1 → ((True → p4) ∨ (p1 ∨ p3))))) ∨ p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712681680097227628459193492159 : (((((p4 ∨ p3) ∧ (p4 → (False ∨ False))) ∨ (((((False ∨ p3) → ((False ∨ p1) ∨ True)) → p5) → (p2 ∨ p2)) ∨ (p5 → (p5 → True)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326938174991091317627555923656 : (True → (((((p4 ∧ p1) ∨ (((((p3 ∧ p5) ∨ p2) ∧ False) ∧ False) ∧ (p3 ∨ ((True ∧ (False ∨ p4)) ∨ p5)))) ∧ True) ∧ (True → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671486081692836880915850657028 : ((((p3 → (((p1 ∨ ((((False ∨ p4) ∨ p2) ∨ p3) ∧ True)) ∨ ((((p4 → False) → p4) → True) → p1)) ∧ p4)) ∨ (p2 ∧ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45103280721287832587104069901 : ((((p1 ∨ False) → ((((p3 ∧ (p1 → (p1 → p5))) ∧ (False ∨ p2)) → p3) ∨ ((True ∧ (p5 ∧ (False → (True ∧ p2)))) → True))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25530653237228468287053197760 : (((p3 ∨ (p2 ∧ p4)) → (True ∧ ((p3 ∧ ((False ∧ p3) ∧ p4)) ∨ ((p1 ∧ False) → ((p4 ∨ p1) ∧ (p5 → (p5 ∨ (p4 ∧ p2)))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h12.left
    let h17 := h12.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191223000035265772034181265425 : (((False ∨ (p2 ∨ p4)) → ((False → p3) → (p1 ∧ p4))) ∨ ((p1 → p1) ∧ (((p4 ∧ False) ∧ p3) → (p3 ∨ (((p5 ∧ p1) ∧ p2) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53385125834663988189273653694 : (((((p1 → True) → (((p3 ∧ p1) ∧ p2) → (p5 ∧ p4))) → p5) → (p4 → (p5 ∧ (((((p4 ∧ p1) ∨ p2) → p3) ∨ True) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173190093219265606376133180546 : ((p4 ∨ (p2 ∨ ((p2 → False) ∨ (p4 ∨ (p1 ∨ (True ∧ (p2 ∧ (False ∨ p5)))))))) ∨ ((True ∨ (((p5 ∧ (False ∨ True)) ∧ p3) ∨ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262520443824523383853385551926 : (True ∧ ((p5 → (p1 ∧ ((((p4 ∧ (False ∨ (p3 ∧ (p4 ∧ (False → p2))))) → (p4 ∨ True)) → ((False ∧ p1) ∨ p2)) ∨ (p3 ∨ True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259863451262693993318430740660 : ((p1 → p4) → ((((False ∨ (((p4 ∨ ((True → p5) ∧ (p5 → p1))) ∧ p2) ∧ p2)) ∨ False) ∧ ((False ∨ True) ∨ (False → (p1 → p3)))) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h12
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
            have h23 : p5 := by
              -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
              have h24 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h18, we can now drive its conclusion.
              let h25 := h18 h24
              -- One of the premise coincides with the conclusion.
              exact h25
            -- We have shown the premise of h19, we can now drive its conclusion.
            let h26 := h19 h23
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h27 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h26
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h28 := h1 h27
            -- One of the premise coincides with the conclusion.
            exact h28
        case inr h29 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h30 : p5 := by
            -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
            have h31 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h18, we can now drive its conclusion.
            let h32 := h18 h31
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h33 := h19 h30
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h34 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h33
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h35 := h1 h34
          -- One of the premise coincides with the conclusion.
          exact h35
  case inr h36 =>
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691349237877924409003874559395 : (((((p2 → (True ∧ True)) ∨ (((p2 ∨ (p3 ∧ ((p1 ∨ p2) ∧ p2))) ∨ p2) ∨ p4)) → (p1 → ((False ∨ (p5 ∨ (p2 ∨ p1))) ∨ p2))) ∨ p3) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
          cases h11
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49111865966008201500889977239 : ((((((False ∨ False) ∧ ((p5 ∧ ((p1 → (False ∨ p5)) ∨ p2)) ∨ p1)) ∨ p1) ∨ ((True ∨ p3) ∧ (p1 → p2))) ∨ (p3 ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52902450355848932928564762077 : (((False → (((p5 ∧ (p4 → (True → (True → False)))) ∧ p4) ∨ (True ∧ False))) → (p3 ∨ (p3 → (True → ((p2 → p4) ∨ (p2 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141424336406998800147288908234 : ((((True ∧ p5) ∧ p5) ∧ ((p4 ∧ True) → (p1 ∧ ((p4 → (p4 → p1)) ∨ (p1 → ((p4 ∨ p1) → (False ∧ p4))))))) → ((p1 ∧ p4) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52263151944966583693605772162 : (((p4 ∨ (p3 ∧ (p3 ∨ (((p3 ∨ (p5 ∧ (p2 → True))) ∨ (p3 → p4)) → False)))) → ((p1 → (((False ∨ False) ∨ p3) → False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161483619634600883430391950905 : ((p3 ∧ (p4 ∨ (p3 ∨ (p5 ∧ (((p5 ∧ (p5 ∧ ((p5 → (p5 → p2)) → p5))) → False) ∨ p5))))) → (p5 ∨ (p2 → ((False ∧ p1) ∨ p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
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
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46497392691280392003245388705 : ((((p1 ∧ (True ∨ False)) → ((((p2 ∧ (p4 ∧ ((p2 → p1) → p2))) ∨ (True → False)) ∨ p2) ∧ ((p2 → False) ∧ p3))) ∧ (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184471351343749098757068562935 : ((((True → (((p3 → p3) ∨ False) → p5)) ∧ p5) ∨ (p3 ∨ False)) ∨ ((p1 → (p3 ∨ p5)) ∨ ((False ∨ False) ∨ (p3 → (False → (p2 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249957529017228825416564143567 : ((True → p2) ∨ ((((((p3 ∧ (True ∧ ((False ∨ p5) ∧ False))) → ((((p4 → (p5 → p3)) ∧ True) → p1) ∨ p2)) ∨ p3) ∨ p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172333919256685644939867777976 : (((((p3 → True) → p5) → (True ∨ p3)) ∧ (((False ∧ (p2 → p3)) ∨ False) ∧ False)) ∨ (p3 → ((p3 → (p1 ∨ p3)) ∨ (p4 → (p4 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37051399605752166213580327522 : (((((((p1 ∧ ((p3 ∧ (True → ((((p5 ∨ (p4 ∨ False)) → p5) ∨ False) → p2))) ∧ (p4 ∧ p3))) → p3) → p2) ∧ p5) ∧ True) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713316897854664666037858328106 : ((((p5 ∨ (p3 ∧ (p5 ∧ (p5 ∧ p1)))) ∨ ((p2 → (((((True → False) ∧ True) ∧ False) ∨ (p3 ∨ ((p3 ∧ p4) ∧ p4))) → p2)) ∨ False)) ∨ p4) ∧ True) := by
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769786923991153993788669596889 : (((p5 ∧ (p3 ∨ ((p3 ∨ p5) ∨ (p5 ∧ (((p5 ∧ (((p4 ∨ p3) ∨ (False → p2)) → (p2 ∨ p3))) → (p4 ∧ (p5 ∧ True))) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154439474983692837610999016318 : ((((p2 ∨ ((True → ((p5 ∨ (((p1 ∨ False) ∧ (p4 → p5)) ∨ p2)) ∧ p5)) ∨ True)) → p3) → p3) ∧ (p3 ∨ ((True ∧ p3) ∨ (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((True → ((p5 ∨ (((p1 ∨ False) ∧ (p4 → p5)) ∨ p2)) ∧ p5)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265060825529853323998060722772 : (True ∧ (True ∧ ((p2 ∨ False) ∨ (((((p1 → ((False ∨ (p1 ∨ False)) → ((p4 ∧ ((p1 ∧ p5) → p5)) ∧ p2))) → p2) ∧ p3) ∨ True) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52005909041015112986688546309 : (((p2 ∧ ((((p3 → (True ∧ ((True → True) ∨ p1))) → p5) ∧ p4) ∨ (p5 ∨ True))) ∨ (p4 → (p2 → (((p3 ∨ p1) → p2) ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213820326396797174166649759831 : (((p4 ∧ (p5 ∧ False)) ∨ False) ∨ ((p5 → ((p5 ∧ p1) → ((p3 ∧ (p5 ∨ (True ∨ p1))) → (p4 ∧ p4)))) ∨ (p5 → ((p2 → False) → True)))) := by
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
theorem thm_5_vars_166312409391979092565549116996 : ((p5 ∧ ((((p2 → (False ∧ False)) ∨ (False ∨ ((False → (p1 ∨ p3)) ∨ p5))) → False) ∨ False)) ∨ ((((p4 → True) → True) ∨ (True → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119440003570617028789205696093 : ((p4 → ((((((p2 ∨ (False ∧ p2)) ∨ p5) ∨ (p2 → p3)) → p3) → (p3 ∨ False)) ∨ (((True ∨ p2) ∨ (p3 ∧ p2)) → True))) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234834674821061986289539194212 : ((p5 → (p3 ∨ False)) → ((p4 ∨ (((False → True) ∨ p1) → (((p1 → ((p4 → p3) ∨ ((p2 ∨ p5) ∨ False))) ∨ p3) ∨ True))) ∨ (p3 → False))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46159538896034074672652152403 : (((((((False ∨ ((p4 ∨ p5) ∨ p3)) ∨ p3) ∨ (((p2 ∧ p5) ∧ p2) ∧ p3)) ∧ ((p5 → False) ∨ (p5 ∨ p3))) → p1) ∧ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313962237067317476315411207397 : (p3 ∨ (((True ∧ ((p3 → (p2 ∧ ((True ∨ p5) → ((False → (True ∨ p2)) → (False → p4))))) → p3)) ∧ (True ∨ (p1 ∨ p2))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41465811837585403175072524610 : ((((False → (((p1 → ((p2 → True) ∨ p5)) ∧ True) ∨ (True ∨ p4))) ∧ (((p4 → (p2 ∧ p1)) → (False ∧ (p4 ∧ p2))) ∨ p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337528915443272170597369258717 : (p1 → ((((((((p3 → False) ∧ p3) → (p4 ∧ False)) ∨ p4) → p5) ∧ ((p3 → p1) ∨ False)) ∧ (p2 ∧ True)) ∨ ((True → (False ∧ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596577934073716080465417963371 : (((((False ∨ ((p3 ∧ (p3 ∨ p3)) → (p1 → p1))) → ((((((True ∨ p4) → True) ∨ p1) → p4) ∧ True) ∨ ((True ∨ p4) ∨ p4))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38898361718721976007048781570 : ((((True ∧ (p1 ∧ p4)) ∨ (True → (((((False ∧ (True ∨ (p4 → p5))) → p3) ∨ (p4 → (p3 ∨ (True ∨ p1)))) ∧ p1) ∧ False))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51189115544820010871256382500 : (((((((p1 → p4) ∧ p5) → p1) ∨ (((p4 ∧ p2) ∨ p2) → False)) ∨ (p5 ∨ (p2 ∧ p4))) ∨ (p2 ∨ (p1 ∨ ((p3 → p3) ∨ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224715573610303525290955257279 : ((p3 → (p2 → p3)) ∧ (((p2 ∧ ((p5 → False) ∧ ((p1 ∨ (True ∨ p4)) → p5))) ∧ (p3 → p3)) → (p5 ∧ (p5 ∧ (p1 ∧ (p5 ∧ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- One of the premise coincides with the conclusion.
  exact h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h3.left
  let h21 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
  have h26 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h25, we can now drive its conclusion.
  let h27 := h25 h26
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h28 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h27
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h29 := h24 h28
  -- False on the left can always be used.
  apply False.elim h29
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h30 := h3.left
  let h31 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h33.left
  let h35 := h33.right
  -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
  have h36 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h35, we can now drive its conclusion.
  let h37 := h35 h36
  -- One of the premise coincides with the conclusion.
  exact h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h3.left
  let h39 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h41.left
  let h43 := h41.right
  -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
  have h44 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h43, we can now drive its conclusion.
  let h45 := h43 h44
  -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
  have h46 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h45
  -- We have shown the premise of h42, we can now drive its conclusion.
  let h47 := h42 h46
  -- False on the left can always be used.
  apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336240707204824460949908408460 : (p1 → ((((((p3 → p5) ∧ (False → (((p5 → (p5 → (p4 ∧ True))) → p1) ∨ False))) ∨ True) → p5) ∨ (p2 → ((p5 → p2) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305779023499101282064494971908 : (p1 ∨ ((True ∧ (True → (((p5 ∨ True) ∧ p3) → False))) ∨ ((((((p2 ∧ p4) ∨ p3) ∧ p3) ∨ False) → p1) ∨ (p4 ∨ ((p5 ∧ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248894733792032391696154096421 : ((p3 ∨ p5) ∨ ((True ∨ (False ∨ True)) ∧ (((((((p4 ∨ True) ∧ (p3 → (p3 ∧ True))) ∧ (p1 → p2)) ∨ p2) → (p4 ∧ p5)) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592830723462051414424218402086 : ((((((((((p4 → p1) ∧ True) ∨ p5) ∧ True) ∧ (False → p4)) ∧ (False ∧ (False → (p4 ∧ (p2 ∨ True))))) ∧ (p3 ∧ (p4 ∧ p5))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638612663312886348265955984964 : (((((p2 → ((p1 → p5) → (False ∨ p5))) ∨ (True → (p5 ∨ (p3 ∧ ((False → ((p1 → (p3 → False)) ∨ (p4 → p1))) → p3))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60309435371542036216705762670 : (((p1 → p3) → ((False ∧ p3) ∨ ((p5 ∧ ((p3 → False) ∨ ((True ∨ ((p4 ∨ p2) → (p5 ∨ p3))) ∨ ((p2 ∨ True) ∨ p2)))) ∨ True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694862622823751722215697024084 : ((((p2 → (p1 ∨ ((p2 → (p5 ∨ ((p4 ∨ p1) → (p5 ∧ p5)))) ∨ True))) ∨ ((p2 ∨ ((p5 → (p2 → p3)) ∧ p2)) ∨ (True ∧ p5))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52609975960979063345327342860 : ((((False ∧ (True ∨ (True ∨ p2))) ∨ (((p3 → True) ∧ p4) ∨ (False ∨ p1))) ∨ (False ∨ (False ∧ (p4 → ((False ∨ p3) ∧ (p2 → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168485321608577075952197619194 : ((True ∧ (((True → (p4 → False)) ∧ p1) ∧ ((False ∧ (p4 ∧ True)) → (False ∨ (p5 → p5))))) → ((p2 ∨ ((p2 ∨ p4) ∧ (p2 ∨ p5))) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950365542997183794392634721621 : (((((p4 → p5) → p1) ∧ (p1 ∧ (p4 → (False ∧ (((True ∨ (p3 ∧ ((True ∧ p2) ∨ (p3 ∧ (p3 ∨ p4))))) ∨ p5) ∧ (p3 ∧ p2)))))) → p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



