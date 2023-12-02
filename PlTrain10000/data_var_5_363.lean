variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336239585149189045900617081868 : (p1 → (((p2 → (False ∨ (p3 ∧ ((((False ∨ (p5 → p5)) ∧ p1) ∧ p5) ∨ (p1 ∧ (p4 ∧ p2)))))) ∧ (((p4 ∧ p4) ∨ p4) → p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655001791783089275891899632981 : ((((((False ∧ p5) ∨ (p3 → ((((((p4 → p2) ∨ (p5 → p5)) → p3) → (p4 ∨ (p5 → p2))) ∧ p4) → True))) → p2) ∨ (True ∨ p2)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_231318623682463778010520556159 : (((True → False) ∨ p5) → ((((p5 ∨ (p3 ∧ (((p1 ∨ (p5 ∧ (((p2 ∧ p2) ∧ p2) ∨ p4))) → True) ∧ True))) ∨ p2) ∨ p1) → (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115216891523364148410136912703 : (((False → (((((False ∧ True) ∧ True) ∨ p3) → False) ∨ p5)) ∧ ((p4 ∧ ((p3 ∨ (p4 ∧ False)) ∧ False)) ∧ (True → (True ∨ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138730566333043314700521533623 : ((((p5 ∧ (False ∨ (p5 → False))) ∧ ((((True → p2) ∧ (p3 ∧ p2)) ∨ (p5 → ((False ∨ p5) ∧ p4))) ∧ p4)) ∧ p5) → (p1 ∨ (p4 → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h20 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h21 := h9 h20
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115198378938533240226915181776 : ((((p2 ∧ p4) ∨ ((p5 ∨ (p1 ∨ (p2 → p5))) ∧ p4)) ∧ ((p1 ∧ p3) ∧ (False → (p4 ∨ ((p3 ∨ p3) → (True ∧ p3)))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166552977246899650845001263950 : ((p5 ∨ ((((p5 ∨ p2) ∧ False) ∧ p5) ∨ (((p1 ∧ (p2 → p4)) ∨ p4) ∨ (True ∨ p1)))) ∨ ((((p5 → p3) ∨ (False → p4)) ∧ True) ∧ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346313819395134183869608145786 : (p3 → ((((False → ((((p3 → p2) ∧ p3) ∨ p4) ∨ ((p3 ∨ (False → ((p3 ∨ False) → p5))) ∧ True))) → p5) ∧ (p1 → p4)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57307200928985213572664922918 : (((True ∧ (p1 ∧ p3)) ∨ (((((True ∧ p5) ∨ ((True ∧ (p4 → (((True → p3) ∨ (p4 → True)) ∧ p4))) ∧ True)) ∨ p1) ∨ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228043268492172319758131760674 : ((p4 ∧ (True ∧ p1)) ∨ (p4 → (((((((p3 ∧ p3) ∧ True) → (p2 ∨ p4)) ∧ (p3 ∧ p5)) → (False ∨ ((p3 → p2) ∨ p3))) ∧ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219786584361180750469799589151 : ((p2 → (p3 ∧ (False ∨ p5))) → (((((p5 ∨ p3) → (p5 → (p5 ∧ (p2 → p4)))) ∨ p5) ∨ False) ∨ ((p2 → p2) ∨ (p2 → (p2 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42860663076551676547564912189 : (((p2 → ((False ∧ ((p5 ∧ ((p5 ∨ p2) → p5)) → True)) ∨ (p5 ∧ ((p1 ∨ (False ∨ (((p4 → p5) ∧ p1) ∧ p1))) ∧ p4)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300718721722462010749960830839 : (False ∨ ((((False → p5) → ((False → p2) ∨ p2)) → (((True ∨ (p2 ∧ p2)) ∨ (p1 ∨ False)) ∧ p1)) → (p1 ∨ (True → (p2 ∨ (False ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p5) → ((False → p2) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49381534481694258024859155564 : ((((((False ∨ p3) ∨ ((((p1 → p5) → (False ∧ ((p2 ∧ (p1 → p2)) ∧ p4))) ∨ p5) → p3)) ∧ p3) ∧ p1) → ((p4 ∧ p1) → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114137022762324429792706944064 : ((((((p5 ∨ p5) ∧ ((p5 → (True ∨ p2)) ∧ (p4 ∨ True))) ∧ (p4 ∨ (p4 ∨ (p2 ∧ p5)))) ∧ p2) → (False ∨ (True → False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177291624527670455432409760596 : ((p1 ∨ ((False → False) ∧ ((p2 ∨ True) ∨ (p5 ∧ ((p5 ∧ False) ∨ p3))))) ∧ (((p3 ∨ (p3 ∨ p1)) → p5) ∨ (((p4 ∧ p1) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158118801553237763344420232406 : (((p1 ∨ (p3 ∧ (p2 ∨ p5))) ∧ (((True ∧ p4) ∨ ((p5 → True) → False)) ∧ ((p4 → p1) ∨ p4))) ∨ (((p2 ∧ False) ∧ False) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340209437541967375083501264051 : (p1 → (p5 → (((((True ∨ (((p4 ∧ p4) ∨ p4) ∨ (p4 → ((p4 ∧ ((p3 ∧ p5) → p1)) → (p1 → p2))))) → p5) ∨ p1) → p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171915600681943400506681937412 : (((p3 → (p2 ∧ ((p5 ∧ p1) ∧ ((p3 ∧ (p4 ∧ False)) ∧ (p4 ∨ p2))))) → p5) ∨ ((p4 ∨ (p4 ∧ ((p3 ∧ p5) ∧ p4))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616344534773156043220154536510 : (((((p1 ∧ (p5 → (((True ∨ p5) ∨ ((p3 ∧ False) → False)) ∧ p3))) ∨ (((p1 ∨ p5) → (False ∨ (True ∨ (p1 ∨ p3)))) ∧ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172340169164554324468082523917 : (((p1 ∧ (False → (False → (p2 ∨ p4)))) ∧ ((p4 ∧ (p4 ∨ (p3 ∧ p3))) ∧ p3)) ∨ (p5 ∨ ((p5 → (p2 → (p1 → (True ∧ p5)))) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721333863326655376458529519994 : ((((True ∧ ((p1 → True) ∧ p1)) → ((((p3 → p4) ∧ (p4 ∨ (p3 → p4))) → (((p4 ∨ p1) → ((p5 → True) → p1)) ∧ p3)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111297030033710607873298094891 : (((True ∧ ((((p2 → (p1 → p3)) ∨ p4) ∨ p1) → ((p3 ∧ ((p2 → (p2 ∨ (p2 ∧ (p1 ∨ p5)))) ∧ p1)) → p4))) ∧ p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791041351308006475362585330564 : (((True → (((((((((True ∨ p5) → p3) ∧ p3) ∨ (p2 ∨ p1)) → p1) ∧ (p3 → ((p3 → (p2 ∧ p5)) ∧ p1))) → p3) → p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185828711405913000798301851573 : (((((True ∧ True) ∨ (p5 ∨ (p2 ∧ (True → p2)))) ∧ p4) ∧ p3) → (((((p3 ∨ p1) → p5) ∨ p5) ∨ p3) ∧ ((p4 → (p1 ∨ p4)) ∨ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2668410556930563725980025499 : ((p3 ∧ ((True ∧ (p2 ∨ p1)) ∨ p2)) ∨ ((p4 ∧ p3) → (p2 ∨ ((((False ∧ True) ∨ p1) → (p4 ∨ (p3 ∨ (p1 ∨ True)))) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314418359977171633654124455342 : (p3 ∨ (((p1 ∧ (((True → (p1 → p5)) → (False ∨ p1)) ∨ ((True → p4) → p3))) ∨ ((False → False) ∨ p2)) ∨ (((p4 → p2) ∧ p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_179076320029921767488889922475 : ((True ∧ ((p5 → True) ∧ (((True ∨ p5) ∨ p3) ∧ ((p5 ∨ p4) ∧ True)))) ∨ ((True → False) → ((((p3 ∨ p1) ∧ (p3 ∧ p2)) ∧ p1) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155725440774221690304043994069 : (((p4 → p2) ∨ (((True ∨ (True ∨ p5)) ∨ p1) → (False ∨ (p5 → ((p2 ∨ p4) ∨ (False → p2)))))) ∧ (False → (p5 ∧ ((p5 ∨ False) ∨ p4)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
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
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h16
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358187453194221371439195592106 : (p5 → (p3 ∨ ((p5 → (p5 ∨ p2)) → (((False → (((False ∨ (True → p2)) → ((False ∨ p3) → p2)) ∧ p1)) → p1) ∨ (p3 → (p3 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118199085271196673607710368477 : ((False ∨ (p1 → ((False → (True ∧ ((p2 ∨ p5) ∧ p3))) → ((p4 ∧ (((p2 ∧ False) → ((p1 ∧ p1) ∧ p3)) ∧ False)) ∧ False)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147348140063902564700823822153 : ((((p3 → (p3 → (p4 → (True → (((p2 ∨ (False ∨ p3)) → p4) ∨ (p5 ∧ p2)))))) → (p2 ∨ p1)) ∨ True) ∨ (((p1 → False) ∨ True) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207622824247761085581751531651 : ((((p2 ∨ (p4 ∨ True)) → True) → p1) → ((p4 ∨ (((((False ∧ False) ∨ p3) → False) → p1) → (p2 ∧ ((p1 ∧ (p2 ∨ p4)) ∧ False)))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((((False ∧ False) ∨ p3) → False) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((p2 ∨ (p4 ∨ True)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h7
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315278113692037162825356002894 : (p3 ∨ (((p2 ∨ (True ∧ p3)) ∧ p2) → (((((p3 → True) ∧ (p5 ∧ p2)) ∨ True) ∧ (((False ∧ False) → True) ∧ (True → (False ∨ p2)))) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338228760738869403122340405731 : (p1 → (((p4 ∨ (True → (p2 ∨ p5))) ∨ p2) ∨ (((True ∧ p4) → (((True ∧ (p3 → False)) → p3) ∧ (((p5 ∧ p2) ∧ p2) ∨ p1))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136413613365358539915199758349 : (((((p5 → True) → p4) ∧ True) → (((p2 ∨ (((p4 → p2) ∧ (p2 → (p4 ∧ False))) ∨ (p5 ∨ p1))) ∧ p2) ∨ False)) ∨ (p5 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200099935551925021818746504624 : ((((p2 → True) → p2) ∧ (p3 → (True → True))) → (p2 ∨ ((True ∧ ((True → p3) → (((True ∨ p5) → ((False ∨ p1) → True)) ∨ True))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681566609952255401822052406592 : ((((False → (p4 → (((p2 ∨ (p4 ∧ (p3 → ((p2 → p1) ∨ True)))) ∨ (p2 → (p3 ∧ False))) → p3))) → ((p2 → True) ∧ (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175357400006545192305009058639 : ((p5 ∨ ((p3 ∨ p5) → ((p2 ∨ (p1 → (((p5 ∨ True) → False) ∨ p5))) ∧ False))) → (((p3 ∨ ((p4 → (False → p1)) ∨ p4)) → p4) ∨ True)) := by
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
theorem thm_5_vars_315496378871947691971709856444 : (p3 ∨ ((p5 ∧ (p3 → p1)) → (p3 ∨ ((p5 → (p5 ∧ (((p1 → (False → (True ∨ p1))) → (p1 → (p5 → p1))) ∨ (True ∨ p3)))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337117313172572456036976956246 : (p1 → (((p2 ∨ p5) → (((((p4 → (((True ∨ (False ∨ (p2 ∧ False))) ∨ True) ∧ p2)) ∧ p2) ∧ p3) ∧ (p5 ∨ p5)) ∨ True)) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_191542798814053924187159750457 : ((p1 ∧ (((p5 → True) → (p5 ∨ p1)) ∧ (p5 → False))) ∨ (((p2 ∧ (p1 ∧ p1)) → True) ∨ (p5 ∧ ((True ∨ p1) ∧ (True → (True → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159457764613680204876052584805 : ((((((((p4 → p5) ∧ p5) → True) → (p5 → True)) → p1) → (((p1 ∧ p4) ∧ p3) ∨ p4)) ∧ p1) → (p5 → (True → ((True ∨ p1) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611922339588030666255875634295 : ((((((((p2 ∨ p5) ∨ (p4 ∨ ((p1 ∨ (False ∧ (p3 ∧ p5))) ∧ (p2 ∨ False)))) → ((p3 ∨ p2) ∨ p5)) ∧ p5) ∧ (p3 ∨ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_259526801494105733159793787629 : ((False → p5) → ((p1 ∨ p4) ∨ (((p5 ∧ p3) → (((p4 ∧ (p1 ∨ (p3 ∧ (True ∧ (True ∨ p5))))) ∧ (False ∧ (p5 ∧ p5))) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612705376897135975808305807276 : ((((((p2 ∧ ((((p1 → (False ∧ p5)) ∧ True) → False) ∨ p5)) ∨ ((((p2 → (p3 ∨ p4)) ∨ p4) ∧ p1) ∧ p5)) ∨ (p4 ∧ False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_68062002037537648609720583605 : ((p2 → (False ∨ (((p5 → (False → p4)) ∧ p3) ∧ ((((((p3 → False) ∧ p2) ∨ p1) ∨ (p1 → p4)) ∧ (p5 ∧ (p4 ∧ p2))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215722487793720432951955924180 : ((False ∨ (p5 ∧ (p2 ∧ p4))) ∨ (p4 ∨ ((((p3 → (p4 → p4)) → p5) ∧ p4) → ((p5 ∧ p1) → (True ∨ (((p2 → p3) → p3) ∧ p1)))))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263898400183148086257063834294 : (True ∧ (((p5 → p2) ∧ (p4 ∧ (False ∨ ((p3 ∨ True) → ((p4 ∨ p4) ∧ p3))))) ∨ ((False → p4) → ((((p1 → p1) ∧ True) ∧ p4) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88968056760690729566545386361 : (((p5 → ((False ∨ False) ∨ p5)) → (p3 ∧ ((((p2 → False) ∨ p2) → p3) ∧ (((p5 → (p3 ∨ ((p3 ∧ p4) ∧ p2))) ∨ True) → False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((False ∨ False) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 → (p3 ∨ ((p3 ∧ p4) ∧ p2))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157987594276112485161053921003 : ((((p5 ∨ (p4 → ((p1 ∧ p3) → p5))) → p2) → ((p5 ∨ ((p5 ∧ p1) → p3)) ∧ (False → p2))) ∨ ((p3 ∨ True) ∨ (p2 → (p3 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208657987924306240646165992748 : ((True ∧ (p2 → ((p4 ∧ p2) ∧ p4))) → ((((((p2 → (False ∧ p3)) ∨ p4) ∨ (True ∧ (p4 ∨ True))) ∨ p5) ∨ ((p1 ∨ p2) ∨ p5)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698889951969875491760754365056 : ((((p2 ∧ ((p4 ∧ (p3 ∨ ((p1 → p1) ∧ (p3 → p4)))) ∧ p1)) ∨ (p3 ∧ ((p5 → p1) ∨ ((p3 ∨ ((True → False) ∧ p4)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39152249144103512301099907119 : ((((p1 ∨ p1) → ((p5 → (((p2 ∨ ((p1 ∧ (p4 → ((p2 ∨ p2) ∧ p2))) → p2)) ∨ True) ∧ p1)) ∨ ((p3 → False) ∨ True))) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54026939321740843311174846175 : ((((p4 ∨ (((p1 ∧ p2) ∨ p2) ∨ p5)) ∧ (True ∨ p3)) → (((p3 ∧ p1) ∧ False) ∨ (p1 → ((True ∧ (p2 ∧ p4)) → (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152136378970548983372526335806 : (((False → ((p5 ∧ (True → (p5 ∧ p4))) ∧ p1)) ∧ ((p1 → p2) ∧ ((((p1 ∧ p2) → p4) ∧ p1) → p5))) → ((p2 ∧ p3) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892054364703810263135579846370 : ((((((p1 → ((p3 ∧ p3) ∧ ((p4 ∨ ((p3 ∨ p3) → p2)) ∨ (p4 ∨ (p4 ∨ (True ∨ p4)))))) → p1) ∨ p1) ∧ (True ∧ (False ∨ p3))) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p1 → ((p3 ∧ p3) ∧ ((p4 ∨ ((p3 ∨ p3) → p2)) ∨ (p4 ∨ (p4 ∨ (True ∨ p4)))))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h8
        -- One of the premise coincides with the conclusion.
        exact h8
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
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h9
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181615413153022629666074875095 : ((p2 → ((p3 ∧ ((p3 ∧ False) ∧ (p2 → p3))) ∧ ((p3 ∧ p3) → p1))) → (((p2 ∧ True) → p4) → ((((p1 ∨ p2) → True) ∧ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134020187339268679648584277410 : (((((p5 ∨ ((((p4 → p1) ∨ p4) → (p2 ∨ (p3 → p1))) ∨ ((p1 → (False → p1)) → p3))) ∧ False) ∨ p1) ∨ p4) ∨ (p2 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659065472797111369907116695160 : ((((p2 → ((p4 → (((p3 → (True → p2)) → (((p3 ∨ p3) ∨ p4) ∨ p1)) ∧ ((p5 → p5) ∧ False))) ∨ (False ∧ False))) ∨ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255678875262471342762911101865 : ((p5 ∧ p5) → (((p4 → p1) ∧ ((True → False) ∧ ((((p3 ∧ (p5 ∨ p5)) ∧ p2) → p3) → (((p5 ∧ p2) ∧ True) ∨ p3)))) ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171981747639544695955943167243 : (((p2 → ((True ∧ (((p5 ∧ (p3 → True)) ∧ p4) ∨ p1)) ∧ p2)) ∧ (False ∧ p1)) ∨ (False → (((False ∧ p5) ∧ ((p1 ∨ p2) → True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307848730848490754837796703906 : (p1 ∨ (p5 → ((((p2 → (True → (((p5 ∧ ((False ∨ (p2 → p2)) ∨ (p1 ∧ p2))) ∧ (p4 ∨ p3)) ∧ p5))) ∧ p4) ∨ (True ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68991767371555819328613653025 : ((p5 → ((((p1 → (p4 ∧ p4)) ∨ (True ∨ (p4 ∧ ((p1 ∧ (((False ∨ True) ∨ True) ∨ (p4 → (p5 → p5)))) → p3)))) → p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39754003992643464454116434920 : (((True → ((((p2 ∧ (True → (((p2 ∧ (p4 ∧ True)) ∨ p3) ∨ p2))) → ((p3 ∨ ((False ∧ p1) → p3)) ∨ False)) ∨ p3) → p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253017147938447963504051374383 : ((True ∧ p3) → ((p1 ∨ ((p2 ∨ (p1 ∨ p5)) ∧ ((False → p5) → (p4 ∧ p2)))) ∨ ((((p4 ∧ p2) ∨ p3) → (p1 ∧ (p1 ∧ p4))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338282177654832042237164889692 : (p1 → ((True ∧ ((p3 ∧ (p5 ∧ True)) → p3)) → (p4 → (((True → p3) ∨ (False ∧ ((p2 ∨ (False ∨ ((p2 → p3) ∨ p4))) ∨ p5))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42844924003196530498594497985 : (((p2 → ((((p2 ∧ ((((p1 ∨ p2) ∧ p4) → p1) ∨ (p4 ∧ (True ∧ (p4 ∨ p2))))) ∧ (p4 → p3)) → (False ∨ False)) ∨ p2)) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150879901269746414273350460254 : (((((p4 → (False ∨ p5)) → False) ∧ (p5 → (p2 ∨ ((p5 → p1) → (p4 → (p2 ∧ (True ∧ p3))))))) ∨ True) → ((p5 → (p5 → p3)) ∨ True)) := by
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
theorem thm_5_vars_197032234929815766081802296567 : ((((p2 ∧ (p5 ∨ p5)) → (p4 ∨ p3)) ∨ p4) ∨ (((p4 → p4) ∨ (p5 ∨ True)) ∨ ((p4 ∧ p4) → (((p3 → (p3 ∧ False)) → True) → p2)))) := by
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
theorem thm_5_vars_173881688028191376737777800426 : (((((p1 ∨ ((p1 → (True → (p1 ∧ (p1 → p2)))) ∧ p1)) → False) ∨ p4) → p1) → (((True → (p4 ∧ p2)) → False) ∨ ((p3 ∧ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136082387685719197209209839226 : (((p4 ∨ ((((p5 ∧ p1) ∨ p4) → p5) ∨ p4)) ∧ ((False ∨ p4) ∧ ((False ∧ p1) ∧ (((p3 → p5) ∧ p4) ∧ True)))) ∨ (True ∨ (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59149094108976947438799123272 : (((False ∨ False) ∨ (((p2 → (((p4 ∨ ((False ∨ (p3 ∧ p2)) ∧ p3)) ∧ (p1 ∧ p1)) ∧ True)) → (p1 ∨ (False ∨ False))) ∨ (True ∨ p4))) ∨ p3) := by
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
theorem thm_5_vars_344420135333859868788701531558 : (p2 → (p5 ∨ (((p1 ∧ p3) ∨ (((p2 → (p1 → (((((False ∨ p4) ∨ True) ∧ p5) → p2) → (False ∧ False)))) ∧ p3) ∨ p1)) ∨ (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234342238533289130669315094623 : ((p1 → (True ∨ p3)) → ((((p2 ∨ p2) → (False ∨ ((False ∨ p5) → (((p4 ∨ p3) ∧ True) ∨ (p4 ∨ True))))) ∨ (p1 ∨ p3)) ∨ (p3 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135813535693620752684367657856 : (((((p4 ∧ (False ∧ p1)) ∨ ((p3 ∧ p2) ∧ (p5 → p1))) ∧ p4) ∧ ((((p5 → False) → True) → False) → (p2 ∨ p2))) ∨ (p2 → (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115650415174959848897397330509 : ((((p5 ∨ ((False → p2) ∧ True)) → False) ∨ (p2 → (p4 ∨ ((((p1 ∨ (p3 ∧ p1)) ∧ (p2 → p2)) ∨ p3) → (p4 → True))))) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356207433460095113983520031217 : (p5 → ((p2 ∨ (((True ∨ p1) ∨ (p4 ∧ p3)) ∧ ((p1 → False) → (((p5 ∨ True) ∨ p1) → False)))) → ((((p4 ∧ p1) ∨ p3) ∨ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727556999324024843914851186556 : ((((p4 ∧ (p3 → False)) ∨ ((((True → False) ∧ ((((True ∧ True) ∨ True) ∨ ((p1 → True) ∧ (p4 → p5))) → p1)) ∧ p1) ∨ (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328295662934925205114371366006 : (True → (((((False → p3) ∨ True) ∧ p4) → ((((((p2 ∨ p1) → (p2 ∨ p5)) → p1) ∨ p3) ∨ True) ∨ p3)) ∨ ((p1 ∨ p3) → (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102869462490065760030581609059 : ((((p3 → (((p5 → ((((p5 ∧ (p1 ∨ True)) ∧ p2) ∨ True) → p4)) ∨ p5) ∨ (p2 → (p4 ∧ p1)))) ∨ (p2 ∨ p2)) ∨ True) ∧ (p1 ∨ True)) := by
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
theorem thm_5_vars_137756849008659741852677895874 : ((p2 ∨ ((((p5 ∧ p1) → ((p3 → (False → ((False ∧ (p4 ∧ p4)) ∨ (True ∧ p3)))) ∨ p4)) → (True → p1)) → p2)) ∨ ((p5 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68816136820452680901553705989 : ((p4 → ((p3 ∧ (p2 → False)) ∧ (p3 ∨ ((p5 ∧ ((((p5 → (p2 ∧ p4)) → (((p5 ∨ True) → p5) ∧ p3)) ∨ p2) ∧ p2)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669722270161550920762739071417 : (((((((p5 ∧ p2) ∧ (p2 ∧ p4)) ∧ ((p1 → p5) → ((p5 ∨ p3) ∧ p3))) ∧ (p4 ∨ ((p2 ∨ True) ∧ False))) ∨ (p2 → (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210193633251834789220252158227 : ((((False → p3) ∨ p5) ∨ True) ∧ (p1 ∨ (((False ∧ (((True ∧ (p4 → (p1 ∧ p4))) ∨ ((p2 → p3) ∧ p5)) ∧ (p4 → p5))) ∧ p5) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337383333606575834081055585177 : (p1 → (((p3 → p3) → ((False ∧ p3) ∧ ((False → p5) ∨ ((p5 → p5) ∧ (p5 ∧ ((False ∧ p4) → (p3 → p4))))))) ∨ ((True → p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629859301026978648943366642236 : ((((((p4 ∨ ((p3 ∧ p4) → ((p5 ∧ (p4 ∧ p5)) → p4))) → ((p4 ∨ p4) → ((((True ∨ p4) ∧ p4) → p4) ∧ True))) ∨ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150179022036045016506023013157 : ((p1 → (p2 ∨ ((p5 ∧ (p1 ∧ ((p5 ∨ p3) ∨ p1))) ∧ (((False ∨ ((p4 → p2) ∨ p3)) ∨ True) → p4)))) ∨ (False → ((True → p5) ∧ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5169128288365258568650385030 : ((((p1 ∧ (p4 ∨ (p5 ∨ ((((p5 ∨ p5) → (p4 ∨ (p3 ∨ p2))) ∨ False) → (p4 ∧ (p2 ∨ (False → (p5 ∧ p3)))))))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609149808653785343460931929850 : ((((((p3 → (p1 ∨ (p2 ∧ p1))) ∧ (p2 ∨ ((((False ∧ (p3 ∧ True)) ∨ (((p3 → p4) ∧ True) ∨ p5)) → True) ∧ p2))) ∨ p2) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165769188418336171048808536581 : ((((p1 ∨ (p4 → p4)) ∨ p2) → ((p4 ∧ (p3 ∨ (True → (False ∧ (True ∧ True))))) ∨ p1)) ∨ ((p3 → True) ∨ (p1 → (p2 ∧ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51224917580130075226887110830 : ((((((p4 ∨ True) ∧ p3) ∨ p3) ∧ ((((p5 ∨ (p1 ∨ (p2 ∨ False))) → False) ∨ p5) → p5)) ∨ (((True → (p5 ∨ False)) ∧ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672665483137994963006188064035 : ((((((True → (p3 ∧ (True → p4))) ∧ (((p4 ∧ ((True ∧ p4) → p5)) → p3) ∧ (p3 ∧ p3))) ∨ (p4 → p4)) → ((p4 ∨ True) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63292645544583861425213913691 : ((p5 ∧ (((p2 ∨ p1) ∧ False) ∨ (p5 → ((((False ∨ ((p2 ∧ (p5 → p2)) ∨ p2)) → ((True → (True → p3)) ∨ p1)) ∧ p1) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181034622047616677747112193949 : (((p3 → False) ∨ (p5 → ((((p4 ∨ p3) → True) ∧ True) ∧ (p4 ∧ p3)))) → (p2 ∨ ((p2 ∨ p1) ∨ ((True ∨ (p2 ∨ p1)) ∧ (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191628110463003069926620060721 : ((p3 ∧ (p5 → ((p1 ∧ ((p4 ∧ False) → p1)) ∧ p1))) ∨ ((((p4 → (p1 ∧ p5)) ∧ p1) ∧ ((False ∧ (p5 → p5)) ∧ (p2 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727320766573297840838791604 : ((p5 ∨ ((p5 ∨ ((True ∧ ((p3 ∧ p3) ∨ (((p2 ∨ p1) ∧ False) → (p2 ∨ False)))) ∨ False)) ∧ (p3 → ((True ∨ False) ∧ p5)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4118294662121328896040025100 : (p3 ∨ ((p2 ∧ p4) ∨ (p4 → (p5 → (True → ((p3 ∨ p3) ∨ ((p5 ∨ ((p2 ∨ p4) → False)) ∨ ((p5 ∧ p4) ∧ (p5 ∨ p5))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167302352710141668995743824073 : ((((((((False → False) ∨ True) → ((False ∧ True) ∧ p3)) ∧ p3) → (True ∨ p4)) → p3) → True) → ((p3 ∨ True) ∨ (((False ∧ p2) ∧ p4) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753424686614450913637922961642 : (((False ∧ ((((True ∨ (False ∧ p1)) ∧ p3) ∧ (p2 → (p3 ∨ (((p3 ∧ ((True → p2) → p3)) ∧ p4) → True)))) ∨ (p3 ∨ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



