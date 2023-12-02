variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624949631971863362609182104738 : ((((p5 ∨ (p1 ∧ (True ∧ (((p4 ∨ p1) ∧ p3) ∧ ((p2 → True) → (True ∧ ((p3 ∨ p4) ∨ ((p4 ∧ (True ∨ p4)) ∨ p4)))))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345364767870394823504416263048 : (p3 → (((((p5 ∧ False) → (((False ∧ True) ∧ (p1 ∨ p3)) ∧ ((p5 → True) ∧ ((p4 → (p1 ∨ p5)) ∨ p2)))) → (p2 ∧ p1)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667831286260666123794348007585 : ((((False ∨ (((p1 ∨ (True ∨ p5)) ∧ (p2 → False)) → ((p3 → False) ∨ (((p5 ∨ p5) ∧ p1) ∨ (False → True))))) ∧ (False ∨ (p2 → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160902142937632625971449040196 : (((p5 ∨ (p2 → (False → p1))) ∨ (((p3 ∧ (p4 ∨ p1)) → True) ∨ (p4 ∨ ((p5 ∧ p1) → p4)))) → ((p1 ∧ p4) → ((p1 ∨ p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h5
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586792849559126035961117918320 : (((((p3 ∧ ((p5 → (True ∧ p5)) → (False ∨ (p1 → (((p1 → ((((p3 ∨ True) ∧ False) ∨ p2) ∧ False)) → p3) ∨ p3))))) ∧ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177727089801760413950700283049 : (((((p4 → p2) ∨ (p4 ∨ p3)) ∨ (p1 ∧ ((False ∧ p3) → True))) ∧ p1) ∨ ((p4 ∨ p3) → (p3 ∨ (False → (((p4 ∧ p4) ∧ p1) ∨ p3))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305354569759949661151004595115 : (p1 ∨ ((p3 ∨ (p5 ∧ (p1 ∧ (p5 ∨ (False → (((False → p2) → p2) → ((p2 ∧ p2) ∧ False))))))) → (((p3 → p3) → (True → False)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h21
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256701840551603265902898762985 : ((p1 ∨ p1) → ((p3 ∧ (p5 → ((p2 ∧ (((False → (p3 → (p3 → True))) → (p3 ∧ (p2 ∧ p1))) ∨ (p5 → p1))) ∨ (p1 ∨ False)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41316367431572873872396277022 : (((((p1 ∨ ((p3 ∨ (p5 ∧ p3)) ∨ True)) ∧ (p5 ∨ ((True ∧ True) ∨ (True ∧ p5)))) ∧ (True ∧ (p5 ∨ ((p1 ∧ p2) → p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303458412903722509388030528096 : (p1 ∨ (((((p3 ∨ (p4 ∧ (p4 → (True ∧ (False ∧ False))))) ∧ ((p2 ∨ (True ∨ False)) ∧ p4)) ∨ p2) → (True → ((p2 → p1) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
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
          -- False on the left can always be used.
          apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321748347173161361217223469191 : (p4 ∨ (p5 → ((False ∧ (p2 ∨ p4)) ∨ ((((p3 ∧ p1) ∧ (((p2 ∨ (p1 → True)) ∨ (p1 ∨ p4)) → (True → p4))) ∨ (p3 ∨ False)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339770263703988781239555989093 : (p1 → (p4 ∨ (p3 ∨ (p3 ∨ (((p1 ∨ p1) ∧ (True ∧ p1)) → (((((p5 ∧ p3) ∧ (p5 → p3)) ∨ True) → ((True ∧ p2) ∨ False)) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_354777767014504072501265091297 : (p5 → (((((p1 ∨ p1) → p3) ∧ (p4 → (p5 ∨ (p2 ∨ p4)))) → (((((p2 → p2) ∧ p1) → (False ∨ (False ∧ p4))) → p3) → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117617385420007404780840193247 : ((p3 ∧ ((((p3 ∧ p1) ∨ (((p5 ∨ p1) → (False ∨ p2)) ∨ (True ∧ (((True ∨ p2) ∧ True) ∧ (False ∨ False))))) ∨ p2) ∧ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115462268475280768961698065147 : (((p1 ∧ (((True → (p5 ∨ p2)) ∧ p4) → p1)) ∨ (((p4 → True) ∧ (((False ∧ p2) ∨ ((False ∨ p3) ∨ False)) ∧ False)) ∧ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618104871296318114323756101744 : (((((False ∧ ((p1 → p2) ∧ True)) ∧ ((False ∨ p2) ∧ (((p3 ∨ (p1 → ((p2 ∨ p5) ∨ (p4 ∧ p1)))) ∨ p2) → (p3 ∧ p2)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227741998347445667912377368062 : ((p1 ∧ (p1 ∨ p4)) ∨ (p1 → ((((p4 ∨ (p5 ∨ p5)) → (p5 → True)) → (p5 ∧ (p5 → ((False → ((p3 ∨ p2) ∧ p4)) ∧ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784942179535878852884129742505 : (((p3 ∨ (p3 → ((p2 ∨ False) → ((True ∧ ((((p4 ∧ p5) ∧ ((p4 ∨ p1) ∧ ((p4 ∧ p5) ∨ True))) → p1) ∧ p2)) ∧ (p4 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258217574441065453611259038710 : ((p4 ∨ p5) → (((((False ∨ (p3 ∨ (p4 ∨ ((False ∨ ((p5 ∨ p1) → p2)) ∨ (p5 ∨ p3))))) → p2) ∧ (p1 → True)) → (p3 ∨ p2)) ∨ p1)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ (p3 ∨ (p4 ∨ ((False ∨ ((p5 ∨ p1) → p2)) ∨ (p5 ∨ p3))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (False ∨ (p3 ∨ (p4 ∨ ((False ∨ ((p5 ∨ p1) → p2)) ∨ (p5 ∨ p3))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697989878532010357229426806337 : (((((((True ∨ True) → (((p5 ∧ p5) ∨ p3) ∧ p1)) ∧ p4) ∨ p2) ∨ (((p4 → (True → p5)) ∨ (p4 → p5)) ∧ ((True ∧ True) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893546587923624204311209299566 : ((((((p2 ∨ (p2 ∧ False)) ∨ False) → (((False ∨ p1) ∧ p2) ∧ (((True ∨ (p2 → p4)) ∨ (p2 ∨ p4)) ∨ p4))) ∧ (p4 ∧ (p5 → p5))) → p4) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40567453688667415723676547707 : ((((p4 → (((p3 ∨ p4) ∧ (True ∨ False)) ∧ (((p5 → (p5 → False)) → (False ∨ p2)) → (((True ∧ p1) ∧ p1) ∨ False)))) ∨ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304061704894919069922177157662 : (p1 ∨ ((False ∨ (p4 → (False ∨ (p3 → (((True → ((((True → p4) ∨ (False ∨ (True ∨ False))) ∨ p3) → (p5 → p3))) → p2) ∨ True))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165288488981024077708091041355 : ((((((p4 → p5) ∧ (p2 → p2)) → p5) → ((p1 ∨ p3) ∨ (p2 → p1))) → (p5 → p1)) ∨ ((p4 ∨ True) ∨ (p1 → (True ∨ (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316462476417743589142824492557 : (p3 ∨ (p1 ∨ ((p2 ∨ True) → (((((p5 ∧ ((p1 → p2) ∨ (p2 → p3))) ∨ (p3 → p4)) ∧ p5) → (p3 ∨ (False ∨ (p1 ∨ p5)))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241291760133418763008352858312 : ((False → True) ∧ (((p3 ∨ p1) ∧ ((p4 ∨ ((False ∨ (p2 → (False → p5))) ∨ ((p5 ∨ p2) ∨ True))) ∧ p2)) ∨ ((p5 ∧ False) ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350939678899644325493346476340 : (p4 → ((((True → (((p3 ∧ (((p3 ∨ p3) → p4) ∨ ((p2 ∧ False) ∨ (True → p3)))) ∨ p1) ∨ p5)) ∨ p3) ∨ (p4 → p5)) ∨ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135170629212906760765679136096 : ((((False ∨ ((True ∧ False) → ((((p1 ∨ p3) ∨ ((p4 ∨ False) ∨ (False ∧ False))) → False) → p3))) ∧ p4) → (p3 ∨ p2)) ∨ ((False → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48678249514718038338492136440 : (((((False → (p4 ∨ (True → p3))) → (p3 ∨ (p5 ∨ p3))) ∨ ((False ∧ (p1 → True)) → (False ∨ (p1 ∨ p5)))) ∧ ((p2 ∨ True) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168016729870218615853761669760 : ((((p2 ∧ p5) → ((p4 ∨ p1) ∨ False)) ∨ ((((p1 → p2) → (True → p2)) → p1) ∨ False)) → ((False ∨ (p2 → p1)) ∨ (p1 → (p4 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64956883159212173755190904297 : ((p2 ∨ (((((p4 ∨ False) ∧ False) ∨ p1) ∧ (False ∧ p4)) ∨ (((p3 → (p4 ∨ (False → (p2 ∧ p3)))) ∨ p2) ∧ (p2 ∧ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137177016582108505842760533243 : ((False ∧ ((p4 → (True → ((p5 → True) → (p2 → ((False ∧ p2) ∨ p5))))) ∧ (p1 → (((p2 ∧ p2) ∨ p3) → p1)))) ∨ (True ∧ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66564870301312741028575035838 : ((True → ((((p3 → (p1 ∨ (False ∧ (p3 ∧ True)))) → (((p5 ∧ (True ∧ p4)) → p2) ∧ p1)) ∨ (p4 ∨ (p1 ∧ p5))) ∨ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180996634944676111217034386435 : (((p4 ∧ p3) ∨ (((False ∧ ((False → p4) ∧ p2)) → p4) ∨ (p2 ∧ p2))) → (((p5 ∨ p3) ∨ ((p4 ∨ p5) ∨ ((True → False) → False))) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40616219270384626892319590008 : ((((((True ∧ True) → (False → (True ∧ (((p3 → ((False ∧ True) ∧ p5)) → p3) ∨ ((p1 ∨ (True ∧ p3)) ∧ False))))) ∨ p1) → False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223596588647892484587808293720 : ((p1 ∨ (True ∨ p3)) ∧ (((p3 ∧ True) → ((p3 ∨ (p4 ∧ ((True ∧ p2) → True))) → p1)) ∨ (True ∨ ((True → (p1 → p3)) ∧ (True → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114933148459935785584517273436 : ((((((True → p5) ∨ p5) → ((False ∧ False) ∨ p2)) → ((True ∨ p4) → p4)) → ((p1 ∧ (p5 ∧ (True ∧ (p4 ∨ p2)))) → p4)) ∨ (p5 ∧ p4)) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (((True → p5) ∨ p5) → ((False ∧ False) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h11
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260111886697656778765972867666 : ((p2 → p1) → (((True → (False → (p2 ∧ ((p4 ∨ p2) → (p1 ∨ True))))) → (p4 ∧ (True ∧ (p4 ∧ ((p5 ∧ p4) ∧ p2))))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318682959284846746897769181660 : (p4 ∨ (((((True → ((True → (((True ∨ p5) ∨ (p1 ∧ (((p4 → p5) → p5) ∨ p2))) → p2)) ∨ True)) ∨ p2) ∨ p5) → False) → (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → ((True → (((True ∨ p5) ∨ (p1 ∧ (((p4 → p5) → p5) ∨ p2))) → p2)) ∨ True)) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((True → ((True → (((True ∨ p5) ∨ (p1 ∧ (((p4 → p5) → p5) ∨ p2))) → p2)) ∨ True)) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46516130151389196776037363895 : ((((p4 ∨ p4) ∧ (((False ∨ ((p5 → (p1 ∨ (((p4 → p1) → p5) ∧ (p3 ∨ p2)))) → (p5 ∧ p1))) ∨ p5) ∧ p4)) ∧ (False → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45472622532105135198866541413 : (((False ∨ (((((False ∨ (((p3 → (p4 ∧ ((False → False) ∧ p4))) → p5) ∧ (p2 → p3))) ∨ True) → p1) ∨ False) ∧ (p5 → p4))) → p1) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((False ∨ (((p3 → (p4 ∧ ((False → False) ∧ p4))) → p5) ∧ (p2 → p3))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137616908324848233824650579831 : ((False ∨ ((((((p2 ∧ (p5 ∨ (p5 → ((False → p4) ∨ (p5 ∨ p2))))) ∨ p1) → p5) ∨ (p4 ∨ True)) ∨ p4) ∨ p3)) ∨ ((p3 → False) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51902768619590338896342116409 : (((((((p3 ∨ p4) ∨ (False → p2)) → (p1 ∨ (True ∧ p2))) ∨ p3) ∧ (p5 → p3)) ∨ (p4 ∨ (False → ((True ∧ p3) → (False ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238321637565030297911512846401 : ((False ∨ True) ∧ ((((p4 → (p2 → p2)) → (p2 ∨ p4)) ∧ (p3 ∨ True)) ∨ ((((p2 ∨ ((True ∧ p3) ∧ False)) → p5) → (p5 ∨ True)) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148516057551346154673376086658 : (((((p5 ∧ (p1 ∧ False)) ∨ (False ∨ ((False ∧ True) → p1))) ∨ False) → (((p2 ∧ p2) ∨ p2) ∧ (True ∧ p4))) ∨ ((p3 ∨ (p3 ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48754874309908587265603169445 : ((((p4 ∨ True) ∧ (p3 ∨ ((p1 → (p5 ∧ p1)) → ((p3 ∨ (((p1 ∨ p5) ∧ (p4 → p4)) ∨ p1)) ∨ True)))) ∧ (True → (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244961466314336108000171400414 : ((p1 ∧ p3) ∨ (p1 ∨ ((p3 ∨ (((p5 ∧ p2) ∨ p4) → ((p3 ∨ (((((p2 → p2) → p2) → p1) ∧ False) → p2)) ∨ (p1 → True)))) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
theorem thm_5_vars_355605732799485081418549413529 : (p5 → (((p5 ∧ p2) ∨ ((((False → ((False ∧ (p4 ∨ p2)) ∧ False)) → (p5 ∨ (False → p1))) ∨ (p5 ∨ (p4 ∧ p1))) → p3)) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337852382174096754037224216682 : (p1 → (((((p4 ∨ (p2 ∧ (False → True))) ∨ True) → (p4 → (p4 ∧ False))) ∨ True) ∨ (p1 ∨ (p5 ∨ (((True → (p5 → p5)) ∨ p2) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303866694186168025479586513750 : (p1 ∨ (((False ∨ (((False ∨ p3) ∧ ((((p2 → True) → p4) → p2) → (p3 ∧ (p5 ∨ p1)))) ∧ (p4 → p3))) ∨ ((p5 → True) ∨ p5)) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350288687386399804756177782764 : (p4 → ((False ∨ (((p5 ∨ ((p4 ∧ ((p2 ∧ (True ∧ p4)) ∧ (p4 ∨ p2))) ∧ (False ∨ p3))) ∧ (p5 → p5)) ∧ ((p3 ∧ True) ∧ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156893798809600449913580752086 : (((((True ∨ (p4 ∨ p3)) → (((p2 ∨ True) ∧ (p5 → (p4 ∨ p2))) → (p5 ∨ p2))) ∨ True) ∨ p4) ∨ (((p3 ∨ p4) ∨ (p4 ∧ p1)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241552620186110294637051115232 : ((False → p3) ∧ ((p4 ∨ p4) → ((p2 → p3) → ((((p3 → (p2 → (True ∨ (p3 ∨ ((p3 ∧ p4) ∧ p1))))) → p3) → p1) ∨ (p2 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57887454543961315498189788162 : (((p2 ∨ (p1 → False)) → ((((((p5 ∨ (False ∨ p1)) ∨ p5) ∧ True) ∧ ((True → p5) → ((p1 → p3) ∨ p5))) ∨ p2) ∨ (True → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652746911566054562737625261529 : ((((p2 ∨ (((p5 → ((True ∨ ((((True ∨ p3) ∧ p4) ∨ False) → p3)) ∧ p3)) ∨ p1) → (False ∧ (p3 → (p1 ∨ p3))))) ∧ (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317129278799081874663180834590 : (p3 ∨ (p5 → ((True → p3) ∨ (p1 ∨ (((p5 → (p1 → ((p3 ∨ p3) ∧ (((False ∨ p3) ∧ True) ∧ p1)))) ∧ False) ∨ ((p2 → p4) → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264898948531793183508728048718 : (True ∧ ((p5 → p3) ∨ (((((((p1 → p3) → ((p3 → p3) ∧ ((True ∨ p2) ∨ (False → p3)))) → p2) → p1) ∨ (p1 → p1)) → p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140817533068883191388446448226 : (((((True ∨ p5) ∧ ((True ∨ (p2 → True)) ∨ (p2 ∨ p4))) ∨ p1) ∨ ((((p5 ∨ p1) ∨ p5) ∧ (True → p5)) ∨ False)) → (p1 ∨ (True → True))) := by
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
      cases h4
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h9
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h22
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181381506058495378736225648436 : ((p1 ∨ ((False → (p5 ∧ (False → (p1 → p4)))) ∧ (p5 → (p2 ∧ True)))) → (p4 ∨ (p5 → (((p4 → (p2 ∨ p3)) ∧ (p2 ∧ False)) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601972998266988217854770411710 : ((((p4 ∧ (p3 → ((False ∧ (p2 → ((((True ∧ False) → p3) → p2) ∨ p5))) ∨ ((p2 ∧ p5) ∧ (p4 ∨ ((p3 ∧ p1) ∧ p1)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776754769927955212813647034982 : (((p1 ∨ (((p1 → ((((p2 ∧ p1) → (p4 ∧ p1)) → False) ∨ (((p4 ∧ ((p4 ∨ p1) ∧ p3)) ∨ p5) ∧ p1))) → (p5 → p3)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136363063946379878349855919777 : ((((p5 → (True ∨ p3)) ∧ False) ∨ ((True ∨ (p4 ∨ (p3 ∨ (True → (True ∨ p1))))) → (p2 → (p1 ∧ (p2 → p5))))) ∨ (False → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191250759694024438130248892734 : (((p2 ∧ False) ∧ (False ∧ (((p4 ∨ p3) ∨ p2) → p4))) ∨ (True → (True ∧ (p3 ∨ ((p4 ∨ (True ∨ (p1 ∨ p5))) ∨ (p4 ∨ (p4 ∧ p3))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_445975780761180071516085221012 : (((((True → (p2 ∨ (((p4 ∨ p5) ∧ p2) → ((p2 ∨ (True ∧ ((p1 → p4) ∨ p4))) ∧ (p3 ∨ True))))) → False) → (p5 ∧ (p5 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p2 ∨ (((p4 ∨ p5) ∧ p2) → ((p2 ∨ (True ∧ ((p1 → p4) ∨ p4))) ∧ (p3 ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (True → (p2 ∨ (((p4 ∨ p5) ∧ p2) → ((p2 ∨ (True ∧ ((p1 → p4) ∨ p4))) ∧ (p3 ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- Conjunctions on the left can always be decomposed.
    let h21 := h16.left
    let h22 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h25 := h1 h14
  -- False on the left can always be used.
  apply False.elim h25
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h26 : (True → (p2 ∨ (((p4 ∨ p5) ∧ p2) → ((p2 ∨ (True ∧ ((p1 → p4) ∨ p4))) ∧ (p3 ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h27
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h32 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30
    -- Conjunctions on the left can always be decomposed.
    let h33 := h28.left
    let h34 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h37 := h1 h26
  -- False on the left can always be used.
  apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173154141928225433128348885045 : ((p3 ∨ ((p2 ∨ p3) ∨ ((((((p4 → p1) ∧ p4) ∨ True) ∨ p5) ∧ False) ∨ p3))) ∨ (p2 → (p4 ∨ ((p3 → True) ∧ ((p3 → p2) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219184473538662454207736181075 : ((False ∨ (True ∧ (True ∧ True))) → ((True ∨ p1) ∧ (((((False ∧ p3) → ((p2 → p5) → p1)) ∧ (True ∨ (p2 ∨ p1))) → (p1 ∧ p2)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719456106600323858698692983237 : ((((p1 ∨ (p1 ∧ (False → p4))) ∨ ((p4 ∨ (True ∧ (((p1 ∧ p4) ∨ ((p3 → False) → p3)) ∨ False))) ∨ (p5 ∨ (p3 → (False ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724087895297725885544916409993 : ((((p1 ∧ (p3 → p5)) ∧ ((((p5 → (((p1 ∧ p1) ∧ p3) ∧ (p1 ∨ (p5 ∧ (p3 ∧ p2))))) ∨ (p4 ∨ p1)) ∧ p1) ∧ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61867580206968980478180708604 : ((p2 ∧ ((p1 ∨ (True → (True ∧ ((False ∧ (p1 → (p2 ∧ (True → (((False ∨ (False → p2)) ∨ p2) ∧ (p4 → False)))))) ∨ p1)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113462914950565399883228022807 : (((((((p1 → False) ∧ p4) ∨ p3) ∨ (p4 ∧ ((False ∨ (((p5 ∨ (p2 → p5)) ∨ False) ∨ p1)) ∧ p3))) → p2) ∨ (p1 ∧ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206826534236416555888664243425 : ((p5 → ((p3 → False) ∨ (p3 → p4))) ∨ (((p1 → ((p3 → p2) ∧ p5)) ∧ (((p4 ∧ (p1 ∨ (False → p4))) ∨ True) ∧ p5)) → (p4 ∨ p5))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185337973757689080138092071503 : ((p4 ∧ ((p4 ∧ (p3 ∧ (p5 ∨ (False ∧ (p2 → True))))) ∧ False)) ∨ (((p2 ∨ (p4 → p5)) ∧ p1) ∨ ((True → (p1 → p5)) → (p5 → True)))) := by
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
theorem thm_5_vars_756316297410926956804732858807 : (((p1 ∧ ((p3 ∧ (p2 → ((True → (True → ((False ∨ ((True ∧ (True → p1)) → p5)) → p3))) → ((p1 → p1) → p2)))) → (p3 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300554203655513275985639259333 : (False ∨ (((p2 ∨ ((((p5 ∨ p3) → p1) → p5) ∧ p1)) ∨ (p5 → ((((p4 ∧ True) ∧ p1) ∨ p1) → p2))) ∨ (((p2 → True) ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1470873004305699266272146150 : ((((((((p3 ∧ (False → (p1 ∨ p3))) ∨ p1) → True) ∧ p2) ∧ p2) ∧ (p4 ∧ ((p2 → p4) ∨ (p2 ∨ p3)))) ∨ True) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_830836383587783438428629573976 : ((((True → ((((p3 → p1) ∧ (((p4 → ((p4 ∧ p3) ∨ True)) → p3) ∧ p5)) ∧ False) ∧ (True ∧ ((p2 ∨ (p4 ∨ p5)) → False)))) ∧ p1) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769132476694441221149349729685 : (((p5 ∧ ((p2 ∨ True) ∧ ((p5 → ((True ∧ False) ∧ ((p4 ∧ ((False ∨ True) ∨ ((p5 → p5) ∧ (p2 ∨ p2)))) ∧ (p1 ∧ p3)))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215086221103606500865286596394 : (((False → False) → (False ∧ p2)) ∨ ((((False → ((p2 ∧ False) ∧ (p1 ∧ (False ∨ (p1 ∨ p1))))) ∨ (p5 → p1)) ∧ (p3 → (p4 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217141260810192130571047324285 : ((((p1 → p4) ∨ p5) ∨ True) → (p5 → (p2 ∨ (((((False ∨ p5) ∨ p2) ∧ (True ∨ ((p1 ∧ p3) ∧ (False → False)))) ∨ (True ∨ p4)) ∨ p2)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
  case inr h6 =>
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
theorem thm_5_vars_155362134926563961432099045544 : ((((p2 ∨ False) ∨ (p5 ∨ True)) ∧ (((True → (((p4 ∨ True) ∧ (p1 → p4)) ∧ p5)) ∧ p1) ∨ True)) ∧ (p4 → ((p1 → p4) ∧ (False → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53852898164246516432529295523 : ((((p3 ∨ (p3 ∨ True)) ∧ ((True ∧ p2) ∧ (p4 → p3))) ∨ ((False → ((((p1 → False) ∨ p5) ∨ False) ∧ p2)) → (p4 ∨ (p5 → p5)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201128812620099123062506932449 : ((True → (p3 → (p3 → ((True ∧ p4) ∨ p5)))) → (p3 → ((False → (p2 ∨ (p4 → False))) → ((p4 ∧ (p3 → (p5 ∧ (p3 ∧ True)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_899546638108939162170452856 : ((p3 → (False ∨ (((((True ∧ p1) ∧ p4) ∧ ((((p4 ∨ ((p5 ∧ p4) ∧ p1)) ∧ p4) → False) ∧ (p1 ∨ True))) ∨ p2) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136529497921885317629695013050 : (((False → (True → p5)) ∧ ((False → p2) → (((p4 ∧ (p3 ∨ (p2 → (p5 ∧ True)))) ∨ (p4 ∧ (p4 → p1))) → p3))) ∨ ((p2 ∧ False) → p1)) := by
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
theorem thm_5_vars_59154908371769695548730689022 : (((False ∨ p1) ∨ (((p5 ∨ p4) → (p2 ∨ (((((p3 ∧ ((p1 → (False ∧ p3)) ∨ p2)) ∨ p2) → False) ∨ False) → p4))) → (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165591536310347239966705467567 : (((((p5 → (False → (True → True))) → p4) ∧ p2) → ((False ∨ p3) ∧ (p3 ∧ (p2 ∧ p2)))) ∨ ((((p5 → (True ∧ p1)) ∨ p3) ∧ False) → False)) := by
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
theorem thm_5_vars_328138892849716160159028614076 : (True → ((False ∧ ((p2 ∧ True) ∧ ((((((False → p1) ∧ True) ∨ True) ∧ p3) ∧ ((p2 ∨ (False ∧ p3)) ∧ False)) ∧ p5))) ∨ ((False → p2) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137734784470677630099223266795 : ((p1 ∨ (p4 ∨ (True ∧ (p1 ∧ ((((p1 ∧ (False → False)) → ((p4 ∧ p2) ∧ (p5 → (p4 → p2)))) ∧ True) → p1))))) ∨ (False ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111413036915997362666905500862 : (((p3 ∨ ((p3 ∧ (((p1 → (p1 ∧ (False ∨ (p5 ∨ False)))) ∧ p4) ∨ (((p5 ∧ p3) → (False → p5)) ∨ p2))) ∧ p1)) ∧ p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39086971850602295474514115806 : ((((p4 ∨ p3) ∨ ((((True → False) ∨ ((p1 ∨ (((p5 → (p1 → (p4 → p4))) → p1) ∨ True)) ∧ (p5 ∨ p5))) ∨ p3) ∧ p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158730777056429928372347138815 : ((p3 ∧ (False ∧ (p4 ∨ (p2 ∧ ((((p5 ∨ False) ∨ p3) ∨ ((p4 ∨ p2) → (True ∧ p1))) ∧ p5))))) ∨ ((False ∧ ((p1 ∨ True) ∧ p1)) → False)) := by
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
theorem thm_5_vars_112317689336075762703944974327 : (((p3 → (((p3 ∨ p2) ∧ (((p3 ∨ (p3 ∨ p1)) ∨ (p5 ∧ ((True ∨ p4) → ((p2 ∧ p1) → True)))) → False)) ∨ False)) ∨ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226305380844241483881288153955 : (((p4 ∨ p5) ∨ p1) ∨ ((((p2 ∧ False) ∨ (p3 ∧ p3)) ∨ False) ∨ (((((False → (p5 ∨ False)) ∧ p3) ∧ ((True ∨ p2) → True)) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55518674074711704353700666008 : ((((p3 ∨ False) ∨ (p3 ∧ (True ∨ p1))) → (((True → True) → (p1 ∨ (p1 ∨ ((((p2 ∧ p1) → False) ∨ (p4 ∨ p2)) → p3)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754722854262292336541267408807 : (((False ∧ (p5 ∧ (p4 → (((((False → p1) → (((((p3 ∨ (p2 → p3)) → p4) ∨ p5) ∧ p4) ∨ p4)) → (True ∧ p2)) ∨ p5) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806996415115762786591461265159 : (((p4 → ((False ∧ ((p1 ∨ (p2 → (p2 ∧ (p5 ∧ (p5 ∨ p3))))) ∧ ((p2 ∨ p3) ∧ (p5 ∧ (p2 → True))))) ∨ (True ∧ (False → p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231378907716900290724506104476 : (((False → p4) ∨ p3) → (((True ∧ (p5 ∧ (p2 ∨ (p1 ∨ ((False → p2) ∨ p5))))) ∨ (p5 → (p1 → (p3 → p5)))) ∨ ((True ∧ p3) → p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252559757736344563612951566074 : ((p5 → p2) ∨ (p2 → (p5 → ((((((p4 ∨ p5) ∨ p1) ∨ p4) → (((p1 ∧ p2) → (p3 → p4)) ∧ (p3 ∧ p4))) ∧ (p4 → False)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 ∨ p5) ∨ p1) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185587675663763282930416281372 : ((p5 ∨ (((False ∨ (p5 ∧ p3)) ∧ (p5 ∨ p3)) → (False ∨ p1))) ∨ (((False ∧ p4) → ((p1 → p1) → p1)) ∨ (((True ∧ True) ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318553748534431503763330645490 : (p4 ∨ (((((p2 ∨ (((p3 ∧ p4) → ((p1 → p2) ∧ (False ∧ p1))) → (p2 → ((p1 ∧ p4) ∨ p2)))) ∧ False) ∨ p1) ∨ True) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



