variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137918342761922595640303943388 : ((p4 ∨ ((True ∧ p3) ∨ (p4 ∧ (p3 ∧ (p4 ∧ (((p5 → p1) ∧ p5) ∧ ((p1 ∨ (p3 → (p4 ∨ p1))) ∧ False))))))) ∨ ((p1 ∧ p3) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136090746763505816712809677547 : (((((True ∨ p3) → (p4 ∧ (p2 ∨ p3))) ∧ True) ∨ (((p1 ∧ True) ∧ (p1 → ((p5 → p3) ∧ p4))) ∨ (p1 ∧ p4))) ∨ ((p1 → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3207757954594187101696679482 : ((p5 ∧ False) ∨ ((((p1 ∧ p4) ∧ True) ∧ ((p4 ∧ (p1 ∧ ((p4 ∧ ((p2 ∨ p4) → (False ∨ p3))) → (p1 ∧ p5)))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142081343276495758722891223472 : ((True ∧ ((p5 ∨ (True ∨ p2)) ∨ ((((p2 ∧ True) ∨ (((False ∧ p1) ∧ ((p1 ∨ True) ∨ False)) ∨ True)) ∧ p3) ∨ p3))) → (p3 → (p5 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h19.left
          let h22 := h19.right
          -- False on the left can always be used.
          apply False.elim h21
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34983251412172590679738239612 : ((p1 → ((((p4 ∨ p5) ∧ p2) ∧ (((((((p4 ∨ (p4 ∧ p1)) ∨ p2) → p2) ∧ p2) → False) → (p1 ∧ (p4 ∧ p2))) ∧ p3)) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161693972759152711145969816321 : ((p2 ∨ ((((p1 ∨ False) ∧ p5) ∧ (False ∨ p3)) ∨ ((p2 → ((False → p2) ∧ False)) ∨ (p1 → p2)))) → (p1 → (p2 → ((p5 ∧ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51790766293541101999933652171 : (((True ∨ ((((True → (False ∨ ((p2 ∧ True) ∨ p1))) ∧ (p3 ∨ p2)) → p3) ∨ True)) ∧ (p4 ∧ (p4 → (False ∨ ((p1 ∧ False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118536025969634758756505839810 : ((p3 ∨ (p4 ∧ (((True → (p4 ∧ p4)) ∧ p3) ∧ (((((p1 ∧ p1) ∨ (p2 ∨ p3)) ∧ False) ∨ ((p3 ∧ p4) ∨ p3)) ∨ p5)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351836878391567196405876252549 : (p4 → (((((False ∨ ((p1 → p5) → p5)) → True) → (p3 → p4)) ∧ p5) → ((((p2 → (p2 → (p4 → False))) ∨ (p4 ∧ p5)) ∧ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171797013954286961820882813317 : (((((p2 ∧ p1) ∧ (p5 ∨ ((p1 ∨ p4) ∧ p1))) ∧ ((p1 ∨ p5) ∨ True)) → p4) ∨ (True ∨ (p3 ∨ (p1 ∨ (((p4 ∨ p2) ∨ p4) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165775509251645116086658054982 : ((((p3 ∨ p2) ∧ (p1 ∨ p5)) → (True → (False ∧ ((((p2 ∨ p1) ∨ p4) ∨ p5) → p2)))) ∨ (((True → p5) ∨ ((p5 ∧ p4) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656699586096190914537822204902 : (((((p2 ∧ (((p2 ∨ p4) ∨ True) → True)) ∧ (((p1 → (p2 ∧ (True → (p2 → ((p1 → p4) → p2))))) ∧ False) ∧ p1)) ∨ (p3 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342565751362907749294621920161 : (p2 → (((False ∨ (((p1 → False) ∨ (p3 → (p3 ∨ False))) → p3)) ∨ p3) ∨ (p4 ∨ (True ∧ ((((p1 ∨ (p3 ∨ True)) ∨ p3) ∧ False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764581714184048730970669034009 : (((p4 ∧ ((((((p3 ∧ ((p3 → p5) → (p1 ∨ p2))) ∨ (((p3 → p1) ∧ p2) ∨ p1)) → p2) → p5) ∨ ((p1 ∧ True) ∧ p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225954037771099227090529854098 : (((p2 ∧ p5) ∨ p5) ∨ ((p2 ∨ ((((p1 ∨ p2) ∨ p1) ∨ ((p3 ∨ (((p2 → False) → p1) → False)) ∨ p4)) ∨ ((p1 ∨ True) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196937486285861113047889481942 : ((((p5 → (p4 ∧ (False ∨ p3))) ∧ p2) ∨ p3) ∨ (((p4 ∨ p2) ∨ True) ∨ (((True ∧ True) → ((False ∨ True) → (p4 ∧ p4))) ∨ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259018394342966436121209934795 : ((True → p4) → (((p4 ∨ (((p5 → (p5 ∧ p5)) → p3) ∨ ((((False ∧ (p1 ∨ (p1 ∨ p3))) → True) → p2) → p1))) → p4) ∨ (False ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h7 := h1 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122686630010435509891866231834 : (((((p4 → (p5 ∧ p5)) ∧ ((p2 → p3) → p2)) → ((p2 → (p1 ∧ (p4 ∧ p5))) ∨ ((p5 ∧ True) ∨ p5))) → (False ∧ p5)) → (p4 → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 → (p5 ∧ p5)) ∧ ((p2 → p3) → p2)) → ((p2 → (p1 ∧ (p4 ∧ p5))) ∨ ((p5 ∧ True) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h3
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324033130744931450927763924028 : (p5 ∨ ((True ∨ (((p1 ∧ False) ∧ p5) → (p5 → (False ∨ (p3 ∨ (True ∧ p5)))))) → ((p5 → p4) ∨ (((p3 ∨ (p1 ∨ p2)) ∧ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135547066052879788379834927629 : (((((p2 ∨ p3) ∨ p5) ∨ (((((p5 ∧ p3) ∧ p3) ∨ False) → False) ∧ (p1 ∧ p3))) ∧ (False ∨ (p3 ∨ (p3 ∧ p1)))) ∨ (p3 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191489691231743702787036187827 : ((True ∧ (p2 ∧ (((p4 ∧ True) ∨ p5) ∨ (False ∧ p3)))) ∨ (p1 → (((((p1 ∨ p1) ∨ (p5 ∧ p2)) ∨ True) → p1) ∨ ((p2 ∨ p2) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185446918547183498047918326738 : ((False ∨ (False ∧ (p2 → (p1 → ((p4 ∨ (p5 ∨ True)) ∧ p4))))) ∨ ((p1 ∨ (p4 → (True ∧ False))) → (True ∨ ((p3 → p4) ∨ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714137788389508264474977210493 : (((((p5 ∧ ((p5 → p1) ∨ p3)) → True) → ((p1 → ((p1 → (p1 ∨ p2)) ∨ ((((False → p4) ∧ True) ∨ p3) ∧ p4))) ∧ (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749635083430837544601555184542 : (((True ∧ ((((True ∧ ((((p1 → ((((False → p5) ∨ False) ∧ p5) ∨ p1)) ∧ False) ∧ p1) → p3)) → (False ∨ (p3 ∧ p4))) ∨ p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137363668282877312473806833204 : ((p3 ∧ ((p1 → (((True ∧ p1) → ((p4 ∧ (p5 → p3)) ∨ (((True ∧ (p3 → p2)) → True) ∨ True))) → p5)) → p4)) ∨ (False → (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657270338077866075835981154453 : (((((True ∧ True) ∧ ((p3 ∧ (((p2 ∧ ((p3 ∧ False) ∧ True)) ∨ (p4 ∧ p2)) ∨ ((p3 ∨ (False ∧ p2)) ∨ p5))) ∨ True)) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_226898242004573561201328679550 : (((p5 ∧ p5) → p4) ∨ (((p2 ∧ (False ∧ p2)) ∨ p2) ∨ (p5 → (((p5 ∧ p2) ∧ ((False ∧ p1) → ((p1 → p2) → (p3 ∧ p2)))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47822372662690737099148434759 : ((((((True ∧ (p1 ∨ p4)) ∨ (p3 ∧ False)) ∨ (p5 → ((((p3 ∨ p2) ∨ (False → (p4 ∧ p3))) ∨ p1) → p5))) → False) → (p2 ∧ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ (p1 ∨ p4)) ∨ (p3 ∧ False)) ∨ (p5 → ((((p3 ∨ p2) ∨ (False → (p4 ∧ p3))) ∨ p1) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h8 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (((True ∧ (p1 ∨ p4)) ∨ (p3 ∧ False)) ∨ (p5 → ((((p3 ∨ p2) ∨ (False → (p4 ∧ p3))) ∨ p1) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h12
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327029905015850378205487474494 : (True → (((((p1 ∨ ((True → (p3 → p5)) ∨ True)) → p2) ∧ (False ∨ p5)) → ((((p3 → p2) ∨ False) ∧ True) → ((p3 ∨ p1) → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264829084329343177719674251310 : (True ∧ ((False ∨ False) ∨ (((((False ∧ (p1 ∧ p4)) → p1) ∧ p3) ∧ ((p3 ∧ (p5 ∨ p5)) ∨ (((p5 ∧ False) ∨ p2) ∨ (p3 → False)))) ∨ True))) := by
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
theorem thm_5_vars_141333846046353258709289670528 : ((((False ∧ (p3 ∨ True)) → p1) ∨ ((((p1 ∧ p3) → ((p3 ∧ (p5 ∧ p2)) → p5)) ∧ (p1 ∨ (p3 ∨ p4))) → p5)) → ((p1 ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117643191701209300449614737677 : ((p3 ∧ (((False ∨ ((p3 ∧ p1) ∧ (p4 → ((p1 ∨ p1) ∧ p1)))) → (((True ∧ False) → ((True ∧ True) → p4)) ∧ p4)) → False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64867667561706107300020277396 : ((p2 ∨ (((p4 ∨ p4) ∨ ((((p4 → p5) ∨ p4) ∨ p1) → (p2 → ((p1 ∨ True) ∧ (True ∨ ((p4 ∨ p3) ∧ p2)))))) ∨ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38238817218666045103932425161 : (((((((p5 ∧ p2) ∧ (p5 ∧ ((((False ∨ p5) ∨ p3) ∧ p1) ∧ False))) ∨ (p3 → p4)) ∨ p3) ∧ ((p2 ∧ p4) → (False ∧ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166119370860080674714581548877 : ((True ∧ ((p5 ∧ ((False → p1) → ((p2 → p1) → (p4 ∧ ((p5 → p2) ∨ p4))))) ∨ True)) ∨ (p2 ∧ ((((p5 → p2) ∧ p2) ∧ p4) ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727822450275353126011270992291 : ((((p1 ∨ (p5 ∧ p2)) ∨ (((p3 ∧ (p4 ∨ (((True ∧ ((p2 ∧ p1) ∧ p1)) ∨ (p5 → ((True → False) ∧ p4))) ∨ p5))) ∧ p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_791051574492623366066847797955 : (((True → ((((True ∧ (p2 ∧ p2)) → (((False → p3) → False) ∨ ((p4 → p4) ∧ ((p1 ∧ True) ∧ ((p3 ∧ p3) ∨ True))))) → p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64424663250399110573548396322 : ((p1 ∨ ((((p4 ∨ (p5 → p4)) ∧ ((p1 ∧ ((False → False) → ((p3 → True) → ((p4 ∨ False) → True)))) ∧ p2)) ∧ p3) ∧ (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135042997762949755768808369950 : (((((p5 ∨ ((False ∧ (((p4 → (p4 → (True ∨ p5))) → p4) ∨ (p3 ∧ p1))) ∨ p1)) ∧ True) ∨ True) ∨ (False → True)) ∨ (p3 ∨ (p2 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800204027847488263780671485875 : (((p2 → ((((p5 ∧ True) ∨ ((((((p3 ∧ (p4 → (p4 ∧ (p5 ∨ False)))) ∧ p4) ∨ (p2 → p3)) ∨ p2) → p5) → p3)) ∧ p5) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41694612505176044967877622503 : ((((((p5 ∨ True) → (p3 ∨ p2)) ∨ p4) → (((p2 → p4) ∧ (((((p4 ∧ p1) → (p1 → p1)) ∧ p3) ∨ True) ∧ p2)) → p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39027641738451638890190848800 : ((((p2 → p1) ∧ (p3 → ((p4 → (True ∧ (p1 ∧ p1))) → (((((p4 ∨ (p2 ∨ (p4 ∧ p3))) → p2) → p4) → p1) ∧ p3)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80680995194313895444958477735 : (((False ∨ (p5 ∨ (p1 ∨ (p2 → ((p1 ∨ (p5 ∨ (p2 ∨ (p5 ∧ ((p5 ∧ (False → (p4 → False))) → False))))) ∧ p2))))) → (p3 ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p5 ∨ (p1 ∨ (p2 → ((p1 ∨ (p5 ∨ (p2 ∨ (p5 ∧ ((p5 ∧ (False → (p4 → False))) → False))))) ∧ p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110673037248956617542438112799 : ((p5 → (p5 ∧ ((((p2 ∧ p2) ∨ False) ∧ ((True ∧ p4) ∧ p4)) ∨ ((p4 → ((((True ∨ False) ∧ True) ∧ p4) → p3)) → p5)))) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51949146067344336940049132382 : ((((p2 ∧ ((p5 ∨ True) ∨ (p4 ∨ p2))) ∨ ((True → (p5 ∧ (False ∨ True))) → p4)) ∨ ((((True → p4) ∧ p5) ∨ p5) → (True ∨ p1))) ∨ p1) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207694165090039151004394346087 : ((((p1 → False) → (p5 → p5)) → False) → (p3 → ((p4 ∧ p4) ∨ ((p3 ∨ p3) → (p3 → (((p4 ∨ ((p3 ∨ p5) ∨ True)) → False) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 → False) → (p5 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329020563853373860182527284266 : (True → (((p3 → (p5 → (True → p1))) ∨ p2) → ((((p3 ∨ (p1 → p3)) ∨ ((p3 → True) ∧ p4)) ∨ (p3 ∧ p1)) ∨ (p1 ∨ (True ∨ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47164724993667225678274433010 : ((((((p3 ∧ False) ∨ (p1 → (p2 ∨ False))) → (((p1 ∧ p2) → p1) → p3)) ∧ (p2 ∨ (((p3 ∧ False) → p3) → False))) ∨ (False → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247502010074499483078798089707 : ((False ∨ p3) ∨ ((p4 ∧ p2) ∨ (p2 ∨ (((p4 → (p4 ∧ ((p2 → (False → (p4 ∧ p1))) ∨ (False → (p4 → p4))))) ∧ (False ∧ p1)) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356728930042445017611889081872 : (p5 → (((p3 ∧ (True ∧ False)) ∨ (p5 ∧ p1)) ∨ ((p3 ∧ (p3 ∧ ((True → p4) ∨ p5))) ∨ (p4 ∨ ((False ∧ False) → ((True ∨ False) → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137529651236085056122318496868 : ((p5 ∧ (p4 ∧ ((((p5 ∧ ((False ∧ p1) ∨ (False ∧ p2))) → p4) ∧ ((((True ∧ p4) ∧ p3) ∨ p1) ∨ p1)) ∨ True))) ∨ (True ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171988162239952227309205379106 : (((((((p4 ∨ p3) ∧ p1) → p3) ∧ (p5 → (True → p1))) ∧ p2) ∨ (p5 ∧ p3)) ∨ (False → (p2 → (((p4 → False) ∨ (p4 ∨ True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928558584981136768413161865773 : ((((True → (False ∧ ((p1 ∧ (p2 → (p2 → p1))) ∨ p3))) ∧ ((((p1 → p2) ∨ ((True ∨ (p4 → p2)) ∧ True)) → (True → p4)) → p4)) → p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688106482805831380014869793725 : (((((p4 ∧ ((False ∧ True) ∧ p5)) → (False → (p2 ∧ ((p4 ∨ (False ∧ False)) → p5)))) ∧ (p2 → ((p1 ∨ p4) → (p1 ∧ (p4 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40535054319020194512080505597 : ((((p2 ∨ (False ∧ (p4 ∧ (((p1 ∨ (p3 → (p4 ∧ (p1 ∨ p2)))) ∨ ((False ∧ p3) → (True ∧ False))) ∧ (p1 → p3))))) ∨ p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180162195622192849899753414901 : (((((p5 → p5) ∧ ((False ∨ (True ∧ True)) → p3)) → (p2 → p2)) → True) → (p3 → (((p3 → ((p1 → p5) → (p2 ∧ p5))) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78987998797435000533561134395 : (((p4 ∧ (((p1 → ((p5 ∨ (((p5 ∧ p2) ∨ ((p4 ∨ p5) ∨ p4)) → p5)) → p4)) → (p3 ∧ p1)) ∧ (p3 → True))) ∧ (True → p4)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (p1 → ((p5 ∨ (((p5 ∧ p2) ∨ ((p4 ∨ p5) ∨ p4)) → p5)) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h8
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317897056736168643041377175113 : (p4 ∨ ((p1 ∧ (p4 → (((False → p3) ∧ ((p3 → p1) ∧ (p2 ∨ ((False ∧ p2) ∧ (False ∧ (((p1 ∨ p1) ∨ False) ∨ p5)))))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336385115459350474262506442899 : (p1 → ((p1 ∧ ((((p1 ∨ (p5 ∧ p4)) ∨ p2) → (((((p2 → (p4 ∧ False)) → (False → p4)) → False) → (True ∧ False)) → p4)) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611104214297377621141751238830 : ((((((((p5 → False) ∨ p4) ∨ p1) → ((p5 ∧ (False ∧ ((p3 ∨ False) ∧ (True → p2)))) ∧ (((False → False) → p5) → False))) → p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810869339283236893929814612872 : (((p5 → ((p1 ∨ p4) ∨ (((p3 ∧ (p1 → False)) ∧ p3) ∨ (((((p4 → p2) ∧ ((p1 ∨ p3) → (p1 → True))) ∨ False) ∨ p5) ∨ False)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41150628677455492066798404490 : (((((p5 ∧ (False → False)) → (((True ∧ (p3 → (p2 ∨ (p4 ∧ (p4 → p1))))) → (True ∧ p2)) ∧ p5)) ∨ ((p5 ∧ p1) ∧ p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134684701489741426517199450325 : (((((((p4 → p3) → p2) → p2) ∨ False) ∨ ((False ∨ (False → p4)) ∧ (p2 ∨ (p4 → ((p2 → True) ∧ True))))) → p4) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256759059345310684451430341278 : ((p1 ∨ p2) → (((False ∧ ((p5 → ((((p3 → p1) ∨ p4) ∨ False) ∧ p4)) ∨ ((False → (p1 ∨ False)) ∨ ((p4 ∨ p1) ∨ p5)))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608224517681013392442402458766 : (((((((((p1 → ((((p4 ∧ (((p4 → p3) → p1) → p2)) ∨ p4) → p3) ∧ p2)) ∨ (p1 ∧ p5)) ∧ p5) ∧ True) ∨ p5) ∨ True) ∨ p5) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_185390320032337639426818100693 : ((p5 ∧ (p1 ∨ ((p2 → (p3 → (False → p1))) → (True → p1)))) ∨ ((True → ((p3 ∧ ((p4 → (p1 ∨ True)) → False)) ∨ (False ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307502191485385107169007122710 : (p1 ∨ (True → ((((p2 ∧ p5) ∨ (((p4 ∧ p1) → True) → p4)) ∧ (p5 → ((p2 → p5) ∧ (p3 → p5)))) ∨ (p1 → (p3 → (p5 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106344417288434479792036951497 : (((p5 ∧ (((p1 → True) → p2) → ((True ∧ p4) ∧ False))) ∨ (p3 ∨ (((p2 → True) ∨ ((True ∨ (True ∨ False)) → p3)) ∨ True))) ∧ (True ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168349443403214191512832695746 : (((p3 ∧ p3) ∨ (((((p5 ∨ p5) ∨ (p4 ∨ (False → p4))) ∨ p1) ∧ p1) → (p1 ∨ False))) → (p2 ∨ ((True → (p1 ∧ p2)) ∨ (True ∨ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46917564585749085825546101292 : ((((((((True ∨ p4) ∧ p3) ∧ p2) ∧ p1) ∧ (p5 ∨ ((p4 → (p3 ∨ p4)) → (((p1 ∨ True) ∧ p4) ∨ False)))) ∨ p2) ∨ (p4 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255775491628831115183104380717 : ((True ∨ True) → (True → ((True → (((((p5 → True) ∨ p2) → p2) ∨ p1) ∨ ((((False ∧ p1) → p2) ∨ (p3 ∧ p1)) ∨ False))) ∨ (True → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225704973915287550397296463274 : (((p3 → p3) ∧ p3) ∨ ((((p5 ∧ (((False ∧ p2) ∨ False) ∨ p4)) ∨ (((p2 ∧ p5) ∧ p5) → (p5 → (p5 ∨ p5)))) ∨ (p1 ∧ p2)) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186322383796448269100397948013 : ((((p1 ∧ (((p1 ∨ True) ∨ p2) ∧ p2)) → (p4 ∨ p2)) → False) → ((((((((p4 ∨ True) ∨ p5) → p3) → False) → p5) ∧ p2) ∧ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (((p1 ∨ True) ∨ p2) ∧ p2)) → (p4 ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709116472958119188048950843427 : ((((((p3 ∨ p4) ∧ p5) → ((p4 ∨ p1) ∨ True)) → (((p2 → True) → (p5 → (p4 ∧ (False ∧ p5)))) ∨ (p2 ∧ ((False → p2) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52263630357425185615777322630 : (((p4 ∨ (False → ((((True ∨ ((p4 ∨ p1) ∧ p2)) ∨ p5) → p2) → (p1 ∧ p1)))) → (((True ∨ p2) ∨ ((True ∧ p2) → False)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116816353434968976806538985464 : (((p4 ∨ p1) ∨ ((p4 → (p3 ∧ (((False ∨ True) ∧ ((p3 ∨ p5) → ((p4 ∧ p2) → False))) ∧ (p3 ∨ True)))) ∨ (p1 → p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197938507294165536142665702873 : (((True ∧ p5) ∧ ((p3 ∨ False) ∧ (p3 ∧ p4))) ∨ ((p1 ∨ True) ∨ (((((p4 ∨ (False ∨ (p3 → p2))) ∧ (True → True)) → p5) ∧ p1) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802217230401625249720754419265 : (((p2 → (p2 ∧ (p4 → (p1 ∨ ((False ∨ p3) ∨ (((p5 → True) → ((((p3 ∧ (p4 ∧ (p5 → p2))) → p2) → True) → p1)) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165835644836833307371509041731 : ((((False ∨ p1) ∧ p2) ∨ ((False ∧ (p4 ∧ (p1 ∨ p5))) ∨ ((p3 → (False ∨ p5)) ∧ p5))) ∨ (False → ((p4 ∨ p4) ∧ ((True ∨ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54437583961992433960238797289 : ((((p3 ∨ (p2 ∨ (False ∨ (p1 ∧ p1)))) ∨ True) ∨ (False → (((p1 ∨ True) → p2) ∧ (False → ((((False ∨ p4) → True) ∧ p1) ∨ True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53899485776728698166101026739 : (((p2 ∧ (p1 → ((p2 → p1) → ((p1 ∧ p3) ∧ p4)))) ∨ (True ∧ (((p3 ∧ True) → (p1 ∨ ((False ∨ (p3 ∧ True)) ∨ p5))) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147085353852474718810826460862 : (((((p1 → p5) ∧ (p5 ∨ p2)) ∨ (((((p4 → False) → p3) ∧ False) ∨ ((True ∨ p4) → False)) ∧ p1)) ∧ True) ∨ ((p4 ∨ (p2 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357251051836116778801116602779 : (p5 → ((False ∧ False) ∨ ((False ∨ (False ∨ p1)) ∨ ((((((p5 ∧ (p2 ∧ (False → True))) ∧ (p2 ∧ p2)) ∨ (p4 ∨ True)) → p5) ∧ p5) ∧ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561126419319639243704829206228 : (((p4 ∨ (p4 ∨ ((((((p1 ∨ True) → p3) ∨ (p3 ∧ (p1 ∨ p4))) ∨ p5) ∨ (p4 → ((True ∨ (True → (True ∧ p1))) ∨ p4))) ∧ True))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216810465702587085806207744207 : (((p2 ∧ (p4 ∨ p3)) ∧ True) → (((p1 ∧ p2) ∧ (((p4 ∧ p4) → (p1 ∧ True)) ∨ (True → False))) ∨ ((False ∧ p2) ∨ ((False ∨ True) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64098560787781410546451633824 : ((False ∨ ((p1 ∧ ((((True ∧ True) ∧ p4) ∧ p4) → (False → p4))) ∨ (((p5 → p3) ∨ p5) ∧ (p3 → ((p4 → (p1 ∨ False)) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138160750739262612710379217040 : ((p1 → ((p3 ∧ (((False ∨ (p1 ∧ (p3 → (p4 ∨ (p2 ∨ False))))) ∨ (True → (True ∧ False))) ∨ p2)) ∨ (p1 → p1))) ∨ ((p4 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57589678340063360918084026986 : ((((True → False) ∧ p4) → ((p3 → (False → p4)) → (False ∨ ((((True ∧ p1) ∨ (p2 ∨ (False ∧ True))) → ((False ∧ True) ∨ p5)) → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585545123589982731063538381004 : ((((((((True → (p4 → ((p4 ∨ p1) ∨ (p4 → (p4 ∨ p5))))) ∧ p4) ∧ (False ∧ (True ∨ (True ∧ (p2 ∨ p1))))) ∨ False) ∧ p1) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153254536714320268712981664906 : ((False ∨ ((((False ∨ (p5 → p5)) ∨ p2) → ((p5 ∧ False) ∧ ((p2 → p3) ∧ p3))) ∧ ((p4 ∧ p4) ∧ p5))) → (p4 ∧ ((p2 ∨ p3) ∧ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h18 : ((False ∨ (p5 → p5)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h20 := h12 h18
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h31 : ((False ∨ (p5 → p5)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h33 := h25 h31
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- We need to get the right conjuct of h34 based on <expert-advice>.
    let h35 := h34.right
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135034029083643534044423440668 : ((((((p4 → p4) → (((p1 ∨ p5) → p4) ∧ ((p1 ∧ (p2 → p2)) ∨ True))) → (p3 → p1)) ∧ True) ∨ (False ∨ True)) ∨ (p3 ∨ (p4 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260239559309709147591582291597 : ((p2 → p3) → ((p2 ∨ ((p3 ∨ p3) ∧ (((((p1 ∨ p3) ∨ p5) ∧ p3) → p1) ∧ ((p5 → p2) → p4)))) ∨ (((p4 ∨ True) ∨ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_595340926282261688577959084433 : (((((((False → True) ∨ True) ∨ ((p4 ∧ p3) → (True ∨ (p5 ∧ p3)))) ∧ (True ∧ ((p1 ∨ p1) ∧ ((p2 → p5) ∧ (p3 → p4))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677992583886364129426122241869 : (((((((((p4 → False) ∧ True) → (p4 ∧ ((p4 → p1) ∨ p4))) → p1) ∨ True) ∧ ((False ∨ p3) ∨ p3)) ∨ ((p5 → p1) ∨ (p5 → p5))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718573800369393329894380830850 : (((((p4 → (p5 → p4)) → p4) ∨ ((p1 ∨ (((False ∨ p2) ∨ ((p5 ∨ (p2 → True)) ∨ p3)) ∨ (True ∧ False))) ∨ ((False → p2) ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200012071389957005017537981387 : ((((p2 ∨ p5) ∧ (False → p2)) → (p3 → False)) → (p1 ∨ ((p2 ∧ False) ∨ (((p5 ∧ p3) → ((p4 ∨ False) ∨ (p3 → (p1 → p4)))) ∨ True)))) := by
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
theorem thm_5_vars_47440506191859487103988799714 : (((p3 ∧ ((((p4 ∧ (((((p1 ∨ False) → p4) ∨ p1) ∧ False) ∨ p3)) ∨ p2) ∨ (((False ∧ p4) ∧ p4) → p5)) ∨ p1)) ∨ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38897523958290447942041522105 : (((((p3 → p5) → p5) ∨ (((((p4 ∧ p3) ∨ (p1 → p1)) ∨ (p3 → ((True ∨ (True ∨ p1)) ∧ p5))) ∨ True) ∧ (p2 ∧ True))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134693502564158870728918446986 : (((((True → (p1 ∨ p5)) ∧ p2) ∧ ((((False ∨ p5) ∧ (False ∨ p4)) ∨ (p3 ∧ (p5 ∧ (True ∨ p4)))) ∨ True)) → False) ∨ ((p5 → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168948218415708454774451831216 : ((True → (p4 ∧ ((((p3 ∨ p3) ∨ p5) ∧ p1) ∧ ((False → (p5 → p2)) → (p4 ∧ p3))))) → (p1 ∧ (True → ((p2 ∧ True) ∨ (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



