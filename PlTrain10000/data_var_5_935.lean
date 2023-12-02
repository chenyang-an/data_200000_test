variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41255216995432354417222306643 : ((((((p1 ∨ True) → (p4 ∨ (((p5 → p1) → p2) ∧ p3))) ∧ ((p4 ∧ p3) → (True → False))) ∨ ((p5 ∨ p4) ∧ (p5 ∧ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312069422788877172417848751503 : (p2 ∨ (p5 ∨ ((((p3 ∧ ((True ∧ p2) ∨ True)) ∨ p4) ∧ (p5 ∧ (True ∨ p1))) → (((((p2 ∧ p2) ∧ p3) → p4) ∧ (False ∧ p5)) ∨ True)))) := by
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
  cases h2
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49390032616933288549613017509 : (((((True ∧ ((p2 ∨ ((False ∧ p4) ∧ ((p1 → (p3 ∨ True)) → ((p3 ∧ p4) ∨ p5)))) ∧ False)) → p4) ∧ p3) → ((p1 → False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634282708410061124039624133548 : (((((p3 ∨ (((p4 ∧ (p3 → p3)) → (False ∨ (p1 → p3))) ∧ (((p4 ∨ (True → p1)) → (True → True)) ∨ p1))) → (p4 ∨ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158979721671205756396373794580 : ((p3 ∨ ((((p1 → ((p2 ∧ (p1 ∨ p1)) ∧ p3)) ∧ p2) ∧ (p3 ∧ p4)) ∨ ((p5 ∨ True) → p5))) ∨ (False → (True → (p3 → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247869007228935506725574798345 : ((p1 ∨ p2) ∨ ((p4 → p2) → ((((((False ∨ (False ∧ (p4 → p3))) ∧ p5) ∨ p5) ∨ (True ∨ (False → False))) ∨ p4) ∨ (False → (False ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_982999784091638878737854923514 : (((p1 ∧ ((((((((True ∨ (False → p1)) ∧ p3) ∨ p3) ∧ (False → p2)) ∧ (p1 ∨ p3)) → p1) → p3) ∧ (p4 ∨ (p3 → (True ∧ p4))))) → p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((((((True ∨ (False → p1)) ∧ p3) ∨ p3) ∧ (False → p2)) ∧ (p1 ∨ p3)) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h18 =>
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h21 =>
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h26 := h4 h8
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h27 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h28 := h7 h27
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47739426546887308715640907056 : (((((((p1 ∧ (True ∧ True)) → ((p2 → p4) → (p2 ∧ p4))) ∨ p2) → ((p5 ∧ ((p4 → p1) → p1)) ∧ True)) ∨ p3) → (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168042889975091872088315976401 : ((((p2 ∧ p4) ∨ ((True ∧ True) ∨ p3)) → (((False ∧ False) → (True ∨ (p1 → True))) ∧ p2)) → (((p4 → p2) ∧ (True ∨ (True ∨ p1))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p4) ∨ ((True ∧ True) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137482406529363665779588672400 : ((p5 ∧ ((p2 ∧ (p3 ∧ ((((p5 ∧ p2) → ((True ∧ False) ∧ p1)) ∨ (((p3 ∧ p5) ∨ True) → p4)) ∨ p2))) ∧ p2)) ∨ (True → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66320673737220563558214534175 : ((p5 ∨ (False ∧ (((((p2 ∨ p1) ∧ (((True → p1) ∧ p4) → (p4 ∧ p2))) ∧ p2) ∨ (p4 ∨ (p1 → (p1 → p1)))) ∧ (False → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594898940797950076908489962834 : ((((((True → p3) → (p5 ∧ ((p5 ∨ (p4 ∨ ((p5 ∨ True) ∧ False))) ∧ True))) ∧ (((p4 ∨ ((p5 ∧ p4) ∨ p1)) ∧ p3) ∧ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118262639116652269355030998037 : ((p1 ∨ ((p2 ∨ ((p5 ∧ (p2 → (p2 ∧ (p5 ∧ p4)))) ∨ (p4 ∧ p4))) ∨ (p5 → (p2 ∧ (True ∨ ((p3 → p2) ∨ p3)))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134605217665210624145081814821 : (((((p5 ∧ (((p5 → p3) → (False ∨ False)) ∧ (p3 ∧ ((p2 → p4) ∨ p5)))) ∨ p3) ∧ ((p5 → p2) ∨ p1)) → False) ∨ ((False ∧ p3) → p1)) := by
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
theorem thm_5_vars_69105303113769771500880978561 : ((p5 → ((((p2 ∨ p1) ∨ (p1 → (p2 ∧ (p1 → ((p1 ∨ p1) → False))))) ∨ ((True ∨ (p4 → True)) ∧ (p1 ∧ p2))) ∧ (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958060667194932559364707958399 : ((((False → (False ∨ True)) → (((p4 ∧ (((True ∧ p1) ∨ (p2 ∧ True)) → (p1 → (True ∨ True)))) ∧ (((p3 → p5) ∧ False) ∧ False)) ∧ p1)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (False ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54077781346559711011860033195 : ((((False ∨ p3) ∧ ((p2 ∨ (True ∨ p3)) ∨ (p2 ∨ p1))) → (False ∨ ((p1 ∨ ((p1 ∨ True) ∨ ((p3 ∧ p5) ∧ True))) ∨ (p5 ∧ p5)))) ∨ p1) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706844547088292071296021468102 : (((((p2 ∨ (((False → p3) ∨ True) ∧ p4)) ∧ False) ∨ (((True → (p2 ∨ p4)) ∨ ((True → True) ∧ ((p1 → (False ∨ p5)) → True))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41473920030300733734794562120 : (((((p3 → (((((p1 → p5) → False) ∨ False) ∧ p4) → p2)) → p3) ∨ (False ∨ (((True ∨ True) ∧ ((p3 ∨ p5) ∨ p2)) → True))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319038949737003001083886092281 : (p4 ∨ (((((((True → p3) → (p4 ∨ False)) ∧ (((True ∧ False) ∧ False) ∧ p1)) ∨ True) ∨ p5) → (p2 ∨ p4)) ∨ ((p1 → False) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_55558721392061612020537664689 : (((p3 ∧ (False → (p3 ∧ (p1 → p5)))) → (p5 ∨ ((p2 → ((p5 → p3) ∧ False)) → (((p3 ∧ p3) → (p3 → p1)) ∧ (False ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317106418144951238802226097114 : (p3 ∨ (p5 → ((((False ∨ ((True → (p5 → (p3 → False))) ∨ False)) → (p4 ∨ (p2 ∧ (False ∨ (p2 ∨ p1))))) ∨ (p1 → p1)) ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64682007685067610474427042959 : ((p1 ∨ (p4 ∨ ((p2 → (((((p1 → ((True → (True ∧ p3)) ∨ (p2 → p2))) → False) ∨ p1) ∧ False) → ((p2 → p2) ∨ p4))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54653796652802915363428691674 : ((((((False ∨ p2) ∧ p1) ∨ (True ∨ p4)) ∨ p2) → (p3 ∨ (((p3 ∧ (p5 → p2)) → ((p5 ∨ (p5 ∧ p4)) ∨ True)) ∨ (p4 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979018260675846553000069304 : (True → (((((False ∨ p2) → ((p3 ∧ p2) → (p5 ∧ (((p1 ∨ p4) ∨ (p3 → p3)) ∧ p3)))) → (p3 ∨ p3)) ∨ ((p5 → False) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56260000611017659139686528906 : (((p2 → ((p1 ∨ False) ∧ p2)) ∨ (True → (p3 → (p2 → (False ∨ ((True ∨ True) → (((p4 ∧ (True ∨ p5)) ∨ False) ∨ (True ∧ p3)))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113473134690924615320413746272 : ((((((((p4 ∨ True) ∧ p4) → (((p4 → (p5 ∧ p4)) ∨ (False → p1)) → p2)) ∧ p4) ∨ p5) ∧ (p4 ∧ p4)) ∨ (p5 → True)) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48849905956734360495999802415 : (((p2 ∨ (((p4 ∧ (p1 ∧ p4)) ∧ (False ∨ (((p3 ∧ p2) ∨ p1) ∨ (True ∨ p2)))) → (True ∧ (p2 ∧ p1)))) ∧ ((p2 ∧ p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317802440109029042645110048983 : (p4 ∨ (((((p4 ∨ (p1 ∨ p2)) ∨ p5) ∨ (p5 ∧ True)) → (((False ∧ (((p3 ∨ p1) ∨ p3) → (p1 → (False ∧ p2)))) ∧ False) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167257757255610515122197392816 : (((((p5 → ((True ∨ (True ∨ (True → False))) ∨ (True → p3))) ∨ (True ∧ p3)) ∧ p4) → p2) → (((((True → True) ∨ p1) ∨ p1) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True → True) ∨ p1) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304072296634249791185157472425 : (p1 ∨ ((p2 ∨ (p3 ∨ ((((p2 ∧ (p1 ∨ p5)) ∧ ((p5 → (True → False)) ∨ ((True ∧ ((True → True) ∧ True)) ∧ p2))) ∨ p5) ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55248463881534899459214786937 : ((((p2 → p4) ∧ ((p5 ∨ p4) → p2)) ∨ ((p1 ∧ p3) ∨ (((True ∨ (p1 → (True ∨ (((p1 ∧ p1) → p2) → True)))) ∧ p4) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117616934817603156867841775095 : ((p3 ∧ (((((True → (p2 ∧ ((p1 → (p1 ∧ (False ∧ p2))) ∨ (p2 ∨ p5)))) → ((False ∨ p4) → True)) → p1) ∨ False) ∧ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40834762066356212397614932518 : ((((p2 → ((((p3 ∧ (False ∧ (False ∧ p1))) ∧ ((p4 → True) ∨ p4)) → (p5 ∧ ((p5 ∧ True) ∨ True))) ∨ (p3 ∧ True))) → p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217350276221887497802625577413 : (((p2 ∨ (p4 ∨ True)) ∨ p5) → ((True ∧ (True ∨ p5)) → (p4 → (p2 ∨ (((False ∧ ((True → ((p3 ∨ p4) ∨ p5)) ∨ True)) → p3) ∨ p4))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57910030006245535942540721438 : (((p4 ∨ (p2 → False)) → ((p4 ∨ (p2 ∨ (False ∨ ((((p5 ∧ p2) ∧ p3) → p1) ∧ (p1 ∧ p2))))) ∧ ((p1 → (p2 ∧ p4)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694488856426818354010023898655 : ((((True ∧ (((p3 ∨ (p5 ∨ (((True ∨ False) → p3) → p5))) → p5) ∧ p2)) ∨ ((p5 ∨ (True → True)) ∨ (((p5 ∧ p4) → p1) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234290131806709756010370785842 : ((False → (p4 → p1)) → (((False ∨ ((p5 → (p4 → ((p4 ∨ True) → False))) → p1)) → (p2 → p3)) ∨ ((False ∧ False) → (p2 ∧ (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62409815355545873382162688063 : ((p3 ∧ ((((p2 ∧ p1) → p1) ∧ (True → (p3 ∨ True))) → ((True ∨ p2) → (((p2 ∧ p1) ∨ True) → (((p5 ∨ True) ∧ p4) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787106344392087678534010179213 : (((p4 ∨ ((True ∧ p2) → ((((p2 ∨ p4) → True) ∧ p3) → (((((p4 → p1) ∧ p1) → p4) ∨ (False ∨ (p1 ∨ p3))) ∧ (True ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739106921445761040547312310261 : ((((p3 ∧ p5) ∨ ((((((True ∨ (((p5 → False) → p3) → p1)) ∨ p3) ∨ p4) ∧ False) ∨ p2) ∨ (p3 ∨ (True → ((p3 ∧ False) → True))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323899805364705152578761412220 : (p5 ∨ ((((p5 ∨ p3) → ((p1 → True) ∨ p4)) ∧ ((p1 ∨ ((True ∨ True) ∧ True)) → p5)) ∨ (((p5 ∨ True) ∨ ((p1 ∨ p1) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186638078373058044914646399186 : (((p5 ∨ (((p4 ∧ False) ∧ p4) ∧ (p2 → p1))) → (p2 → p5)) → (p4 ∨ ((p3 ∧ (p1 ∨ p4)) ∨ (((True ∨ p1) ∧ (p2 ∨ False)) → True)))) := by
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
theorem thm_5_vars_349416462207243173845370092650 : (p3 → (p4 → (((True ∨ (((p5 → p2) → False) → False)) → (p2 → ((p2 ∧ p5) ∧ False))) ∨ (False → (p5 ∧ (((p1 ∨ True) ∧ p4) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
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
theorem thm_5_vars_47296720060951729404289743781 : (((((p3 ∧ False) → p3) ∧ ((False ∧ (p5 ∧ (p5 ∨ ((False ∧ (p1 ∨ ((p1 ∨ (p4 → p3)) ∨ p4))) ∧ False)))) ∨ p5)) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309285995850444293591621198544 : (p2 ∨ ((True → (p2 → (False ∨ ((((((p2 ∧ ((True ∧ False) ∨ (p2 ∨ p1))) → p1) ∨ p2) → (p3 ∨ p2)) ∨ p3) ∨ False)))) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160682937636374358511134764943 : (((((p3 → False) ∨ (p2 → p2)) → (p3 ∧ p5)) ∧ ((p2 ∨ p2) ∧ ((False → True) → (p3 → p3)))) → (((p4 → False) → (p2 ∧ p4)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217993608987545105484324452821 : (((p4 ∧ p5) ∧ (p5 ∨ p3)) → ((((True ∧ (((p2 → (((p2 ∨ p5) → p5) ∧ False)) ∧ False) ∧ p2)) ∧ ((True ∨ p1) ∨ False)) ∨ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661304213354284082628163484240 : (((((((((((p2 ∧ p5) ∨ p5) → (p1 → False)) → (p5 ∧ (p2 → (p3 → True)))) ∨ p3) ∨ p5) → True) → (p1 ∨ p4)) → (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39056745422257500077042667444 : ((((p3 ∧ p1) ∨ (((((True → (((True ∨ p2) ∨ p4) → p5)) ∧ (p5 → p1)) ∧ p3) ∧ p5) ∨ ((p2 → True) ∨ (p2 → p4)))) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54520361667759985767709011667 : ((((p3 ∨ p1) ∧ (p3 ∨ ((p3 → True) → False))) ∨ ((((p4 ∧ (p2 ∧ (False → True))) ∨ False) ∨ p4) ∧ (p2 ∧ ((p5 ∧ p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53756955073380938188105563111 : (((((p1 ∧ False) ∨ (p3 ∨ (p1 ∧ (p2 → p1)))) ∧ p1) ∨ ((False → ((((True ∨ p5) → True) ∧ p4) → ((False ∧ False) ∨ True))) ∨ p3)) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134070361225501110066405716397 : (((((((False ∧ ((p2 ∨ p3) ∧ (p5 ∨ p1))) ∧ False) ∨ (True ∧ ((p3 ∨ (False ∧ p3)) ∨ p2))) → False) → p3) ∨ p4) ∨ (True ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599957980927925055614709303927 : (((((p5 ∧ p3) → ((((((False ∧ p1) → (p4 ∨ (p1 ∧ (((True ∨ p3) ∧ (p4 → p3)) → p3)))) → False) ∨ p1) ∧ p1) ∧ p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201094579387271917069333372822 : ((True → (((p3 ∧ True) ∧ (False → p4)) ∧ p1)) → ((p1 → True) ∧ ((((p4 ∨ True) → (False ∧ False)) ∧ (p4 → p4)) ∨ ((p4 ∨ p4) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123100231004948909380426951975 : ((((((((p3 ∧ p3) ∧ ((p3 → ((p1 → p4) → False)) → p1)) → False) ∧ p2) ∨ True) ∨ (p5 ∨ p4)) → ((p2 → p5) → p1)) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678364760629657298165939961620 : (((((p3 ∧ (True ∧ ((p2 ∨ p1) ∧ p3))) ∨ (False ∨ ((True → p2) → ((p4 ∧ (p2 → p5)) ∧ p4)))) ∨ (((p2 ∧ p4) ∧ p3) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_615733872650434720823042011743 : (((((False ∧ (((p4 ∧ True) ∨ ((True → p1) → True)) ∨ ((p3 ∧ p3) ∨ p5))) ∧ (((p4 → True) ∨ ((False → p5) → p1)) → p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_55352340476119271377384528888 : (((p2 → (((p3 ∧ False) → True) → False)) ∨ (((p5 → (True ∧ p2)) ∧ p2) → (p3 ∧ (((True ∨ (p3 → (p5 → p2))) ∨ False) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41502722477647891127277285753 : (((((p1 ∨ p3) → (False → (p1 ∨ (((p4 ∨ p5) ∧ p5) ∧ p3)))) → (((p3 ∨ False) ∧ (p2 → (p2 ∧ (True ∧ p2)))) ∨ p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609478568965530877458204365580 : (((((False ∧ (p4 ∧ ((((p2 → ((p1 ∧ p4) ∧ True)) ∧ (((True ∧ (p3 → (p3 ∨ p2))) → p1) → p1)) → p1) ∨ p3))) ∨ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178776956110314615544902108187 : (((False ∨ (p4 ∨ p1)) ∧ (p3 ∧ (p4 → (p4 ∧ (p3 ∧ (True ∨ p4)))))) ∨ ((False ∧ (((p4 ∧ p3) → p1) ∨ p4)) → (p2 ∨ (False → True)))) := by
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
theorem thm_5_vars_669660504326949377970252410599 : ((((((((p3 → p4) ∧ (p2 ∨ p3)) ∨ (((p4 → p4) ∧ True) ∧ (True → False))) ∨ p3) → ((p1 → True) → p4)) ∨ ((p2 ∨ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348204920711833717814977399734 : (p3 → ((False → p4) → (((p1 ∧ (False ∨ (True → True))) → False) ∨ ((((((((True ∧ p3) ∨ True) ∨ True) ∧ False) ∧ True) ∨ p4) ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185580673795864584836100229642 : ((p5 ∨ (((p3 ∧ p5) ∨ (((p4 → False) ∧ p5) ∧ p3)) ∨ p1)) ∨ ((p3 → p4) → ((p4 → (False ∨ (False → ((p2 ∧ p4) ∧ p1)))) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217437031808513016563854858347 : (((p3 → (p1 ∨ p2)) ∨ True) → ((True → (p5 ∧ ((p3 → (True ∧ p2)) ∧ p5))) → (((p1 ∨ ((p5 ∨ (p1 ∨ p2)) ∧ p4)) ∨ True) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52795191529629372505340389080 : ((((p2 ∨ ((p4 ∧ ((False → p2) ∨ p4)) ∧ True)) ∧ ((p2 → False) → p1)) → (p4 ∧ (p1 → ((p5 ∧ p5) → (False ∧ (p2 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305168463481107183244411399720 : (p1 ∨ ((((True ∧ ((((p3 ∨ p3) → p2) ∨ (p4 → (p1 ∧ (False ∨ p2)))) ∧ p1)) ∧ p1) ∨ (p4 → p4)) ∨ (((p2 → p5) ∨ p2) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116213328511329538184330092521 : ((((p3 ∧ True) ∨ False) ∨ (False ∧ ((p2 ∨ (True ∧ (False ∧ ((p3 → False) → False)))) ∧ (False → (p3 ∧ (p3 ∨ (p4 ∧ p5))))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164682523271659828188177098276 : (((((p1 → False) ∨ (((False → p1) → p2) ∧ ((p5 ∨ p2) ∨ (p3 → p1)))) ∧ p1) ∨ p1) ∨ ((p5 ∧ p2) ∨ (((p4 ∧ p5) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147907340342379414816669482861 : ((((True ∨ ((p3 ∧ (p4 → (True ∨ (p2 ∨ p2)))) → (True ∧ ((p4 → p3) → p1)))) → p2) ∧ (True → p1)) ∨ ((p3 → p3) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67394512574259769702502363910 : ((p1 → ((p2 ∨ (False → (((True → p4) ∧ True) ∨ (p1 → (p3 ∨ ((((p2 ∨ True) ∧ (p5 ∨ p3)) ∧ (p5 ∧ p1)) ∧ p2)))))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147331184860043285968821120201 : (((((p1 → (((p2 ∧ (False ∧ ((p1 ∨ True) → (p5 ∧ True)))) → p3) ∧ True)) ∧ False) ∨ (p5 → False)) ∨ False) ∨ ((p4 → p5) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158147891085685389266030196657 : (((p1 ∧ (p5 ∨ (p2 ∧ p5))) ∨ (((((p1 ∨ p4) → (p3 ∨ p5)) ∨ p1) ∧ True) → (p3 → p4))) ∨ (True → (((False ∧ p5) → p5) ∨ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319383714062681613331427707653 : (p4 ∨ ((p1 → ((((p4 → p4) ∨ p4) ∧ (((False ∧ False) ∨ p4) ∨ p3)) ∧ p4)) ∨ (((p4 ∧ p4) ∧ p3) ∨ (True ∨ (p3 ∧ (False → p1)))))) := by
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
theorem thm_5_vars_232109301526765330443194656963 : (((p5 ∨ p1) → p2) → ((p2 ∧ (p3 ∨ p1)) ∨ ((((True ∧ (p1 → (p3 → p5))) ∧ ((False ∨ p3) ∧ p3)) ∧ p5) ∨ (p5 → (p4 → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62791982439314501227819102306 : ((p4 ∧ ((True → (((((p5 ∨ (p3 ∨ True)) ∧ p3) ∨ (p3 ∨ p4)) ∧ p5) ∧ (p3 ∨ p4))) ∧ (((p2 → p4) → p3) ∧ (p5 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134021688813831241944157800486 : (((((((p1 → True) ∨ (((p4 ∨ False) → (p5 ∨ False)) ∧ (p1 → (p4 ∧ (False ∧ p5))))) → p2) ∨ False) ∨ True) ∨ p2) ∨ ((False ∧ p2) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180067753403274135616410811534 : (((p1 → ((False ∧ ((p4 ∨ p3) ∨ ((p1 ∨ p3) ∨ True))) → p1)) ∨ True) → (((p4 → (p5 → (p3 → False))) ∨ False) ∨ ((p2 ∧ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245953777261605091818377173662 : ((p4 ∧ True) ∨ ((p4 → (((False ∨ (p2 → False)) → (p1 ∨ False)) ∨ (((p2 ∧ p4) ∨ (False → ((p2 → p4) ∧ False))) ∨ (p1 ∨ p4)))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768721496001327454137262491536 : (((p5 ∧ (((p1 ∧ p5) → ((p2 ∧ p3) → (p1 ∧ (True ∧ False)))) → ((p1 ∧ (((p3 ∨ (p4 ∨ p5)) ∧ (p5 ∧ p2)) ∨ p4)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24717459182188050539238195127 : ((((False ∧ False) ∧ p1) ∨ (((False ∧ ((False → p1) → (True → p2))) ∨ True) ∨ ((p1 → (True ∧ (p3 → ((p3 → p5) ∨ True)))) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_702796857571763118545381355810 : ((((((p5 ∧ (p5 ∧ False)) ∧ False) ∧ ((True → p3) ∨ p5)) ∨ ((((((False ∨ p3) ∨ p5) → (False ∨ False)) ∨ p3) ∨ (True ∧ p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45487915981024422921895781699 : (((False ∨ ((p2 ∧ p2) ∨ ((((((False ∧ p1) → p1) → (p1 → False)) → ((False ∨ (False → p5)) → False)) ∧ (p1 ∨ p5)) ∨ p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388149397874158566131717516145 : (((((((((p3 ∨ (p4 ∧ (False ∨ True))) → (p3 → ((p3 ∧ False) ∨ p4))) ∨ p1) ∨ p4) ∨ False) ∨ (((p4 ∨ p5) ∧ p5) ∧ p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_358049490510436556782348707319 : (p5 → (p1 ∨ ((((p5 ∧ p2) → (((p2 → False) ∨ ((p5 → p1) → p4)) → (p4 ∧ ((True → p3) ∧ p1)))) ∨ True) ∨ ((p3 ∧ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783503651625054220654227434994 : (((p3 ∨ ((((p4 → ((p2 ∨ p2) ∧ False)) → ((False → p4) ∧ True)) ∧ p3) ∨ ((((p1 ∨ True) ∨ (p3 → p4)) → (p2 → p1)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55592332191433983972349852270 : (((p4 ∨ ((p1 → True) ∧ (p5 ∨ p3))) → (p4 ∧ (p3 ∧ ((p5 ∧ ((((p2 ∧ (p5 → p5)) ∧ (True ∧ p5)) ∨ False) ∨ p5)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707227782375717162342484140719 : (((((p4 → (p3 → (False ∧ (True ∨ True)))) → p3) ∨ ((p3 ∨ True) ∨ ((p2 → p5) → ((p3 ∨ ((p4 → (p4 → p3)) ∧ p5)) ∧ p3)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_175507166402246385262527671185 : ((p3 → ((p5 ∧ True) → (p4 ∨ ((p1 ∧ (p5 ∧ p3)) → ((p1 → p5) ∨ p2))))) → (((p1 → p1) → p3) → (p1 → ((p5 → p3) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113509155923870742753004410534 : (((((p3 → False) → ((p2 ∨ True) ∧ ((p3 ∨ (True ∧ (p3 → p1))) → True))) → ((p1 → (p3 ∧ p5)) ∧ p5)) ∨ (p2 ∨ p3)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148893123253242318890501366371 : ((((p5 → p5) → (p4 ∨ p1)) ∨ ((((True ∧ (p3 ∧ p1)) → (p5 ∧ p3)) → p3) ∨ ((p3 ∧ True) → p3))) ∨ (p4 ∧ (True ∨ (False → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683873252747581535975779457735 : (((((p5 ∧ (p3 → (((True ∨ p3) → ((p5 ∨ p1) ∧ (p2 → p5))) → (False ∧ True)))) ∨ p1) ∨ ((p4 ∧ ((p2 ∧ True) ∧ p3)) → p4)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107064820916681722511179898576 : (((((p5 → p1) ∨ p3) → False) → ((p2 ∧ (p3 → (False ∧ (((((p3 → p5) ∨ True) ∧ p2) → False) → False)))) ∨ (True ∨ p3))) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193541892396724949226293992795 : (((p1 ∧ p2) → ((True ∧ True) → (True → (p4 ∧ p4)))) → (((p1 ∧ p4) ∨ (p4 → (p3 → p2))) ∨ ((p3 ∧ (False ∨ (p1 ∧ False))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172627268846901306472173665234 : (((p2 ∧ p5) ∧ ((p1 ∧ (p2 ∨ p2)) ∨ ((p5 ∨ (False → (p1 ∨ p5))) → p3))) ∨ ((True ∨ p3) ∨ ((True → p4) ∧ (p1 → (p5 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141440265889067874845417423332 : ((((p5 ∧ p4) ∨ p5) ∧ (((p1 ∨ ((p5 → False) ∧ p2)) ∧ (((p5 → p2) → (p1 ∧ p2)) ∨ p5)) ∨ (p4 ∨ False))) → ((p5 ∧ p2) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
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
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- False on the left can always be used.
        apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158170144450067060050283279669 : (((((False ∨ True) → False) → False) → (((False ∨ (False → (p5 ∨ (True ∧ (p3 ∧ False))))) ∧ p3) → p5)) ∨ (False → ((False → p2) → (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671165585742568138484477469716 : ((((p2 ∨ ((True ∨ p2) → ((((((p2 ∨ (p2 ∨ p2)) ∧ (p3 → True)) → True) ∨ False) → (p5 ∧ p3)) ∨ p3))) ∨ (True ∧ (True ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147785316006765495292611149034 : ((((p5 ∨ p2) → ((False → ((p5 ∨ ((p5 ∧ p4) ∧ p3)) → ((p3 ∨ (p1 ∧ True)) → p1))) ∨ False)) → p3) ∨ (p3 → (False → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



