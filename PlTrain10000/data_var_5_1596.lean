variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319056726654798958351393326356 : (p4 ∨ ((True ∧ (p1 ∧ ((p2 → p2) ∧ (p3 ∨ (p4 → (p4 ∧ ((p3 → p5) → ((p5 ∨ p2) ∧ p3)))))))) ∨ (p1 → ((True ∧ p1) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226453439961433909205313956554 : (((p1 → p3) ∨ p3) ∨ (p2 ∨ ((((p5 ∨ False) ∨ ((p1 → p2) → (p5 ∨ (True → False)))) ∧ p4) → ((p2 ∨ p2) ∨ (p5 → (p5 ∧ True)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350003024444139343858908010867 : (p4 → (((False ∧ ((((p2 → (p1 ∨ p5)) ∧ (False ∧ ((p3 ∨ (p4 ∧ p2)) ∨ ((True → p2) ∨ p1)))) ∧ False) ∨ (False ∨ p5))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342080672323059196209506931712 : (p2 → ((False ∨ (p2 → ((p3 → (((p4 → ((p4 ∧ ((p5 ∧ p3) ∧ False)) ∨ p5)) ∨ p3) ∧ p4)) → (p5 → p1)))) → ((p1 ∨ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194173050749108650995184065855 : ((p2 → (((p1 → p1) ∧ (p4 → p5)) ∨ (p1 ∨ True))) → (((p3 → ((False ∧ (True ∨ p4)) → p4)) ∧ ((p3 ∨ p5) ∨ (True ∧ True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58982719597873348188935220869 : (((p2 ∧ p5) ∨ (True ∧ (False ∧ (((p3 ∧ ((((p3 ∧ False) ∧ ((p5 ∧ True) → False)) ∧ p5) ∧ p1)) ∧ (p2 ∧ (False ∧ p5))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658539860716717962360767813109 : ((((p2 ∨ (((p1 → p3) ∧ ((p5 → (p1 ∨ False)) ∨ p4)) → (False ∨ (p2 ∨ ((p1 ∧ (p2 → (p3 → p3))) ∧ True))))) ∨ (False → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340822545846337588665732524335 : (p2 → ((((((False ∧ (((p3 ∨ True) ∨ (p4 → True)) ∧ p5)) ∧ False) ∧ p1) ∧ ((True ∧ p1) ∧ ((p2 ∨ p1) → p3))) ∨ (p1 → p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149913154850287123193711544681 : ((p3 ∨ ((p1 ∧ (p5 ∨ (((False → False) → (p2 ∨ p4)) ∧ ((p2 ∧ p5) → ((p3 ∨ p3) → p3))))) ∨ p3)) ∨ ((p4 ∧ False) → (p1 ∨ p4))) := by
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
theorem thm_5_vars_340616509475635683818423900256 : (p2 → ((False ∨ ((((((p4 → False) ∨ (False ∨ ((True → p1) ∧ p5))) ∧ (True → p3)) ∧ (p1 ∨ ((False ∨ p4) ∨ False))) ∧ p3) → p1)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h15 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h16 := h9 h15
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
            have h28 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h21, we can now drive its conclusion.
            let h29 := h21 h28
            -- One of the premise coincides with the conclusion.
            exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137470334874106485121563457118 : ((p4 ∧ (p4 ∨ (p4 ∧ (p2 ∨ (((p5 ∨ (True ∨ ((p3 ∨ p5) ∧ p2))) ∨ False) → ((True ∧ p2) ∨ (False ∨ p2))))))) ∨ ((p1 ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230903160828582438601532433026 : (((p2 ∧ p4) ∨ True) → (((p1 ∨ ((p3 ∧ ((p1 → p3) → p3)) ∧ p4)) → ((((p3 ∨ p2) → ((p1 → False) ∧ False)) → True) ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_598263899755416964156193206198 : (((((False ∧ (p1 → False)) ∨ (((((True ∨ p2) → (True → ((p2 ∨ p1) → ((p5 ∨ p1) ∧ True)))) ∨ p3) ∨ True) ∧ (True → True))) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117698768466245719288466159290 : ((p3 ∧ ((False ∨ True) → (p2 ∨ ((p1 → (p1 ∨ p3)) ∧ ((p1 → (p5 ∧ (p2 ∧ p1))) → (False ∨ (p5 ∨ (p2 → False)))))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237916860316125196274169552236 : ((True ∨ True) ∧ (p1 ∨ (((((False ∧ False) ∨ p3) → (p5 ∧ (p4 ∧ (((p2 → p3) → False) ∧ (True ∨ p4))))) ∧ ((p3 ∨ p3) ∨ p1)) → p1))) := by
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
      have h6 : ((False ∧ False) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (p2 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((False ∧ False) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : (p2 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h20
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63140349123113641629902310449 : ((p5 ∧ ((p4 ∧ ((((p5 ∧ p2) → ((p3 ∧ (False ∧ p5)) ∧ p5)) → ((p3 ∧ (p2 ∧ (True ∧ (p4 ∨ p3)))) ∧ p4)) ∧ p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97004482788993746993620976209 : ((p1 ∨ (p4 ∧ (((p4 ∨ ((((p1 ∧ True) ∨ p4) ∧ (False → (p5 → p3))) ∨ p2)) → (False ∨ (p4 → False))) ∧ (False ∨ (p4 ∨ p3))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h11 : (p4 ∨ ((((p1 ∧ True) ∨ p4) ∧ (False → (p5 → p3))) ∨ p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h12 := h6 h11
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h16 := h14 h15
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : (p4 ∨ ((((p1 ∧ True) ∨ p4) ∧ (False → (p5 → p3))) ∨ p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h22 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h23 := h21 h22
          -- False on the left can always be used.
          apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135288604150443564690628211206 : (((p4 → (((p4 ∧ p4) ∨ p1) ∨ ((((p1 → ((p4 ∧ p3) ∧ p2)) ∨ (True → p4)) → p2) ∧ p1))) → (False ∨ p5)) ∨ (True ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64883161658563972337482667246 : ((p2 ∨ (((((p2 → p3) ∧ p3) ∨ (((((p4 → p2) → p4) ∨ p5) → ((p4 ∧ p1) ∨ p5)) → False)) ∨ p3) ∧ ((False ∨ p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763933520657670577409100732729 : (((p3 ∧ (True → ((p3 ∨ (((((p2 ∧ (p5 ∧ p5)) ∧ p1) ∧ (False → p1)) ∨ False) ∨ (((p1 ∧ p3) ∧ p4) → (False → p3)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321474263543255537452183165547 : (p4 ∨ (p1 → (((p5 → (((((p2 ∨ True) ∨ True) ∧ p4) ∧ (True ∧ False)) ∧ ((((p5 → (p2 ∧ p3)) → p4) → p1) → p3))) ∨ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192730066661588831972530142074 : ((((True ∨ p3) ∧ (True ∨ ((p2 ∨ p1) → p3))) → p1) → ((p5 ∨ p1) ∨ (p5 → ((p3 ∧ ((p3 → p2) ∨ ((False → p5) ∧ False))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p3) ∧ (True ∨ ((p2 ∨ p1) → p3))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340825877959640579880408669306 : (p2 → (((p1 ∧ ((((True ∨ (((True ∧ (False → (p4 ∧ p2))) ∨ (True ∧ True)) ∧ (p1 → p4))) ∧ p1) ∧ True) → p5)) ∨ (p3 → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702819552563219438519944489550 : (((((p4 ∧ ((p2 → p5) ∧ p1)) ∧ ((p1 ∧ False) → p4)) ∨ ((p4 ∧ False) ∧ (p3 → (p2 → (False ∧ (p4 ∧ (p2 ∨ (p4 → p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757908821789843854662571783723 : (((p1 ∧ (p4 ∨ (((p4 ∨ ((False ∨ (p1 → (True ∧ p4))) ∨ (((p5 ∨ p4) ∨ p1) ∨ (p1 ∧ p4)))) ∨ (p3 → p1)) ∨ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50975075023139509389085971522 : (((((True → p5) → p3) ∧ ((p3 ∧ (p4 ∨ (False ∧ p4))) ∨ (False ∧ (p3 ∨ (True ∧ True))))) ∧ ((p4 ∧ p2) ∨ ((p1 ∨ p4) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193013300446915506066348241630 : (((((True → p2) → True) ∨ (False ∧ p2)) → (p2 → p5)) → (((p1 → ((p5 ∨ p5) → p5)) → False) → ((True ∧ (p4 ∨ p3)) ∧ (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → ((p5 ∨ p5) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p1 → ((p5 ∨ p5) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h9
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196575127974885684828731916376 : ((p4 → (((False → (True ∧ p1)) ∧ True) ∨ p4)) ∧ ((p4 → (((p2 → (((p1 ∨ p1) ∧ p4) → p5)) → p4) ∨ p3)) → ((True → False) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116501942580375752948939269326 : (((p3 ∧ p4) ∧ ((p4 ∧ False) ∧ (((((p2 ∧ (((p1 ∨ p1) ∨ p4) ∨ p5)) → p5) ∧ p4) → (p4 → (p1 → False))) ∨ True))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51353872419391655814574794898 : (((((((p5 → p1) ∨ (p1 ∨ True)) ∨ (p2 ∨ ((p1 ∧ p5) ∨ p2))) ∧ (False → False)) ∧ p5) → ((p2 ∧ p2) ∨ ((False → p2) ∨ False))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h21
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306187289619150100367709327288 : (p1 ∨ ((False ∨ (p3 → False)) ∨ (((p2 ∧ p3) ∧ ((p3 ∨ ((p5 ∨ ((False ∨ p5) ∧ p1)) ∧ (p5 ∧ p4))) → p3)) ∨ ((False → True) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42425735777541473230685461601 : (((p5 ∧ (((p3 → ((p4 → p3) → (p3 ∨ p4))) → (p2 → (p4 ∧ False))) ∨ ((True → True) → ((p3 ∨ (True → p3)) → p4)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47145905244670130161615922757 : (((((p1 ∨ ((((True ∨ (p4 → p3)) → False) ∧ False) ∨ (p2 → False))) ∧ (p2 → p1)) ∨ (((p1 ∨ p4) → p4) → True)) ∨ (p5 ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115744358877403663777133095309 : ((((True → True) ∨ (p4 → (True ∨ False))) → (p4 ∧ ((p5 ∨ ((False ∨ (((p3 ∧ True) ∧ False) ∧ True)) → p2)) ∧ (p3 ∧ p4)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781066597854277525877885282218 : (((p2 ∨ ((p3 → p2) ∧ ((p1 ∧ (p2 ∧ (False ∧ ((p3 ∨ (p3 ∨ p5)) ∨ (p4 ∧ p3))))) ∧ (p1 ∧ (p4 → (True → (p4 ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165369284891819785930430198509 : (((((p4 ∧ False) ∧ ((p5 ∨ (False ∨ (p3 ∨ True))) ∨ True)) ∨ False) ∨ (p4 ∧ (p4 → p2))) ∨ (True → ((p2 ∨ p3) → ((p1 → p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49137501567611596163352436458 : (((((True ∧ p1) ∨ ((p5 → ((True → p5) ∨ p3)) ∧ p2)) ∧ (((p2 ∨ p5) ∧ (p5 → (True ∧ p3))) ∧ False)) ∨ (False ∧ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61728594002046022460492497575 : ((p1 ∧ (p1 → (((p5 → p1) ∧ ((p4 → ((True ∧ ((p4 → False) ∧ ((True ∧ (p1 ∧ False)) → (p5 ∧ p1)))) ∧ p3)) ∨ p1)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253780814448776157742814545416 : ((p1 ∧ p2) → (((p5 → p2) → (((p1 → ((p5 ∨ (p3 ∨ (p2 ∨ True))) → (((True ∧ p3) ∧ p2) ∧ (False → p5)))) ∨ p1) ∨ p2)) ∧ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49065182757077660621034991556 : ((((((p5 → p3) ∨ ((False ∧ (True ∧ p4)) ∧ p4)) ∨ (((p5 ∧ p4) → False) ∨ (p4 ∨ p1))) ∨ (p5 → True)) ∨ (p1 ∧ (True → True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231939027443334116197413820547 : (((p1 ∨ True) → False) → ((False ∨ p5) ∧ ((True → ((((False → p2) ∨ (p4 ∨ (False → p2))) ∨ (p1 → (p5 ∨ p5))) ∨ (False ∧ False))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56190155843053401925926687207 : (((p4 ∧ (False → (p2 ∧ p2))) ∨ (True ∧ (((True → False) ∧ (p2 ∨ p3)) → (p1 → (True ∧ (((False ∨ p5) ∧ (p1 ∧ False)) ∧ p5)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h19 := h15 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h22 := h15 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h27 := h23 h26
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h30 := h23 h29
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1822911665562718757559128076 : ((p5 → ((p4 → (False ∨ (p2 → ((p3 ∧ (p3 ∨ False)) ∨ p1)))) ∨ (p1 ∨ ((p5 ∨ p1) ∨ (p2 → False))))) ∨ (True ∧ (p3 → p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308504236893876997249616054918 : (p2 ∨ (((((True → True) → p1) → (((False → (p5 → ((p4 ∧ p3) ∨ p3))) ∧ (p3 ∨ p2)) ∨ False)) ∨ (False → ((p5 ∨ p2) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315105156325493862758430462476 : (p3 ∨ ((p5 → (True ∨ (p3 ∨ (p2 ∨ p3)))) ∧ ((p5 ∨ False) ∨ ((p5 ∧ (((False ∨ p3) → (True ∧ (p1 ∧ False))) ∧ (True ∧ False))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230892065272958505799399395192 : (((p2 ∧ p2) ∨ True) → ((p5 ∨ ((p3 ∧ (((((p4 → (False ∧ True)) ∧ p1) ∨ (False ∨ (p1 → p1))) ∧ p2) ∨ False)) ∧ p4)) ∨ (False → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320141096541825285238093366141 : (p4 ∨ ((p5 → (p5 ∨ p2)) → ((((p2 → p5) ∨ (p3 ∨ ((p1 ∨ (p4 → p1)) ∧ ((p2 → (p2 ∧ p5)) ∧ (p1 ∧ False))))) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36790045743565543523204053720 : ((p5 → ((p5 ∨ (p2 ∨ (((((p5 → p3) ∨ (p4 ∨ True)) ∨ p5) ∨ ((p2 ∧ (True ∧ False)) ∧ p4)) ∨ p2))) → (p1 ∨ (p3 → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h13
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- Disjunctions on the left can always be decomposed.
              cases h14
              case inl h15 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h16
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h17 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h18
                -- True on the right can always be proven directly.
                apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h22.left
          let h25 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302011627394179064826274547429 : (False ∨ (True ∧ (((((((False ∧ (p5 ∨ False)) ∨ (p5 → (p2 ∧ (False ∧ p4)))) ∨ False) ∧ p5) ∧ p5) ∧ ((p4 ∨ True) ∨ (False → p3))) ∨ True))) := by
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
theorem thm_5_vars_159022065721006969065251934873 : ((p4 ∨ (((p3 ∧ True) ∨ (p2 → (True → p2))) → (((p2 ∨ p5) ∧ p1) ∧ ((p5 ∨ p4) → p3)))) ∨ ((p5 ∧ False) → ((True ∨ p5) ∨ p3))) := by
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
theorem thm_5_vars_232085017097599157325325927559 : (((p4 ∨ p4) → False) → ((p3 → (True ∧ ((((p3 ∧ (p4 ∧ p5)) ∧ False) ∧ ((p2 → (p3 ∧ p4)) ∧ p2)) ∧ p1))) ∨ (False → (p5 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42174174730456590667437608342 : (((True ∧ ((True → (((True ∧ (((p4 ∧ (True → (p2 ∧ p3))) ∧ p3) ∨ p5)) ∨ (p1 ∨ (False ∨ p4))) ∧ (True ∧ p1))) ∧ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320104414297004704760707973554 : (p4 ∨ (((p5 ∨ True) → False) → (((((p3 ∨ p4) ∨ (p5 ∨ True)) ∨ p5) → ((True ∧ p4) → (p1 ∨ ((p5 → p2) ∧ p4)))) ∧ (p3 → True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h13 := h1 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : (p5 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h20 := h1 h19
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : (p5 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- False on the left can always be used.
    apply False.elim h23
  -- Implications on the right can always be decomposed.
  intro h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225457922892842182970442937042 : (((p4 ∨ p1) ∧ p3) ∨ (((p5 ∨ p5) ∨ (p3 → False)) ∨ (False → (p1 → (((p1 → (p4 ∨ (p5 → p4))) ∧ (p4 → p5)) ∨ (p5 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310291496103253598945070085057 : (p2 ∨ (((((((False ∨ p2) → p5) → p2) → True) → p2) ∨ p5) ∨ (((((p3 ∧ p5) → False) ∨ True) ∨ p5) → ((False ∧ (False ∨ p3)) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672336042849670855331645430993 : ((((((p4 ∧ (p5 ∨ ((p4 ∧ ((False ∨ (p3 ∧ ((p3 ∨ p4) ∨ p3))) ∧ p1)) → True))) → (p5 ∨ False)) → True) → ((p1 ∧ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14719517918838385331053017951 : (((((p5 ∨ (((p3 → p4) ∧ (((p4 ∨ p3) ∨ True) ∧ ((p4 → p3) ∧ p4))) → (False ∨ p5))) → False) → (False ∨ p4)) ∨ (False ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735070281416848166793018523354 : ((((p3 ∨ False) ∧ (p5 ∨ (((p5 → (((p2 ∧ (False ∧ p5)) ∨ (((p2 ∨ (True ∧ p2)) → (p4 → p4)) ∧ False)) ∨ False)) ∨ p4) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300953868825826479179588972457 : (False ∨ (((((p5 ∨ ((p4 ∨ p3) ∨ p1)) ∧ p2) ∧ (True → False)) ∧ True) ∨ (((True → True) ∧ (True → p5)) → ((False → (p4 ∧ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190291555574561101231194501722 : (((((p5 ∧ (p2 ∨ (p4 ∧ True))) → p3) → p5) ∨ p2) ∨ ((p1 → ((p3 ∨ True) → p1)) ∧ ((False ∨ False) ∨ (((p4 ∨ False) ∨ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346390798011524424429306630035 : (p3 → ((p1 → ((p2 ∨ ((((p4 ∨ (((True ∨ False) → True) → p4)) ∧ p5) ∧ p2) ∨ p4)) → (((p3 ∧ p5) ∧ p2) ∨ False))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764618576815413438459797866340 : (((p4 ∧ (((p1 → (p5 → (((p4 ∨ (True ∧ p5)) ∨ p4) → False))) → (((p3 → (p3 → p5)) ∧ (p4 ∧ p1)) ∧ (p3 ∧ True))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53023951870710400340989231164 : ((((((False → True) ∨ p2) ∧ True) → ((False → (p2 → p4)) → p3)) ∧ (((((p2 → p2) ∧ p3) ∧ (p3 ∧ p1)) ∨ (p2 → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213444686001102435631140397510 : (((p5 ∨ (p3 ∧ p1)) ∧ p5) ∨ (p1 → ((((p3 ∨ p5) ∨ (((p4 → (p1 ∨ p1)) ∧ (p3 → (p5 ∧ p4))) ∨ p3)) ∨ (False → p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726383926559275271007545342056 : (((((p5 ∨ p5) ∨ p5) ∨ (((((p3 → p1) ∧ p3) ∧ ((p3 ∧ p2) ∨ (p5 → p3))) → ((((p4 ∨ False) ∨ True) → p4) → False)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47498068129046630721741519730 : (((p1 ∨ ((p4 ∧ (((True → True) ∨ p2) ∧ (((((p1 ∨ p1) ∨ p3) ∨ (p2 ∨ True)) ∧ p2) ∧ p3))) → (False ∨ p4))) ∨ (True → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168365252308459707243250715900 : (((p1 ∨ p3) ∨ ((((((True ∧ (p5 ∨ p1)) ∨ p3) ∧ p5) ∧ True) → (p2 → True)) ∨ p3)) → (((p3 ∨ p2) ∨ (True → p4)) ∨ (p4 → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300691105754089271516255945142 : (False ∨ ((p4 ∧ (p5 ∨ (p1 ∨ ((p3 ∧ ((p5 → False) ∨ (p3 ∨ ((p4 ∧ p5) → True)))) ∨ False)))) ∨ (((p2 ∨ (p4 ∨ True)) → False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148033258828495873198323393977 : ((((p3 ∧ (False → False)) → ((((p1 ∧ (p1 ∨ (True ∨ (True → True)))) ∨ p2) → False) ∨ False)) ∨ (True → p3)) ∨ ((p1 ∧ p4) → (False ∨ p1))) := by
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
theorem thm_5_vars_651422873764352143427133168491 : ((((((p1 → p4) ∨ True) → ((p4 → (False ∨ (p1 ∨ p1))) → (((p3 ∧ p3) → ((p4 → (False → False)) → p1)) ∨ p1))) ∧ (p2 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213438047554096859788747427793 : (((p4 ∨ (p4 ∨ p4)) ∧ p2) ∨ (((p4 ∨ (((p2 ∨ p3) ∨ (p2 → (p1 → p3))) ∨ False)) ∨ (p4 ∨ (p2 ∨ ((p3 → True) → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632228401182241230855523350728 : (((((False ∧ (((p4 ∧ p5) → (p2 ∨ ((False ∧ p1) → (p5 ∧ (False → (p5 → p5)))))) ∨ ((p5 → p2) ∨ (p5 → True)))) → True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697606103186607181513473909137 : ((((p2 ∨ ((False → ((p2 → (p2 ∨ (False ∧ p3))) → False)) ∨ p3)) ∧ (((p3 → (((True → True) ∧ (p1 ∧ True)) ∧ p1)) → p5) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354734359006823402259757056404 : (p5 → ((((((p4 ∨ False) ∨ True) ∨ p3) ∧ (p4 ∧ (((p2 → (False ∧ (False ∨ p5))) ∧ p5) ∧ p5))) ∨ ((p5 ∨ (p4 ∨ p2)) ∧ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149664153824878283442231151148 : ((p4 ∧ (p1 ∨ (((False ∨ ((((False ∨ True) → ((p4 → False) ∨ p4)) → p1) ∨ p4)) ∧ (p2 ∧ p2)) ∧ p5))) ∨ (p4 → (p5 → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136258173236860211259988304047 : ((((((p5 ∧ p2) ∨ p3) ∨ False) ∧ p5) → (((False ∨ p4) → ((False ∨ p3) → ((p1 ∨ (p5 → False)) ∨ p2))) ∨ p3)) ∨ ((False → p4) ∧ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351808098841775932727837531945 : (p4 → (((((p4 → True) ∨ p3) → ((p2 ∧ p1) → (False ∨ p1))) ∧ p5) ∨ ((((p2 ∧ (p1 ∧ (p2 ∨ p1))) ∧ (True → p2)) ∧ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249554286881238343757978539671 : ((p5 ∨ p2) ∨ ((p1 → ((((p1 ∨ p1) ∧ p5) ∧ True) ∨ (p5 ∧ ((p1 ∧ p1) ∨ p5)))) ∨ (((((True ∨ True) ∨ False) ∨ p4) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726478238970793787674349018390 : (((((p2 → p3) ∨ p2) ∨ (p1 ∨ ((p3 ∨ (((((p3 → (p2 ∨ p5)) → p2) → True) ∨ ((True ∧ True) ∨ False)) → (p4 → p5))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161003205870967818039570988253 : ((((p2 ∨ p3) → True) ∨ (p5 ∧ ((p4 ∨ (p3 ∨ (((p3 → p2) ∨ False) ∧ (p2 ∨ p1)))) ∧ p3))) → (((p5 → p3) ∨ p4) ∨ (p2 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114991167194588641885692239443 : (((((p1 ∨ p1) → ((p3 → (p1 ∧ p1)) → p5)) ∧ (p1 ∧ p5)) ∧ (p1 ∨ (((((p1 → p5) ∨ p3) → p1) ∧ p1) → p4))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318909789319711897467437309781 : (p4 ∨ ((p5 → (False ∧ ((((p1 → (p2 ∧ (p3 ∨ ((False → p5) ∧ (False → p4))))) → (False ∧ p1)) → p3) ∧ p1))) ∨ (False ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323473187009854274250107508465 : (p5 ∨ ((((((((((True → p3) ∨ p1) ∨ p4) ∨ (p2 → (False ∨ (p3 → p3)))) → False) ∨ p3) ∧ p1) ∧ p4) ∨ p2) ∨ (True ∨ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198557535208398274966483519575 : ((p1 ∨ (((p4 ∨ p1) ∧ (p5 ∨ p5)) ∨ p3)) ∨ (((True ∧ False) → p2) ∨ ((p2 ∧ ((p5 ∨ (p2 → False)) → (True ∧ (p4 ∧ p5)))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68886767874048715513342161105 : ((p4 → (p3 ∧ ((((p1 ∧ (p5 → (((p2 ∨ True) ∧ False) ∨ ((p5 → p3) ∧ p3)))) ∨ False) ∧ (((True ∧ True) ∧ True) ∨ p4)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599574482985527804618686511619 : (((((p4 ∨ p3) ∨ (((p3 → p4) → p4) ∨ (((p1 ∨ (p1 ∨ (p1 ∧ ((p3 → p2) → (p5 → p1))))) ∨ (True → p1)) ∧ p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724220056349517720372639662914 : ((((p3 ∧ (p4 ∨ p5)) ∧ (((p5 → ((p4 ∧ (p4 ∨ (p4 → ((p2 ∧ ((True → p3) ∨ (p4 ∨ p3))) ∧ p1)))) ∨ p3)) ∧ p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37905391206751595052866272863 : (((((((True ∧ (p1 ∧ ((p2 ∧ False) ∨ True))) ∧ p5) ∧ ((p4 ∨ True) ∧ p2)) ∨ (True → ((False → False) ∧ p2))) ∧ (p4 ∧ True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354980845135162049401504638444 : (p5 → ((p5 → ((p2 ∨ p3) ∧ (False ∨ (p3 ∨ (((p5 ∧ ((False → (True ∧ p2)) ∨ (((p2 ∧ p1) ∧ p2) ∨ p5))) → p3) → p1))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147269969615107038263012944912 : ((((((((p5 → (p3 ∨ p5)) → False) ∨ (p4 → ((False → p1) ∨ False))) ∨ False) → (False ∨ p2)) ∨ True) ∨ p4) ∨ (((True ∨ p1) ∧ p4) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152016736051105442744693912811 : (((((((p4 ∧ p3) ∨ (False → p2)) → True) → p5) ∧ p4) ∧ (((p3 ∨ True) → ((p4 ∨ True) ∧ p2)) ∧ True)) → ((p1 → p3) ∨ (p5 ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (((p4 ∧ p3) ∨ (False → p2)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h8
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263567372262342052482265859233 : (True ∧ (((p4 ∧ ((((p5 ∧ (p2 ∧ (p5 ∨ True))) ∧ p1) ∧ False) → p5)) → (((p4 → p1) → False) ∨ p4)) ∨ (True ∧ ((p1 → p4) ∧ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263588835055256092790423633215 : (True ∧ ((True → (((p1 ∧ (True ∧ ((((True → p5) ∨ p1) → False) → p1))) ∨ p2) ∨ ((p2 ∨ True) ∧ p1))) ∨ (p3 → (True ∨ (p2 ∧ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116065202541423552282995113914 : ((((False ∨ p1) ∧ p2) ∧ (p4 ∨ (p2 ∨ (p4 ∧ (p5 ∧ ((((True ∧ (p5 ∧ (True ∨ p2))) ∧ p4) ∧ p3) ∧ (True → True))))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323236438292546906150074745583 : (p5 ∨ (((p5 ∨ (p2 ∧ p5)) ∧ ((True → (p4 ∨ (p1 ∨ ((p2 ∨ p4) → ((True ∧ p3) → p3))))) ∨ (p4 ∧ (p2 ∨ True)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700974997129276523319640615263 : (((((p5 ∧ ((p1 ∨ (False ∨ (True ∧ p2))) ∨ p3)) ∨ p4) ∧ (((((p3 ∨ (p5 → p2)) → p2) ∨ (True ∨ p5)) ∨ (p1 → p1)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_863191797480023092352293383270 : (((((((p1 ∨ p3) → (p2 ∨ ((p3 ∧ (True ∧ p1)) ∨ False))) ∨ (p5 → True)) ∨ (((((p2 ∧ p3) → p2) ∨ p5) ∨ False) ∨ p4)) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ p3) → (p2 ∨ ((p3 ∧ (True ∧ p1)) ∨ False))) ∨ (p5 → True)) ∨ (((((p2 ∧ p3) → p2) ∨ p5) ∨ False) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134022632171694698375832040109 : ((((((False ∧ ((False → p2) → (p1 ∧ (p1 ∨ p5)))) ∨ ((p4 ∧ p1) ∧ ((p1 → p2) ∧ p4))) ∨ False) ∨ False) ∨ p5) ∨ (p5 → (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179535005611944329635448673039 : ((p1 → ((p4 → ((p5 → ((p2 ∨ p2) ∨ p1)) ∧ (p5 → False))) → p4)) ∨ (p3 → (True ∨ (False ∨ ((p3 ∨ p1) ∨ ((False → p5) ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655739068115085546238002638324 : (((((((True ∧ (((p1 ∧ p4) ∨ (p1 ∧ (p2 ∧ p2))) ∧ p5)) ∨ ((True → p2) → p4)) ∨ True) ∨ (p5 ∧ (False → p5))) ∨ (p2 ∧ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



