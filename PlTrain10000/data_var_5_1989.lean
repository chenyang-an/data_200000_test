variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316573841642596024884696535644 : (p3 ∨ (p3 ∨ ((p3 ∨ ((False ∧ (p5 ∨ (p3 → p1))) ∧ p3)) → (((p1 ∧ ((p5 → p4) ∨ p4)) ∧ (p4 → False)) → ((p1 ∨ p2) ∨ p1))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357402066860036282761318156931 : (p5 → ((True ∨ True) → (((p4 ∧ p5) ∨ p3) ∨ ((((True ∨ (p1 ∧ p1)) ∧ (True ∨ (p2 ∨ ((True → False) → (p2 ∨ p2))))) → p2) → p2)))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ (p1 ∧ p1)) ∧ (True ∨ (p2 ∨ ((True → False) → (p2 ∨ p2))))) := by
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
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((True ∨ (p1 ∧ p1)) ∧ (True ∨ (p2 ∨ ((True → False) → (p2 ∨ p2))))) := by
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
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196238570953511633375117531236 : ((p2 ∨ (((p2 ∧ (p2 ∧ p2)) ∧ p1) ∨ True)) ∧ ((p2 → ((p4 → False) ∨ ((((p5 ∨ True) ∧ True) ∨ (p5 ∨ (p3 ∨ p2))) ∨ p2))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_356264398158091862952890024009 : (p5 → ((((False ∨ p5) → False) ∨ ((True ∧ p2) ∧ (((p2 → p3) ∧ p1) → (p3 ∧ p2)))) ∨ ((p3 ∨ (True ∨ ((False ∨ p1) ∨ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_133981168620220120319333123679 : (((((((((p5 ∨ True) → ((True ∧ (p2 ∨ p2)) ∨ (p1 ∨ (p1 → p5)))) ∧ p1) ∧ True) ∧ True) → False) ∧ p3) ∨ True) ∨ (p1 → (p1 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232702188057184168432885653064 : ((p1 ∧ (p1 ∨ p5)) → ((p2 ∨ p3) ∨ (p2 → ((True ∨ ((p3 ∨ p3) ∧ p5)) → ((p4 ∨ (((True → (p4 ∧ False)) → p3) ∧ True)) ∨ p4))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h17
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h23
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h31
        -- One of the premise coincides with the conclusion.
        exact h30
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h33
        -- One of the premise coincides with the conclusion.
        exact h32
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68926840503543004498778633456 : ((p4 → (p3 ∨ ((p2 ∧ ((p2 ∨ True) ∧ (p3 ∨ ((((p4 → p3) → ((((True ∧ False) ∨ p4) ∧ p4) ∧ p3)) → p4) → False)))) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_613742499490372280053134793285 : (((((True ∧ ((p2 → False) → ((True → (p4 ∨ (p4 → False))) ∨ ((p3 ∨ (p5 ∨ p5)) → (p3 ∧ p3))))) ∧ (p4 ∧ (p5 ∧ p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_234111469040901585677859391353 : ((True → (False ∨ p3)) → (((False → ((True ∧ (True ∨ p1)) ∧ (True ∧ ((True ∧ p2) ∧ (p2 ∧ p3))))) ∧ (((False ∨ p4) ∨ p3) ∨ p4)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137723902419644502075953574082 : ((p1 ∨ (True ∧ ((((p4 → ((p4 → True) → False)) ∧ p4) ∨ p5) ∨ ((p5 ∨ False) → ((True → (p1 ∧ p3)) → p3))))) ∨ (p4 → (True → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776592943885514976661321433742 : (((p1 ∨ ((p2 ∧ (p2 ∧ (((p5 ∨ (p5 → p1)) → (p4 ∨ False)) → (((((p2 ∨ (p2 ∧ True)) ∧ p4) ∨ p5) ∨ p4) ∧ True)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172196410331534943864141579472 : ((((p1 ∨ (((p5 ∧ p3) ∧ True) → (p1 → p5))) ∨ True) → (p5 → (p3 ∧ p3))) ∨ (((p4 ∧ False) → ((p4 → p3) ∨ (p4 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154227708369445241131180091896 : (((((((p5 ∨ p5) ∨ p5) ∧ (p1 ∧ p3)) ∧ p2) ∧ ((((p3 → p2) → p4) ∧ p3) → True)) ∨ True) ∧ (((p4 ∨ (p3 ∨ False)) ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181248373258909774517015291686 : ((p3 ∧ (p4 ∨ (((p3 ∧ (p5 → p3)) ∨ p3) ∧ (p3 ∧ (p4 ∧ p4))))) → (((True ∨ (((p3 → p5) ∧ p4) → (p1 ∧ p2))) → p5) ∨ p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126411366288900676237586794098 : ((p1 ∧ (p4 ∨ ((((((((False ∧ p3) ∧ p4) → p1) ∨ p3) ∧ p2) ∨ False) ∨ p1) ∧ (((p2 ∧ p1) ∨ (True ∧ p4)) ∧ p2)))) → (False ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
          -- Conjunctions on the left can always be decomposed.
          let h13 := h7.left
          let h14 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h7.left
          let h23 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h7.left
      let h33 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147043984333606968213143801830 : (((((p4 → p2) → ((p5 → p4) ∨ (((False → False) → True) ∧ p4))) ∨ (True → ((p4 → p1) → True))) ∧ p3) ∨ ((p3 ∧ (False → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54954746277922436586083665243 : (((((p5 ∨ False) ∨ p2) ∨ (False → p2)) ∧ (p5 ∧ (p2 ∧ (p5 → (((p3 → False) ∨ p2) → ((False ∨ (p4 ∨ (p5 → p2))) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259640885914356987393348207906 : ((p1 → False) → ((((p4 ∧ (p1 ∨ p4)) → p1) ∧ p4) → (p3 ∨ ((((p2 ∧ (p1 ∨ p4)) ∨ ((p2 ∨ (p3 ∧ False)) → p1)) → p2) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∧ (p1 ∨ p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356656620840988849555485998430 : (p5 → ((((True → (p5 → p3)) ∨ p4) → (p3 ∧ True)) → ((False ∨ (((False → p3) → (p5 ∧ (p5 ∨ p3))) → p1)) ∨ ((False → p5) ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299297251573094287615280034962 : (False ∨ ((((p2 ∨ ((p5 ∨ (p3 ∨ True)) ∧ (p3 ∧ p1))) ∨ True) ∨ ((p3 → True) → (((p3 ∨ (False ∨ p2)) ∨ p5) → (p2 → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40603011167453675161931683421 : ((((((p4 ∨ (((((p1 ∨ p4) → ((p1 ∨ p3) ∨ p4)) ∨ ((p3 → p3) ∨ True)) → (p3 ∨ p5)) ∨ p5)) ∨ p5) ∨ p2) → False) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783646379478491426354083301885 : (((p3 ∨ ((p3 ∧ (p2 ∧ (p3 ∧ ((True → p1) ∧ p2)))) ∨ (((p2 ∧ False) → ((p1 ∨ p1) → p1)) → (p2 ∨ ((p5 ∧ p2) → p5))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119286925250560817218485526296 : ((p3 → (((p1 ∧ p1) ∧ ((p2 ∨ ((p5 ∧ p2) ∧ p4)) ∨ (p4 ∨ ((((True ∨ p1) → (p2 → p3)) → p3) ∧ p5)))) ∨ p5)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111920478795864542805182622924 : ((((((p4 ∧ p2) ∨ ((True ∨ ((True ∧ p2) → p5)) ∨ p1)) ∨ False) → ((p3 → (((False → True) → True) ∧ p2)) → p5)) ∨ False) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319322006837609759590331678128 : (p4 ∨ ((p4 ∨ (((p1 ∨ p3) → True) → (False ∧ (p1 → (p3 → (False ∨ (p5 → p4))))))) → ((p3 ∨ ((p1 ∨ False) → (p5 ∧ p5))) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659055854598421287562302028029 : ((((p2 → ((((((p4 → p4) → p4) ∨ p4) ∧ (((p5 ∧ ((True ∧ False) ∧ p4)) → (p2 ∧ p1)) ∨ p3)) → p1) → p5)) ∨ (True ∧ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_62723967598186529829140488339 : ((p4 ∧ (((((((p2 → False) → ((p4 ∧ (True ∧ p1)) ∧ (p5 ∧ (True ∧ p3)))) ∨ p5) ∧ p3) → (p3 → p1)) ∧ p5) ∧ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327804996003447290857493350163 : (True → (((((p3 ∧ (True ∧ p1)) ∨ p2) ∨ ((p5 ∧ ((p3 ∨ (False ∨ ((False → p2) → (p2 → p5)))) ∧ True)) ∨ p5)) ∨ True) ∨ (p5 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149952427582545494115093141887 : ((p4 ∨ (((p5 ∧ ((((True → p3) → p4) ∧ ((True → (p1 → (p5 ∨ p4))) ∨ p2)) → True)) ∧ p4) ∧ False)) ∨ ((False ∧ p4) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40696497906871320190428934589 : (((((((((False ∧ p3) → p1) → p1) ∨ (p4 ∧ (False → False))) ∨ (True → False)) ∨ ((p2 → False) ∧ (p1 ∨ (p4 ∨ p4)))) → p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117676467874804254928138779662 : ((p3 ∧ (((p5 ∧ ((False ∨ p3) → p5)) ∨ (p1 ∧ True)) ∧ ((p4 ∧ p2) ∨ ((p1 → (p1 → (p3 ∨ p5))) ∨ (p1 ∧ p3))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155224256749061730340598665093 : (((p3 ∧ ((((p3 ∨ p3) ∨ p4) ∧ True) ∨ p5)) ∨ ((((p3 → (p3 ∨ p4)) ∨ p5) ∨ p4) ∨ p5)) ∧ (((p5 ∨ True) → p1) ∨ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200936765748746970473694186772 : ((p1 ∨ (p2 ∨ (p3 ∨ (False ∨ (False ∧ True))))) → (((p3 → p2) → ((p3 ∨ True) → (((((p2 ∧ p5) ∨ p5) → p3) → p3) → False))) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148828267865991321013587569193 : (((p3 → (p5 ∨ ((p4 ∨ p3) → True))) → (((True ∨ ((p4 → (p4 ∨ (p5 ∨ False))) ∨ p4)) → p4) ∧ p2)) ∨ (False → (False ∧ (p4 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85339677435770824220643994089 : ((((False ∨ (((p5 ∧ (True ∨ p4)) → (False → False)) ∨ p2)) → False) ∧ (True ∨ (((p2 ∨ True) → ((p3 ∧ p2) ∨ (p4 → p5))) → p2))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ (((p5 ∧ (True ∨ p4)) → (False → False)) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ (((p5 ∧ (True ∨ p4)) → (False → False)) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h10
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310068671372968265019662855627 : (p2 ∨ (((False ∨ p3) ∨ (p3 ∧ (((p2 ∨ p3) → (p5 ∧ True)) ∨ (p5 → (p2 ∧ p4))))) → ((p3 → ((True → True) ∧ p5)) ∨ (p1 ∨ p3)))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726853825227636266018186994512 : (((((p3 ∨ False) → p4) ∨ (((p5 ∧ (((True ∧ (p1 → p2)) → p1) → p1)) ∨ p3) ∨ ((((True ∧ p1) ∧ False) ∨ (p1 ∨ True)) ∨ p3))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138063626819704580993061672310 : ((True → (p2 ∨ ((p5 ∨ p5) → ((False ∨ p1) ∨ (((p3 → (p4 ∧ (p2 ∧ True))) → (p4 ∧ (p1 ∨ p3))) → True))))) ∨ (p2 ∧ (p1 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49560615383724097518945608375 : ((((p5 ∨ (((((p4 ∧ (True ∨ p4)) ∧ p2) → p1) → (False ∧ p4)) ∧ (True ∧ True))) ∨ ((p4 ∧ False) ∧ p3)) → (p2 ∨ (True ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264553182587861424075336133390 : (True ∧ (((p2 → p4) ∨ p1) ∨ (((p5 ∧ (p4 ∧ p2)) ∨ ((p4 ∧ ((p3 → (False ∧ p1)) → True)) ∨ (p4 ∧ ((p2 ∨ True) ∧ True)))) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41731277013098453461623429592 : (((((p1 → p1) ∨ (p1 ∨ p1)) ∧ (True ∧ ((True ∨ (p2 → (p2 ∨ ((((p4 → p1) → (p2 ∧ p2)) ∨ p4) ∨ p2)))) → False))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728660102964490305695635943898 : ((((p5 → (p2 ∧ p2)) ∨ ((False ∧ (p1 ∨ ((False ∧ (p2 ∧ p5)) ∧ ((p2 ∧ (p5 → (False ∧ ((p4 ∧ p2) ∧ p4)))) → True)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253769792555563308591656708194 : ((p1 ∧ p1) → (p4 ∨ ((((p3 ∨ p5) ∨ ((p2 ∧ (p4 ∧ (False → (p5 ∨ (False ∧ p5))))) → (False ∧ p2))) ∧ (p5 ∨ False)) ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733056112030321971339298658528 : ((((p2 ∧ p5) ∧ (True ∧ ((((((p1 ∨ p2) ∧ True) → (p4 ∨ (p1 ∨ ((False → p4) ∧ False)))) ∧ (p4 → True)) → p5) ∨ (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38467499275034184945365596279 : ((((p2 ∨ ((p3 → p2) ∨ ((p4 ∨ ((p4 ∨ p1) ∧ (p5 ∧ True))) ∨ True))) → (False ∨ (p4 → (((p2 → p4) ∨ True) ∨ p3)))) ∧ True) ∨ p3) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
            -- Conjunctions on the left can always be decomposed.
            let h15 := h13.left
            let h16 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h13.left
            let h20 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134310391695340464347258267955 : (((True ∧ (p3 ∨ (p2 ∨ (p4 ∧ (((False ∧ (p5 → p4)) ∧ (p1 ∧ (((p4 ∧ p5) ∨ p4) ∨ p5))) ∨ p3))))) ∨ True) ∨ ((p3 → p4) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141399159699821910737067057433 : ((((p2 ∧ p4) → (p2 → p3)) → (((p5 ∧ ((p4 ∨ p2) → p4)) ∧ (False ∧ (p2 ∧ (False ∨ (p4 → p2))))) ∧ p5)) → (p3 → (False ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p4) → (p2 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : ((p2 ∧ p4) → (p2 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h12
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56754930558733602058663012059 : ((((p3 → True) ∨ False) ∧ (p1 → ((p4 ∨ p1) → ((p3 ∨ (p5 ∨ p4)) → (True → ((p5 → True) → (p5 → ((p5 ∧ p2) ∧ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198377615714145796017089828366 : ((p3 ∧ (((False ∧ p1) ∧ p2) ∧ (p2 ∨ p1))) ∨ (((p2 → p2) ∨ False) ∨ ((p5 ∧ (False ∧ (p3 → ((True ∨ (True → False)) ∨ p3)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687856069009483707265769645116 : (((((((p2 ∧ p3) ∧ (p2 ∨ (False → (p2 ∨ True)))) ∧ p2) ∨ (p2 ∧ (p1 ∧ True))) ∧ (True ∨ ((p3 → (p3 ∧ (p2 ∨ p5))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186289953360113288712948532889 : (((((True ∧ ((True → p1) ∧ p4)) → (p4 → False)) → True) → p4) → (((((True → p5) ∧ ((p1 → p1) ∧ p4)) → (p5 ∧ False)) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ ((True → p1) ∧ p4)) → (p4 → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233256031243824274218654128098 : ((True ∨ (p2 ∧ p2)) → (((p5 → (((p2 → p1) → (p1 ∧ p4)) ∨ (True → p2))) ∧ ((p3 → True) ∨ (((p5 ∧ p5) → p2) → p2))) ∨ True)) := by
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
theorem thm_5_vars_165920856264946908654480861021 : (((p1 ∧ p1) ∧ (p5 ∨ ((p1 → ((True → ((p3 → p5) → p2)) ∨ False)) → (p1 ∨ p4)))) ∨ (((p3 → (p5 ∨ p4)) ∨ (p3 ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_348767369548229689638457601354 : (p3 → (False ∨ (p3 ∧ (((p5 ∧ ((p2 → False) → ((True ∨ p2) ∨ ((p4 ∧ True) → p5)))) → (((False ∨ p1) ∨ p4) → False)) ∨ (p5 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781464868428806230868921323980 : (((p2 ∨ (p4 ∧ (p3 → (((((p5 ∨ p3) → ((True ∨ p1) ∨ (p2 ∧ p1))) ∨ (((p5 ∨ p5) → p2) → True)) → p4) ∨ (p1 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304992923521099018578499561823 : (p1 ∨ (((True → (p4 ∧ ((p1 → p2) → ((p1 → ((False → p4) → (p2 → True))) ∨ (p1 → (p4 ∧ p4)))))) → p2) ∨ ((p3 → p3) ∨ p2))) := by
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
theorem thm_5_vars_314300169052008105459398425126 : (p3 ∨ ((((((p2 → (p4 ∧ (((((p1 ∨ p5) ∨ p1) → p1) → p2) ∧ False))) ∧ (p2 → p1)) → p5) ∨ p3) → False) → (p3 → (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p2 → (p4 ∧ (((((p1 ∨ p5) ∨ p1) → p1) → p2) ∧ False))) ∧ (p2 → p1)) → p5) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113614137800643049463228398385 : (((p5 ∨ ((p1 ∧ ((True ∧ p2) ∨ (p2 ∨ (p2 → (p3 ∨ (((p2 ∧ (True ∨ p5)) ∧ False) ∨ p2)))))) ∨ True)) ∨ (False → True)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115083421671861862194105881474 : (((p5 ∧ (p4 ∨ (((p5 ∨ (p5 → (p1 → p4))) ∧ False) ∨ True))) ∨ ((((p4 → (p5 ∧ True)) → p2) ∧ (p3 ∧ True)) ∧ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138277630606822118254948035888 : ((p3 → (((((p5 ∧ p3) → ((((False ∧ p2) → p3) ∧ (True ∧ p2)) → False)) ∧ ((p2 ∨ p2) ∨ p2)) ∧ True) ∨ p3)) ∨ (p1 → (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313975483372521547977540751642 : (p3 ∨ ((((((False ∨ p4) ∨ ((False ∨ p5) → (p1 ∧ p3))) → False) → False) → (p2 ∧ (((False ∨ (p5 → p2)) → p5) ∨ p3))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769869637654628462385602322126 : (((p5 ∧ (p5 ∨ (p3 ∧ (p3 ∧ ((p3 → (p2 → (((p1 → p2) ∧ p1) ∨ (p5 → ((False ∨ False) ∨ (p2 ∧ (p5 → True))))))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47456532980237038369187449142 : (((p4 ∧ ((p1 → (p2 → (p4 ∨ p3))) → (p2 ∧ ((p3 → (((p3 → p4) ∧ (p3 ∨ p4)) ∧ False)) ∨ (p3 ∧ False))))) ∨ (False → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46876933360433845107376636202 : ((((((((((p5 ∧ (p4 ∧ (p3 ∧ (False ∨ True)))) → ((False ∨ p4) ∨ p2)) ∧ True) ∧ p5) ∧ p2) ∧ p3) ∧ p1) ∨ p5) ∨ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336328142065679058263029994592 : (p1 → ((((p1 ∧ False) ∨ p5) ∨ ((((p3 ∨ p4) → (False ∧ (((p4 ∨ p1) ∧ ((p3 ∨ True) ∧ p2)) ∨ p1))) ∨ (p3 ∨ p2)) ∧ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57435850254234642384116298798 : (((p3 ∨ (p1 → p3)) ∨ (True → (((((p4 → p3) ∨ (p3 → True)) ∧ (p4 ∧ ((p4 → False) ∧ ((False → p5) ∨ False)))) ∨ p3) → p3))) ∨ p1) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h21 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h22 := h18 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
  case inr h24 =>
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205519840502388591910508236487 : (((True ∨ False) ∧ ((p5 ∧ p1) ∨ p4)) ∨ ((((False → False) ∧ p2) → (p1 ∨ (((p5 ∨ p2) ∧ p2) → ((p1 ∨ p2) ∨ (p4 → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47209083930710167928171643965 : ((((p5 ∨ ((((False ∨ p3) ∧ p1) ∨ (p5 → True)) ∨ True)) ∧ ((p4 ∨ ((p2 ∧ p1) → (p2 ∨ p5))) → (False ∧ p3))) ∨ (True ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135723966757521682128535119894 : ((((((p3 → False) → ((p3 ∧ p2) ∨ (False ∧ p2))) → (False ∨ p3)) ∧ True) ∨ ((p2 ∨ True) ∨ (p1 → (False ∧ p4)))) ∨ ((True ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115475020743033640316771086583 : (((True → ((((False ∨ p5) ∨ p2) → p5) → p3)) ∨ (((p1 → (p2 ∧ p2)) ∨ p1) ∨ ((p3 ∨ p2) ∨ ((False ∨ p1) ∨ True)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_470493955429411016975164601294 : (((((((p1 ∨ False) ∧ p4) ∧ (p5 ∧ p5)) ∨ ((False ∨ p3) → p3)) ∧ (((p4 → (p3 → p4)) ∧ (False ∧ True)) → ((p3 → p1) → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262480233362245142106240895993 : (True ∧ ((p5 ∨ (((False → p2) ∨ p5) ∧ ((((((False → ((p2 ∧ p5) ∨ p1)) ∧ p4) → (True → (p3 ∨ p3))) → p4) ∨ p1) ∨ p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740471059268746959123980802030 : ((((p1 ∨ p5) ∨ ((((((p2 → ((p3 ∨ p1) → (True ∨ p4))) ∧ (False ∧ False)) ∧ ((False → p5) ∧ (p5 → p3))) ∨ p5) ∨ p1) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_227305303423305396355430806820 : (((p2 → p1) → False) ∨ (((p5 ∧ ((p2 ∧ p5) ∧ ((p1 ∨ ((True → p4) → p2)) → (True ∨ ((p1 ∧ p5) → p2))))) ∨ True) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48539979620804101828889060178 : ((((p5 → ((p3 ∨ True) ∧ (p4 ∧ ((p5 ∨ (p1 ∨ (True ∧ True))) ∧ ((p5 → (p2 ∨ False)) ∧ False))))) ∨ p3) ∧ ((True ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316562800007953787862268404829 : (p3 ∨ (p3 ∨ (((((((p5 ∨ p1) → (True ∨ p4)) ∨ (p3 → ((p2 ∧ False) ∨ p2))) ∨ False) → False) → (p3 ∨ p1)) ∧ (p4 ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ p1) → (True ∨ p4)) ∨ (p3 → ((p2 ∧ False) ∨ p2))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752963574681746123147581607849 : (((False ∧ ((((p4 → p3) ∧ ((((p4 ∨ False) ∨ p4) → (((True ∨ True) ∨ p4) → p2)) ∨ p4)) ∧ ((p5 ∧ (p2 → p4)) ∧ p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131480552306217522214148110306 : ((((True ∨ False) → (p4 ∧ False)) → (p3 ∧ (False ∨ (((False ∨ (((p5 ∧ p2) ∨ p4) ∧ p4)) ∨ p4) ∨ (p3 ∧ True))))) ∧ ((False → True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115418076553683882120647967806 : ((((((p5 ∨ True) ∨ p3) ∧ (False ∧ False)) ∧ p3) ∨ ((((p5 ∧ (True → (True ∧ (True → p2)))) → p2) ∧ (p5 → True)) ∨ p5)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351389700688396170456694082497 : (p4 → (((((((p4 → False) ∨ ((p5 → (p1 ∧ p1)) ∨ p4)) → p5) → (True ∨ (p4 ∨ p2))) → p1) ∨ p4) ∨ (p3 → ((p2 → p4) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255207233754098314760902899878 : ((p4 ∧ p4) → ((((False ∧ False) ∨ (p2 → p1)) → p3) ∨ (((p4 ∨ ((p1 → (p2 ∨ p1)) ∧ True)) ∧ p3) → ((False ∨ (p1 ∨ p1)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148893171981022835424606481104 : (((True ∧ ((p5 ∧ p5) ∧ True)) ∨ ((p3 → ((p2 ∨ (p4 → p5)) ∧ False)) ∨ ((p4 ∨ False) → (p5 ∧ p4)))) ∨ (p2 → (p1 → (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616365504299485394005293433860 : (((((p4 ∨ (p1 ∧ ((True ∧ True) ∧ (False ∧ ((True ∧ p3) ∧ p1))))) ∨ ((False → (p1 ∨ ((p1 ∨ p4) ∨ p5))) ∨ (p2 ∨ True))) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158811857591705129884806713297 : ((p5 ∧ (True → (((p2 ∨ p3) → ((p3 ∧ p3) ∧ (True → (((p4 ∨ True) ∧ p1) ∨ p4)))) ∨ p3))) ∨ ((p2 ∨ False) ∨ ((False ∧ p5) → p2))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158124304819484943698911586180 : (((p3 → ((p3 ∨ True) ∨ p2)) ∧ ((((p5 ∧ p1) ∧ p2) ∧ ((p2 ∨ p1) → p5)) ∨ (p3 ∨ p2))) ∨ (((True ∧ (False ∧ p5)) → p3) ∨ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178466203719477884967793001056 : (((p3 → ((((True ∧ False) ∨ p3) ∧ p4) ∨ p2)) ∧ ((p4 → p1) → p5)) ∨ (((False → True) ∨ (((False → True) → (p4 → p4)) ∨ p5)) ∧ True)) := by
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
theorem thm_5_vars_803368241085686604812331922809 : (((p3 → ((False ∧ (p5 → (True ∨ ((((p2 ∧ ((p2 ∧ p5) ∧ p5)) ∧ False) ∨ (((False ∧ p1) ∨ p3) ∨ (p1 → p2))) ∨ p5)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632697847353401599568178324154 : (((((p4 → ((p1 → True) ∨ ((((p4 ∨ ((True ∨ p1) ∧ ((p1 ∨ (p1 ∨ p4)) ∨ (p5 → p5)))) ∨ p5) ∧ p5) ∧ p2))) → p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259604528086453325128401460829 : ((p1 → True) → (p3 → ((((p5 ∨ (True ∧ p3)) ∨ False) → ((((True → p3) ∨ False) ∧ p5) ∧ ((p3 → p2) ∨ ((p5 ∨ p1) ∧ p5)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357453924157109053179492802992 : (p5 → ((p1 → p1) → ((p5 ∧ (p4 → (p2 ∧ (((p2 ∧ (((p3 → p1) ∨ (p2 → False)) ∧ (p1 ∨ (p2 → p2)))) → p3) ∧ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193346862266025074939044893260 : ((((p2 ∧ p3) → p3) → (p2 ∧ ((p5 ∨ p1) ∨ p5))) → ((((p2 ∨ (False ∨ (p3 → ((p4 → (False ∧ p4)) ∨ p4)))) ∨ True) ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688885235085687559105701687676 : ((((((p4 ∧ ((p2 → p2) ∨ (p1 ∨ p3))) → (p3 ∧ ((p4 → p3) → p4))) ∧ p4) ∨ ((True ∧ (True → (False ∨ p4))) ∨ (p1 ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55646823952278992572075441379 : (((((p4 ∧ p2) → p4) ∧ p2) ∧ ((((p4 ∧ ((False ∧ p5) ∧ (((p5 ∨ p4) → p4) → p5))) ∧ (p5 → p5)) ∧ (p5 → p5)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197726480251030611964745953501 : ((((p5 ∧ p2) ∨ p3) ∧ ((p1 ∧ False) ∨ False)) ∨ (p2 ∨ ((((True ∨ (p2 ∧ p5)) → ((p4 ∧ (p2 → True)) ∨ (False ∨ p5))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192927734106476702156434350348 : (((((True ∨ True) ∨ (p1 ∧ p5)) → True) ∨ (False → p1)) → ((((p1 ∧ (True ∧ p3)) ∧ (p3 → (p5 ∧ (True ∨ (True → p1))))) → False) ∨ True)) := by
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
theorem thm_5_vars_138311811553579475655810120896 : ((p3 → ((p2 ∧ (p1 ∨ p4)) ∨ (((p2 ∧ ((p5 ∧ ((p4 ∧ True) ∧ p1)) → (True ∨ False))) ∧ p4) ∨ (True ∨ p3)))) ∨ (p1 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47337847984230959697502383547 : ((((False ∨ True) ∧ ((((p3 ∨ False) ∨ ((p1 ∨ ((p3 ∧ (p3 ∧ p3)) ∧ False)) → ((True → True) → p4))) ∨ p4) ∨ p1)) ∨ (False → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718963311101047101033755651785 : (((((p2 ∨ p3) → (p1 ∧ False)) ∨ (((False → p2) → p3) ∧ (((False ∨ (p3 ∧ True)) → ((True → p5) ∧ p4)) ∧ (False → (False ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50200026181047443410739486534 : (((((((p3 → (p2 → False)) ∧ ((p2 ∨ (False ∨ ((p5 → p2) ∨ p5))) ∨ p3)) ∧ p3) ∧ p2) ∨ p3) ∨ ((p2 → p5) ∨ (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115870871939164683941230029621 : (((((p4 ∨ p2) ∧ p3) ∧ False) ∨ ((p3 ∨ True) → (p3 → ((p4 ∨ (p5 → ((p5 ∨ (True → True)) ∧ p3))) ∧ (True ∨ p2))))) ∨ (p3 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



