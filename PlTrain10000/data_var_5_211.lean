variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37459094672073932923967194755 : ((((((p3 ∧ ((p3 ∨ True) ∧ True)) ∧ ((True → p4) → p5)) ∨ (p5 → (p4 ∨ ((p1 → ((p3 → p1) → p4)) ∨ p3)))) ∨ p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191945315748847103641440827447 : ((True → (p4 ∧ (p5 ∧ (((p3 ∨ True) → p2) → False)))) ∨ ((((p4 → p4) ∧ ((p2 → False) ∧ ((p1 ∧ (p5 ∧ p2)) ∧ p3))) → False) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h12 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337350823634667508748030855287 : (p1 → ((((p3 ∨ ((p4 ∧ p4) ∧ ((False ∧ False) ∧ ((False ∧ (False → False)) ∧ (True → p4))))) → (False ∨ p4)) → p3) ∨ (p3 → (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43155803165120933137916075773 : ((((((p5 ∧ (False ∨ p2)) ∧ p1) ∨ ((p4 → p5) → (p3 → ((((p3 ∨ (p1 → p1)) ∨ (p4 ∨ p4)) ∧ p4) ∨ p1)))) ∧ p2) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162891456160688509086864214245 : (((p2 ∨ (p4 ∨ (False ∧ (p1 ∨ (p1 ∨ (((p3 ∧ True) → p2) ∧ p3)))))) ∨ (p3 ∨ True)) ∧ (((True ∨ (p5 ∨ p4)) ∨ p2) ∨ (p2 → p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94714876734207613323091790571 : ((p3 ∧ ((p1 ∧ (((p5 ∨ p1) → ((((False ∧ p4) → False) → ((True → p1) ∨ p5)) → p5)) ∧ p4)) ∧ (p3 ∨ (True → (p1 ∨ p1))))) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (p5 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (((False ∧ p4) → False) → ((True → p1) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h18 : (p5 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h19 := h8 h18
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : (((False ∧ p4) → False) → ((True → p1) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h23 := h19 h20
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_930466132585984137080864008215 : (((((True → (p5 ∨ (p5 ∨ ((p3 ∨ True) → False)))) ∨ True) → ((((p2 ∧ ((p4 ∨ (False → False)) ∧ p4)) → p5) ∧ False) ∧ (p2 ∧ False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p5 ∨ (p5 ∨ ((p3 ∨ True) → False)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735892625936581780584916835760 : ((((True → False) ∧ (p4 ∧ (((False ∧ ((p1 ∨ ((p2 ∧ (p4 → (p2 ∨ (p4 → p4)))) ∨ (p3 ∧ p5))) ∨ (p5 ∨ p4))) ∧ True) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612183338634242671648079561253 : (((((((p3 → (p5 ∨ p5)) ∧ ((p3 ∧ p4) → p3)) → ((p2 → ((p2 ∧ (p2 ∧ (p4 ∧ p4))) ∨ p4)) ∨ p5)) ∧ (p4 ∨ False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197755637102583522220224789772 : (((p3 ∧ (p3 ∨ p3)) ∧ ((p1 → p3) ∨ p1)) ∨ ((p5 ∧ (False ∨ ((p2 ∧ ((p2 → ((p4 ∨ p4) → p4)) → (True ∧ p5))) ∧ False))) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671093943891644699623864505076 : ((((p1 ∨ ((((True ∨ (p2 ∨ p3)) ∧ p3) → ((p5 ∨ (p3 → (p1 ∨ ((p4 → True) ∧ False)))) → p2)) ∧ p1)) ∨ ((p3 → p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246661453561244148182799364444 : ((p5 ∧ p3) ∨ (False ∨ ((p3 ∨ (p2 ∧ False)) ∨ ((True ∨ p5) ∨ (p1 → (((((p4 ∧ p3) ∨ p2) ∧ (p5 ∨ (p4 ∧ p2))) ∨ True) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_337520568393195696272325804471 : (p1 → ((((((False → p1) ∨ ((p1 ∨ True) → (True → True))) ∧ (p3 → ((p4 → p3) → p5))) → False) ∨ p1) ∨ (((p5 → p1) → p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167682546434669428063750767184 : ((((((p1 → (p4 ∧ (p3 → p3))) ∧ (p5 ∧ p2)) → False) ∨ p2) ∧ (p1 ∨ (p4 → p1))) → (((p1 ∧ (p4 ∨ (p1 ∨ p2))) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181023929217164140227421594821 : (((True → p4) ∨ (((p5 ∨ ((p4 ∨ p1) ∨ p1)) ∨ (p5 ∨ p5)) ∧ p5)) → (p3 → ((False ∨ ((False → (p1 ∨ (False ∨ p2))) ∨ p2)) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h14
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214028536136762324024480938455 : ((((p1 ∨ p2) ∧ p5) → False) ∨ (p1 ∨ ((((((p5 ∨ (True ∨ ((p3 ∨ (p4 ∧ False)) → p2))) ∧ p5) → p4) ∨ p1) ∨ p3) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60008263222959007037801063744 : (((p1 ∨ True) → (((p2 ∨ ((p3 → (False ∨ (((p1 ∨ (p4 ∨ p1)) → ((p1 → p4) ∨ p1)) ∨ (p4 ∨ p5)))) ∨ p3)) ∨ False) ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52621001838742944214759780562 : ((((False ∧ (False → False)) ∨ (((p2 ∨ (p2 → p4)) → True) → (p3 ∨ p2))) ∨ (False ∨ (True ∨ (p2 ∧ ((p3 → True) ∨ (p5 ∨ p2)))))) ∨ p2) := by
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
theorem thm_5_vars_136103982453707393886738721439 : ((((False ∧ (p3 ∨ (p4 ∨ p4))) ∨ (p3 ∨ True)) ∨ ((True ∨ (((p2 ∨ (p3 ∧ p3)) ∨ (p4 → p3)) ∨ False)) ∧ True)) ∨ (p1 ∨ (p3 ∧ p2))) := by
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
theorem thm_5_vars_323661322141165044164180430387 : (p5 ∨ (((((False ∨ True) → p4) ∨ (p5 ∨ (((True → p5) ∧ (p1 ∧ (False ∨ False))) ∧ p4))) ∨ (False → p5)) ∨ ((p4 ∧ True) ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141453010824965002608154985500 : ((((True ∨ p1) → False) ∧ (p2 → (p5 → (p5 ∧ (((p4 ∧ (True ∧ p4)) ∨ (((p1 ∨ p2) → True) ∧ p3)) ∨ p1))))) → ((p1 → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111127365155654928966159797808 : ((((((p4 ∧ (p3 ∧ p2)) → (p4 ∨ p5)) → p2) ∨ (p1 ∨ ((p1 ∨ p4) ∨ (((p3 ∧ p4) → (p3 ∨ p5)) ∨ False)))) ∧ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250158710864336104290803075367 : ((True → p5) ∨ (((((((False → p4) ∨ p2) → (p4 ∨ p2)) ∧ (p1 ∨ (p4 ∨ True))) → p3) ∧ (False ∨ p3)) → (p4 → (p3 → (True ∧ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302516194938043795379308496148 : (False ∨ (False ∨ ((p4 ∨ (p5 → (False ∨ (((p5 → p4) → True) ∨ (p3 ∨ (False → (p5 → p5))))))) ∧ (p4 ∨ (((p2 → p5) → True) ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727890374135887926832833123250 : ((((p2 ∨ (p2 ∧ p5)) ∨ (((False → p1) ∨ (((p3 ∨ p3) → False) ∧ False)) → (((p3 ∧ p3) ∧ ((True ∨ (p3 ∧ p1)) → False)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153807287437315936882792433022 : ((p5 → (((True → (True ∨ (((p2 → p4) → ((False ∧ False) ∨ (p3 → (True ∨ p4)))) ∨ p4))) ∨ p3) → p3)) → (p3 → ((p5 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668728570340036209759916281289 : (((((((p1 → False) ∨ (((p1 ∨ p3) ∧ (p2 → ((p1 → p2) ∨ p4))) → ((p1 ∧ p5) ∨ False))) ∨ True) ∨ True) ∨ ((p5 ∧ p4) → p3)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_663943052144242621553617548531 : ((((p4 ∧ (((p4 → (p5 ∨ p1)) ∨ p1) ∧ (p1 ∨ ((p5 ∨ False) ∨ (((False → (p2 ∧ (p3 ∨ p2))) → p4) → p1))))) → (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158162656763936743275759147747 : ((((p1 ∨ (False ∧ p4)) ∧ p2) → (p4 ∨ (((False → p1) → ((p2 ∨ (False ∧ p5)) ∧ True)) ∧ p4))) ∨ ((p2 ∨ (True ∨ p2)) ∨ (p1 → False))) := by
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
theorem thm_5_vars_39757564210275387354341132271 : (((True → (((((((p2 ∨ True) ∨ p3) ∧ (p1 ∨ ((p2 → False) → p5))) ∧ p4) ∧ p5) ∨ ((True ∧ False) ∨ True)) ∧ (p2 → p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137881785986186650531592119911 : ((p4 ∨ (((p1 → (False ∧ (p5 → (((p1 ∨ (True → (p3 ∧ p5))) ∧ (p2 ∧ p1)) → (False ∧ False))))) ∨ p1) ∨ True)) ∨ (p3 ∧ (True ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214521479890115499870325355218 : (((p4 ∧ p5) ∧ (False ∨ True)) ∨ (((p1 → (((p2 → False) → (((p4 → p3) ∨ (True → p3)) ∧ (p5 → p4))) ∨ p1)) → p1) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158704085479730825079474961162 : ((p3 ∧ (((((((p2 → p5) → (p4 ∨ (False → p3))) ∨ True) ∨ p5) → (p3 → p4)) → False) ∧ True)) ∨ (p1 → (p1 ∨ ((True → p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776417546652026441484813496292 : (((p1 ∨ ((((p4 ∨ (p5 → (((p4 ∧ (p5 → p4)) ∨ p3) → ((True → p1) ∨ False)))) ∨ (p1 → (p1 → (p1 ∨ p2)))) ∨ p5) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178276181372856663821252294378 : ((((p1 ∨ p1) ∧ ((True → (True ∧ (p2 ∨ p3))) ∨ False)) ∧ (p5 ∨ False)) ∨ ((p2 ∧ ((p2 ∧ (False → p5)) ∧ False)) → (p4 ∨ (p5 ∨ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201151655843733856478502241740 : ((False → ((p4 ∨ p3) ∨ ((True ∧ False) → False))) → ((False ∨ (True → (((((p2 ∨ p3) ∧ p2) ∧ p2) ∨ (p5 → (False → False))) ∨ p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317710158109990489806629719654 : (p4 ∨ ((((p1 ∨ p4) → (((((p3 → (p4 ∨ True)) → p4) ∧ (True ∨ (True ∨ p3))) ∧ p1) ∧ ((p5 ∨ p2) ∧ p3))) ∨ (p3 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114396307664317485795487089234 : ((((((p2 ∧ p1) ∨ p5) ∨ (p3 ∨ (p4 → (p2 → True)))) ∧ (False ∨ ((p4 → p4) ∧ True))) ∨ (False ∨ (p4 ∨ (False ∨ p4)))) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358580091399265459871578637903 : (p5 → (p3 → (((p4 → (((p1 ∧ p1) ∧ (False ∧ ((p3 ∨ True) ∨ ((p3 ∧ p2) → (p2 → ((p4 ∨ False) ∧ p2)))))) ∨ p2)) ∨ p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166318243336588007170317415919 : ((p5 ∧ (((p1 → (p1 ∨ (((p1 ∧ p3) ∧ (p2 → p3)) ∧ p5))) → p1) ∧ (p2 ∨ p1))) ∨ (((p3 ∨ p1) ∧ (False ∨ (p5 ∨ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55413691329395848347935815947 : (((((p5 ∨ p3) ∧ (p4 ∨ p1)) ∨ p1) → ((True ∧ (p2 → p4)) → ((p1 ∨ (p1 ∧ (p2 → (((p4 ∨ p3) → True) → p2)))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64491812886341458908196749549 : ((p1 ∨ ((p1 ∧ ((p1 ∨ (p4 → ((False ∧ p2) ∧ (p5 ∨ p4)))) ∧ ((p1 ∨ p5) ∧ p2))) ∧ (((p5 ∨ p4) ∨ (p4 → p3)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112514272785369156711594837364 : ((((((True → (p1 ∨ (p1 → (p1 → (p4 ∨ p3))))) ∨ (((p3 ∨ p2) ∨ p2) ∨ (p1 → (p5 ∨ p1)))) ∨ p3) → p2) → p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251832025326477631286675257441 : ((p3 → p4) ∨ (p4 → ((False ∨ ((((p3 → p5) ∨ p4) → (((p3 → p3) ∧ ((p3 → (p5 → p4)) → True)) ∧ False)) ∧ (True → p3))) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 → p5) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302558307297987254335241574438 : (False ∨ (p1 ∨ (((p1 ∨ (((True ∨ p4) ∨ False) ∧ (((p1 ∨ p4) → (True ∧ (p4 ∧ False))) ∧ True))) ∨ (((True ∨ p4) ∨ False) ∨ p5)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722272299385150593207222116533 : (((((False ∧ True) ∧ p3) ∧ (p1 ∨ (p2 ∧ (((p5 → (((p5 → p1) → (p1 ∧ (p2 → p1))) → (p3 ∧ p3))) ∨ p2) ∧ (p4 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51855093151212605468409367782 : ((((True → (((((p4 → p1) → p1) → p4) ∨ (p2 ∧ p2)) → (False ∧ p4))) ∧ p3) ∨ (p5 → ((p2 ∨ p5) ∨ (False → (p5 → p1))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139652199421907691328508266888 : ((((p2 → ((p4 ∧ (False ∧ p4)) ∧ p3)) → (p4 → ((p5 ∨ ((p5 ∧ (True → p3)) ∨ (p3 → p4))) ∨ False))) → False) → ((p3 → False) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → ((p4 ∧ (False ∧ p4)) ∧ p3)) → (p4 → ((p5 ∨ ((p5 ∧ (True → p3)) ∨ (p3 → p4))) ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 → ((p4 ∧ (False ∧ p4)) ∧ p3)) → (p4 → ((p5 ∨ ((p5 ∧ (True → p3)) ∨ (p3 → p4))) ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262341704856941124991560253122 : (True ∧ (((p3 ∧ ((True → p5) → p4)) ∧ (False ∧ ((p2 → p1) ∨ (((p5 ∨ ((True ∨ True) → (p1 ∨ p4))) → p1) ∧ (False ∧ False))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327022398191039038380677272106 : (True → (((False ∨ (p2 ∨ ((p1 ∨ p5) → ((p3 ∧ False) ∨ ((False ∨ False) → p5))))) → ((p4 ∧ False) ∨ (((True ∧ p3) ∨ True) ∧ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h6 =>
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
theorem thm_5_vars_200392555035713950556453737648 : (((p1 ∧ False) ∨ (p3 ∧ ((True ∨ p1) → p2))) → ((((p1 ∨ p1) → (False ∨ p3)) ∧ (p1 → ((p4 → p4) → ((False ∨ p4) → False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41325816863944482942458361031 : ((((p3 ∨ ((p2 ∧ ((((p1 → p5) ∧ True) ∧ p5) → (p3 → p1))) ∨ (False ∧ p2))) ∧ ((p2 ∨ False) ∧ ((False ∨ p5) → p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657213405363593758990449722947 : ((((((False ∧ p5) → p5) → (p3 → (p1 → ((((p3 → True) ∨ (p2 ∨ (p5 ∨ p1))) ∨ (p1 ∧ (p4 ∨ p3))) → p5)))) ∨ (True ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112702816768618946648702457758 : (((((True ∧ (((False ∧ (False ∧ p3)) ∧ (p2 ∨ (p5 → p2))) ∨ (p5 → p2))) ∨ p4) → (p2 ∨ (True ∧ (p5 → False)))) → p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789210401481333919800790117628 : (((p5 ∨ ((((((p5 ∧ p5) ∧ p3) ∨ ((True ∧ p5) → False)) ∨ False) ∧ (((p1 → p5) ∧ p2) → p2)) ∧ (True ∧ ((p5 ∧ False) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149707651457469713966020600638 : ((p5 ∧ (p2 ∧ (p3 → (((p3 ∧ ((p1 ∨ ((p4 ∨ p1) → (p3 ∧ (p4 ∨ p3)))) ∧ p3)) ∧ p1) ∨ p5)))) ∨ ((p3 ∨ p3) → (True ∨ False))) := by
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
theorem thm_5_vars_225738501659295876399143628030 : (((p4 → p2) ∧ p2) ∨ (p2 ∨ ((((p2 ∨ p5) → p2) ∧ True) ∨ ((False ∨ (False ∨ (p2 ∨ ((p5 ∨ p3) ∨ p3)))) ∨ (p4 ∨ (p5 → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45932522605485470118240376251 : (((p4 → (p3 → (((((p2 ∨ p1) ∨ p1) → p5) ∨ (p3 ∨ p3)) → (((p2 ∨ (p3 ∧ p3)) → (p3 ∨ p1)) → (p5 → p2))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51534448306596698623164966520 : (((True ∧ ((p5 ∧ p3) → (((p1 ∧ (p1 → True)) ∨ p4) ∧ ((p2 → (p3 ∨ p3)) ∨ False)))) → ((p2 ∨ p3) ∧ ((p5 ∨ p4) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112923627726053999102606107477 : ((((False ∧ False) → ((p3 ∧ ((((p5 ∨ True) ∨ True) ∧ p3) ∨ ((p3 ∨ p4) → (p1 ∧ (True ∧ p1))))) ∨ (False → p1))) → p4) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641181798334993942850968194309 : (((((p2 ∨ p3) ∨ (((p1 ∧ (((False → (p1 ∧ (p1 → p2))) ∨ p1) → (True ∨ ((p3 ∧ p2) → (p4 ∨ False))))) → p1) ∨ p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164885456311546861496213461434 : (((p3 → ((((p1 ∨ p5) ∨ ((False ∧ (False → (True → p1))) ∨ p4)) ∧ p1) ∧ p4)) ∨ p3) ∨ (((p1 → p3) → (p5 → (False ∨ True))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179832586165638849405438167765 : (((p5 ∧ (((True ∨ (True ∨ p4)) ∧ (p4 ∨ (p2 ∨ p2))) ∨ p2)) ∧ p2) → (p1 ∨ (p4 → (p2 → (((p2 → (False ∧ p2)) → p5) ∨ p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- Implications on the right can always be decomposed.
            intro h28
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Implications on the right can always be decomposed.
            intro h31
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h34
          -- Implications on the right can always be decomposed.
          intro h35
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h38
            -- Implications on the right can always be decomposed.
            intro h39
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h41
            -- Implications on the right can always be decomposed.
            intro h42
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h42
  case inr h43 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h44
    -- Implications on the right can always be decomposed.
    intro h45
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156939019255165980517745653184 : ((((((p4 ∧ (((p4 ∨ p2) ∨ (p1 ∧ p2)) → p5)) → p5) → (False ∨ p2)) ∨ (p2 ∨ p5)) ∨ p1) ∨ (p4 ∨ (p4 → ((p4 ∨ p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708189834652714435548844494870 : ((((p1 → (p5 → (((p2 ∧ False) ∧ p3) ∧ p4))) ∨ ((True ∨ ((p2 → ((True ∧ (p1 ∨ p5)) ∨ ((True ∨ p4) ∧ p4))) ∧ p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93896017362111561218456620332 : ((p1 ∧ (((((p2 → True) ∨ (False → (p3 → False))) ∧ p1) ∧ (p4 → False)) ∧ (False ∨ ((p1 ∨ p3) → ((p1 ∧ False) ∧ (p3 → p3)))))) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53301978781801076213090737522 : (((p4 ∨ ((((p4 ∧ ((p2 ∨ p3) → p2)) ∨ p1) ∧ p2) ∧ p4)) ∨ ((((p3 ∧ p5) ∨ (p5 → p3)) → (p1 → (p1 ∨ True))) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115545668275965594215471623666 : (((p2 → (p5 ∨ (p3 ∧ (True → (True → p5))))) → ((p3 → (p4 → (True → ((False ∧ False) ∨ ((p2 → p5) ∨ p5))))) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718733242084820284889429386538 : (((((p5 → p5) ∧ (p2 ∨ p4)) ∨ ((p3 ∨ ((False ∨ ((True ∨ p5) ∨ ((((True ∧ False) ∨ p3) ∧ (True ∧ p4)) → p5))) → p4)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257444116719351861580099388408 : ((p3 ∨ True) → ((((True → (((True → p5) ∧ p4) ∧ (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∧ True) ∨ p1))) → p1) → False) → (p2 ∧ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((True → (((True → p5) ∧ p4) ∧ (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∧ True) ∨ p1))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h4
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : ((True → (((True → p5) ∧ p4) ∧ (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∧ True) ∨ p1))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Conjunctions on the left can always be decomposed.
        let h33 := h31.left
        let h34 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h35
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h36 := h2 h21
    -- False on the left can always be used.
    apply False.elim h36
  -- Implications on the right can always be decomposed.
  intro h37
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h38 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h39 : ((True → (((True → p5) ∧ p4) ∧ (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∧ True) ∨ p1))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h40
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h41 := h2 h39
    -- False on the left can always be used.
    apply False.elim h41
  case inr h42 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h43 : ((True → (((True → p5) ∧ p4) ∧ (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∧ True) ∨ p1))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h44
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h45 := h2 h43
    -- False on the left can always be used.
    apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204395104101842938612601286397 : (((False → (p4 ∧ (p1 ∧ p3))) ∧ p4) ∨ ((((((p1 ∧ (p1 → False)) ∧ (p2 → (p1 ∨ True))) ∧ (True ∧ (p3 → False))) ∧ p1) ∧ True) → p5)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h7.left
  let h13 := h7.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h14 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639191770787200021287152415467 : (((((p2 ∨ ((p3 ∨ False) → False)) ∨ ((p2 ∨ ((p4 → p5) → True)) → (((p3 ∧ (p1 → (False → (False ∧ p1)))) ∧ True) → False))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147778047051937419523815616616 : ((((p2 → p2) ∨ ((True ∧ False) → ((((p1 → (p3 ∨ p1)) → (False ∨ p4)) ∧ (False → True)) ∧ p5))) → p3) ∨ ((True ∨ (p1 → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636513010581691260057750536001 : ((((((((((p2 ∨ True) ∧ p1) ∧ True) ∨ p3) ∧ True) ∧ ((p3 → p1) ∧ p4)) ∧ (p5 ∨ ((p5 ∨ (True ∨ p2)) ∨ (p1 ∨ p2)))) → p1) ∨ p5) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- One of the premise coincides with the conclusion.
              exact h12
            case inr h22 =>
              -- One of the premise coincides with the conclusion.
              exact h12
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- One of the premise coincides with the conclusion.
            exact h12
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h5.left
      let h28 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h33
            case inl h34 =>
              -- One of the premise coincides with the conclusion.
              exact h12
            case inr h35 =>
              -- One of the premise coincides with the conclusion.
              exact h12
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h38 =>
            -- One of the premise coincides with the conclusion.
            exact h12
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h5.left
    let h41 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h42 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h43 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h44 := h40 h43
      -- One of the premise coincides with the conclusion.
      exact h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h48 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h49 := h40 h48
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h50
          case inl h51 =>
            -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
            have h52 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h39
            -- We have shown the premise of h40, we can now drive its conclusion.
            let h53 := h40 h52
            -- One of the premise coincides with the conclusion.
            exact h53
          case inr h54 =>
            -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
            have h55 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h39
            -- We have shown the premise of h40, we can now drive its conclusion.
            let h56 := h40 h55
            -- One of the premise coincides with the conclusion.
            exact h56
      case inr h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- One of the premise coincides with the conclusion.
          exact h58
        case inr h59 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h60 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h61 := h40 h60
          -- One of the premise coincides with the conclusion.
          exact h61
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152309588352219720886371251939 : ((((p2 ∧ (False ∨ p5)) ∨ p5) ∧ ((p4 → (((True → p4) ∧ p1) ∧ p3)) ∧ (((p4 ∨ False) ∨ True) → p4))) → ((p3 ∨ p3) ∨ (p2 ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47896678267067241872682853585 : ((((p3 ∧ (p3 → ((p2 → (p2 ∨ (p1 → (p4 ∨ (((True → p2) → (True ∨ False)) → p1))))) ∨ p3))) ∨ (p4 → p5)) → (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111597676205185831560180747459 : ((((p4 → (((p1 ∧ (p5 ∨ False)) ∨ ((p3 → (p3 ∨ p5)) ∧ (p2 ∨ (p4 → (p3 ∨ (True ∨ p1)))))) ∨ p3)) ∧ p5) ∨ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685412938356562790660849953642 : ((((((((p4 ∨ p2) ∨ p4) ∧ (((p3 ∨ False) ∨ ((p1 ∨ False) ∨ p1)) ∨ True)) ∨ False) ∧ p4) → ((p4 → False) ∨ (p1 ∧ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231571015135915771565366073100 : (((p5 → p3) ∨ p4) → (((((False → (p2 → p3)) → False) ∧ p3) ∧ True) → (p4 ∧ ((p2 ∨ ((p5 ∨ False) ∨ True)) ∧ ((p3 ∨ p5) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h1
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (False → (p2 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h8
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h19
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h2.left
    let h22 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h2.left
    let h29 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h32 =>
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170030117730331467124647908988 : ((((p1 → (True → True)) → (True → ((p4 ∨ p3) ∨ p5))) ∨ ((True ∨ p5) ∨ True)) ∧ (p4 ∨ ((((p1 ∨ p1) → p2) ∨ (p2 ∨ True)) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354617673015709300134136896647 : (p5 → ((((((p5 → p2) → p5) → (False ∨ (True → p2))) ∨ ((((p1 → (False ∨ p3)) ∧ (True ∨ (p3 ∧ p2))) ∧ p4) ∨ p3)) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802608101684445932677542044227 : (((p2 → (p5 ∨ (True → ((True ∧ (p1 ∧ p3)) ∨ ((((p3 ∨ (((p3 → p1) ∨ (p5 ∧ p2)) → p2)) → (p3 ∧ False)) ∨ p2) ∨ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_687428681832723762552489859375 : ((((((p5 ∧ (((p4 ∧ (False → (p1 → p1))) → p1) ∧ p5)) ∨ (p4 → p1)) ∨ p4) ∧ ((((p2 ∧ (p3 ∧ False)) → p2) ∧ p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681953098766353924028170614711 : ((((((((False ∧ (True ∧ (True ∧ p5))) ∧ ((p1 ∨ True) → p5)) → True) ∧ (p3 ∨ False)) ∨ p1) ∧ (p3 ∨ ((p4 → (p1 ∨ p3)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620202902352996136095930531187 : (((((p3 ∧ p4) ∨ ((False ∧ p5) ∨ (True ∧ ((True → ((((p3 → True) → p4) → True) ∧ (True ∨ (True → p2)))) → (False ∧ p5))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122871569741510371005528862285 : ((((p1 ∨ (p3 ∧ (p3 ∨ p2))) ∨ ((False → (False ∧ p4)) ∨ (False ∨ (((p2 → p5) → False) → p1)))) ∧ (p3 ∧ (p1 ∨ p2))) → (p4 ∨ True)) := by
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
      let h6 := h3.left
      let h7 := h3.right
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
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
        -- Conjunctions on the left can always be decomposed.
        let h19 := h3.left
        let h20 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h3.left
        let h33 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210542414207909573589526639296 : ((((p4 ∧ p3) ∧ p2) → True) ∧ ((True → (p2 → p3)) ∨ (p5 → ((((p4 → False) ∨ (True → (p1 → p5))) → (False ∧ p4)) ∨ (p2 → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192436955662565651109034054291 : (((((p2 → (p2 → True)) ∨ (p5 ∧ p4)) → p5) ∨ p3) → ((((p3 → p4) ∨ (p3 ∨ False)) → (p3 ∨ p5)) ∨ (p1 → (p3 ∨ (False → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65990127253910984345295961613 : ((p4 ∨ (p3 → ((((p1 → True) ∧ ((p5 ∧ (p2 → p3)) → (((p2 ∨ (p5 ∧ (p2 ∧ True))) → (p1 ∧ False)) ∧ p5))) ∨ True) ∨ False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209354469406034702955921349514 : ((False → (p4 ∨ ((False ∧ p1) ∨ p5))) → (p2 → ((((p1 ∧ (p4 ∨ (p3 ∨ p4))) ∨ (p4 → (p2 → p4))) → False) → ((True ∧ p3) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ (p4 ∨ (p3 ∨ p4))) ∨ (p4 → (p2 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∧ (p4 ∨ (p3 ∨ p4))) ∨ (p4 → (p2 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h8
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249070907910918622565952635806 : ((p4 ∨ p1) ∨ (((p3 → p2) ∧ ((True ∧ (p4 → (p3 ∨ p5))) → p1)) ∨ (p1 → ((p2 ∧ ((True ∨ (p4 ∨ p4)) ∧ (p3 ∧ p2))) → p1)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h6.left
      let h13 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328127215505782759170464612654 : (True → (((False ∧ (p1 → (p5 ∨ p5))) ∧ (((p4 ∧ (p4 ∧ False)) ∧ (True ∧ ((p1 ∨ False) ∨ (False → False)))) ∧ p2)) ∨ (True ∨ (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321608203898966255648164033642 : (p4 ∨ (p3 → ((((((p4 ∧ p5) → (True ∧ p2)) ∧ p2) ∨ (p1 ∨ (p5 ∨ False))) ∧ (p5 → ((True → p1) ∨ (p5 → p4)))) ∨ (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216272332003874248618200172655 : ((p1 → (p4 → (False ∨ p2))) ∨ (p1 ∨ ((p4 ∨ ((p5 ∧ p1) ∧ p4)) → (((p2 ∨ p1) ∧ p2) → ((p4 ∧ (True → (p5 ∧ False))) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301144344656120300428196489841 : (False ∨ (((False → ((True ∧ (p2 ∧ True)) ∨ p5)) → False) ∨ ((p2 ∨ True) ∨ ((p3 ∨ (((p2 ∨ ((False ∧ True) → p2)) → p4) ∨ p1)) ∧ True)))) := by
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
theorem thm_5_vars_41738206413633403472257252883 : ((((True ∨ ((False ∨ p5) → p5)) ∧ (True → (p5 ∨ ((p5 ∨ (p2 ∧ p2)) ∧ (p4 → ((p1 → (p5 ∨ True)) ∧ (p1 → p3))))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53281524835339438641778079753 : (((p4 ∧ ((p4 ∧ (((p5 ∧ p1) ∧ (p2 → p4)) ∧ True)) ∨ p5)) ∨ (p4 ∨ (((p3 ∧ (p3 → (p4 ∨ (p4 ∧ p2)))) ∧ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148653304831852528078088026177 : ((((False ∨ (True ∧ p2)) → ((p3 ∧ True) ∨ p4)) ∧ (p5 ∧ (p5 ∧ (((False ∨ p3) → (p2 ∨ False)) ∧ p2)))) ∨ (((p4 ∧ False) → p1) ∨ False)) := by
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
theorem thm_5_vars_174007069430634863416333210721 : (((False ∧ (False ∨ (((p3 ∨ (p5 ∧ (p5 ∧ (True ∧ True)))) ∨ p1) → p4))) → p3) → (p2 ∨ (((p2 → p5) ∨ True) ∨ (p3 ∧ (False → p3))))) := by
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
theorem thm_5_vars_174815419705005613082315152831 : (((p4 → False) ∧ ((p4 ∧ p1) ∧ (p3 ∧ (p5 ∨ (p1 ∨ ((p2 ∨ p1) ∧ p3)))))) → (p2 ∧ ((((p1 ∨ (p3 → p3)) ∨ True) ∧ False) ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h22 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h22
        -- False on the left can always be used.
        apply False.elim h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h27.left
  let h31 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h32 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h40 := h1.left
  let h41 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h41.left
  let h43 := h41.right
  -- Conjunctions on the left can always be decomposed.
  let h44 := h42.left
  let h45 := h42.right
  -- Conjunctions on the left can always be decomposed.
  let h46 := h43.left
  let h47 := h43.right
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h48 =>
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h49 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h44
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h50 := h40 h49
    -- False on the left can always be used.
    apply False.elim h50
  case inr h51 =>
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h52 =>
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h53 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h44
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h54 := h40 h53
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h55.left
      let h57 := h55.right
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h58 =>
        -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
        have h59 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h44
        -- We have shown the premise of h40, we can now drive its conclusion.
        let h60 := h40 h59
        -- False on the left can always be used.
        apply False.elim h60
      case inr h61 =>
        -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
        have h62 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h44
        -- We have shown the premise of h40, we can now drive its conclusion.
        let h63 := h40 h62
        -- False on the left can always be used.
        apply False.elim h63
  -- Conjunctions on the left can always be decomposed.
  let h64 := h1.left
  let h65 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h66 := h65.left
  let h67 := h65.right
  -- Conjunctions on the left can always be decomposed.
  let h68 := h66.left
  let h69 := h66.right
  -- Conjunctions on the left can always be decomposed.
  let h70 := h67.left
  let h71 := h67.right
  -- Disjunctions on the left can always be decomposed.
  cases h71
  case inl h72 =>
    -- One of the premise coincides with the conclusion.
    exact h70
  case inr h73 =>
    -- Disjunctions on the left can always be decomposed.
    cases h73
    case inl h74 =>
      -- One of the premise coincides with the conclusion.
      exact h70
    case inr h75 =>
      -- Conjunctions on the left can always be decomposed.
      let h76 := h75.left
      let h77 := h75.right
      -- Disjunctions on the left can always be decomposed.
      cases h76
      case inl h78 =>
        -- One of the premise coincides with the conclusion.
        exact h77
      case inr h79 =>
        -- One of the premise coincides with the conclusion.
        exact h77



