variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740366204315456408501178475906 : ((((p1 ∨ p2) ∨ ((((p5 ∨ p2) ∨ ((((p4 ∨ p3) ∧ (p5 ∧ p3)) → True) ∧ p3)) → p3) ∧ (p2 ∧ (p3 ∧ ((False ∨ p1) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313165765318497074643644547927 : (p3 ∨ (((p5 → (((False ∧ ((p3 ∨ False) ∨ p5)) ∧ p4) ∧ p1)) ∧ ((((p1 → (p5 ∨ p2)) → p5) ∧ p2) ∧ ((p4 → p3) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338925813528252974075185451067 : (p1 → ((p1 ∨ p5) → (((p3 ∧ p4) ∧ (((((p2 ∧ False) ∨ True) → True) ∨ False) ∧ (False ∨ p3))) ∨ ((p1 ∧ (True ∧ (p1 ∨ False))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_55487939515383010672307753937 : (((((False ∨ p2) ∧ p4) → (p2 → p1)) → (((p1 ∨ (False → ((True ∨ p4) → p3))) ∧ p5) ∧ (((p2 ∧ (p1 ∨ True)) → p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682126722950541362535465399458 : ((((((p5 ∨ (p2 ∧ (p3 → ((p3 → (p1 → p1)) ∧ (p4 ∨ (p5 ∧ p4)))))) → p5) → p3) ∧ (p3 ∨ (((p1 → p5) ∨ p5) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158738794153926170079119637609 : ((p3 ∧ (p2 → (((p1 → p5) ∧ (p5 ∨ ((p3 ∨ False) ∨ p3))) ∧ (((p2 → p1) → p2) → p2)))) ∨ (((p1 → p5) → (p2 ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707401388718882091972558913372 : (((((p4 ∧ ((False → p5) ∨ p2)) → (False ∧ False)) ∨ (True ∨ (False ∨ (p4 ∨ (((False → (True → (p2 → p5))) ∧ (p4 ∨ p3)) ∨ p3))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_329348129659665584945294973911 : (True → (((False ∨ p2) → p2) → ((False ∨ (((p1 ∨ (((True → (p5 ∨ (p2 ∧ (p2 → False)))) → True) ∨ False)) ∧ (p5 → p1)) ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231462565788644366532324618031 : (((p2 → p5) ∨ p2) → (((True ∧ (p3 → p2)) ∧ ((p1 ∧ p5) → False)) ∨ ((p4 → (p3 → ((p4 ∧ ((p1 ∧ p5) → p4)) ∨ p3))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178306384990119250929303291949 : ((((True ∧ (((True ∨ p5) ∨ (p5 → p5)) ∧ p1)) ∧ False) ∨ (p1 ∨ p5)) ∨ (((p2 ∨ True) ∨ ((True → ((p2 ∨ p5) ∨ p4)) ∨ p4)) ∨ False)) := by
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
theorem thm_5_vars_64187515771268958139400150129 : ((False ∨ ((p5 → p1) → (((True → (((((p1 ∧ p2) → (p5 ∨ p2)) ∨ p5) ∧ p4) → p5)) ∨ (((p2 ∧ p5) ∧ p3) ∧ p5)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65770154566385764526460524042 : ((p4 ∨ (((p1 ∨ (p3 ∨ p4)) ∧ (((p5 ∧ (((True → p3) → p4) → False)) → True) ∧ p5)) ∨ (True ∨ ((p5 ∧ (p3 ∨ p5)) ∧ p1)))) ∨ p2) := by
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
theorem thm_5_vars_205610434837066101456866573456 : (((True ∧ p4) ∨ ((p1 ∧ False) ∧ p4)) ∨ (p4 ∨ (p4 → ((((False ∨ p4) ∨ ((p1 ∨ ((p3 ∨ p3) ∧ p2)) ∨ p5)) ∧ p1) → (p5 → p1))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669913715352718342164405918808 : ((((((p3 ∧ (p2 → (((True ∨ p4) → True) → p1))) ∨ p4) ∧ ((True ∧ True) → (((True → False) → p5) → p3))) ∨ (p4 → (p3 → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233622533770531002313410508582 : ((p2 ∨ (p4 ∧ p3)) → ((((p3 → p4) ∨ p5) ∧ ((((p4 → (p2 ∨ (p5 ∧ False))) ∧ (False ∨ p1)) ∨ p4) ∧ p5)) ∨ ((False → p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204125744471236740627617011687 : ((((p1 ∧ (p5 ∧ False)) ∧ False) ∧ False) ∨ ((p2 ∨ (p1 ∨ p5)) → (p5 → (p3 ∨ (((False ∨ ((p5 ∧ (p1 ∨ p5)) ∧ False)) → p4) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307747199967864916160728437302 : (p1 ∨ (p3 → (((p1 ∧ (p1 → ((True ∨ ((p4 ∨ (True → p5)) ∧ (p3 ∧ True))) ∨ p1))) ∨ p4) → ((p2 → False) ∨ (True ∨ (p5 ∨ p5)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317052052796840506651523692644 : (p3 ∨ (p4 → (((p2 ∧ p1) ∨ (((p5 ∧ ((p5 ∨ p4) ∨ (True ∧ p4))) ∧ ((p5 ∧ False) → p5)) ∧ p4)) ∨ (True ∨ (p4 ∨ (p3 ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171585414890348531667770388089 : ((((((p4 → p5) ∧ ((False ∧ p5) ∨ p3)) ∨ False) ∧ (False ∨ (p2 ∧ p4))) ∨ True) ∨ ((((True → p1) ∨ p4) ∧ (p2 ∨ p5)) ∨ (p1 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715077772787831226840179208970 : ((((p3 ∨ ((True ∨ True) ∧ (False → p4))) → ((False ∨ (p3 ∧ (True → (p2 ∧ p1)))) ∨ ((False ∧ (False ∨ (p5 ∧ True))) ∨ (False ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32314049213236208333334660395 : ((p1 ∨ (p3 ∨ (((((p4 ∨ False) ∨ ((p3 ∨ ((True ∧ (False ∨ p1)) → (p5 ∨ p3))) ∨ p4)) ∨ ((p4 ∧ False) ∨ True)) ∧ p3) ∨ True))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608774947708871370113770588547 : (((((((((p3 ∨ (p2 → (p4 ∧ (True → (p3 ∧ (False ∧ p5)))))) → p4) ∧ p2) ∨ (p5 ∨ p4)) ∨ ((False ∧ False) ∧ p5)) ∨ p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85895725269698221314365225779 : ((((((((p5 ∧ p1) → p5) ∨ p1) → p5) ∧ p4) ∧ p2) ∧ (p1 ∨ ((p5 ∨ ((p3 → p4) ∧ (p4 → ((p4 ∧ True) ∨ p1)))) ∨ p1))) → p5) := by
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
  cases h3
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (((p5 ∧ p1) → p5) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h17 : (((p5 ∧ p1) → p5) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h17
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : (((p5 ∧ p1) → p5) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h24 := h6 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152045468615231382445087404819 : (((p3 → ((((p3 ∨ p2) → True) ∨ (False → p1)) → p5)) ∧ (p2 ∧ (p2 → (((p2 ∨ p5) ∨ p4) ∨ p3)))) → (p4 ∨ ((True ∧ p1) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248164761794639675240974521012 : ((p2 ∨ False) ∨ ((((p2 ∨ p3) ∨ True) ∧ p2) → ((True → (((p1 → (((False → ((False ∨ p4) ∨ True)) → False) ∧ False)) → p1) ∨ p5)) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_157255318358949208902072421972 : ((((((p2 → p5) ∨ p4) ∨ False) ∧ (p3 → (True → (True ∧ ((p3 ∨ p4) ∨ (p2 ∧ p5)))))) → p5) ∨ ((((p4 ∧ p3) ∨ p5) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727783305506856991465117370739 : ((((False ∨ (p1 → p4)) ∨ (((p4 → True) → ((False ∨ True) ∧ (p4 ∨ p2))) ∨ (True ∨ (((p3 ∨ (p3 ∧ p2)) ∨ p2) ∧ (p5 → p3))))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67333950352594860791062855954 : ((p1 → (((p4 ∧ ((((True ∧ p1) ∧ ((p2 ∧ (p3 ∨ p2)) → (p1 → p5))) ∨ (False ∨ (p1 → p4))) → p4)) ∨ (p5 ∨ p3)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308686067308709842518175230766 : (p2 ∨ ((p1 ∨ (((((p1 ∧ (p4 → (p4 → ((p1 → p5) ∨ (p3 → (True ∨ p5)))))) ∨ (p5 ∧ p3)) ∨ p4) → (False → p4)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113587393611417848794946757723 : (((p3 ∧ ((False ∨ ((True ∧ p1) → p2)) → (p3 ∧ (p2 → ((False → (p4 ∨ ((p4 → p5) → p3))) → p4))))) ∨ (p1 → True)) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192720115147291030003727464367 : (((((p1 ∨ p4) ∧ False) → ((p1 ∨ p4) → p4)) → p1) → ((p1 ∧ ((False → False) ∧ (p3 ∨ ((p5 → p4) → p1)))) ∧ (p3 → (p2 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p4) ∧ False) → ((p1 ∨ p4) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- False on the left can always be used.
  apply False.elim h16
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (((p1 ∨ p4) ∧ False) → ((p1 ∨ p4) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h19.left
      let h23 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h23
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h19.left
      let h28 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h28
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h31 := h1 h18
  -- One of the premise coincides with the conclusion.
  exact h31
  -- Implications on the right can always be decomposed.
  intro h32
  -- Implications on the right can always be decomposed.
  intro h33
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h34 : (((p1 ∨ p4) ∧ False) → ((p1 ∨ p4) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h35
    -- Implications on the right can always be decomposed.
    intro h36
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h35.left
      let h39 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h39
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h39
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h35.left
      let h44 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h45 =>
        -- False on the left can always be used.
        apply False.elim h44
      case inr h46 =>
        -- False on the left can always be used.
        apply False.elim h44
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h47 := h1 h34
  -- One of the premise coincides with the conclusion.
  exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780128729624692180755354997700 : (((p2 ∨ ((p3 ∨ (((p4 ∧ ((p5 → True) ∨ (p4 ∧ (True → ((((p5 ∧ p3) → False) → p4) → p4))))) ∨ p4) ∨ False)) → (False ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
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
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52963240097711444767696839486 : (((((p1 ∨ ((p4 → ((p4 ∧ p5) → False)) ∨ True)) ∧ p1) → p2) ∧ ((p4 → p2) ∨ (((False ∨ ((p3 ∨ p4) ∨ False)) → p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677786408174791183476322762781 : (((((p1 → (p2 → (p5 → (((p3 ∧ (True ∧ (p1 → True))) ∧ False) ∧ (p2 → (p4 ∧ True)))))) → p4) ∨ ((True ∧ False) → (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148014084964706106269886556344 : (((((p1 ∨ (((p2 ∨ ((p3 ∧ p5) ∧ True)) ∨ p3) ∧ p5)) → p1) → ((p4 ∨ p3) ∧ p5)) ∨ (p3 ∧ p4)) ∨ (False → ((p4 ∨ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113980345870993991244403969379 : (((p1 ∨ (((p3 ∨ p4) ∧ ((p3 → p4) ∨ p2)) ∧ (((((p1 → p2) ∨ p4) ∧ p2) ∨ p1) ∨ p2))) ∧ ((p4 ∨ p2) → p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45380105888585395348256218187 : (((p4 ∧ (False → (p2 → ((((p4 ∧ (p4 ∨ False)) → p1) ∨ (p5 ∧ (((False ∨ (p1 ∧ (p4 ∧ p3))) → p3) → False))) ∧ p1)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156907416511716787170061616914 : ((((((p1 ∧ ((p2 ∨ p4) ∧ p5)) → ((p3 → (p2 → (True ∧ p1))) → p3)) ∨ False) → p5) ∨ True) ∨ (True ∧ (True ∧ (p2 ∧ (p5 ∧ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147338936524893943990624676527 : ((((p2 → ((((p5 ∧ p4) ∧ (p3 ∧ p1)) → p2) → ((p4 ∧ p1) ∨ (p1 → False)))) ∨ (False ∨ p5)) ∨ True) ∨ (((p4 ∧ p1) ∧ p1) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158316041121074023829853374506 : (((p3 ∨ (p1 ∧ p1)) → ((((p1 ∨ (p2 ∨ p3)) ∨ ((p3 ∧ p4) ∧ p4)) → (False ∨ False)) ∨ p5)) ∨ ((p1 → (False ∨ (False → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49636073062542147085041843062 : ((((((p5 ∧ True) ∨ p1) ∧ p1) ∧ ((p3 → (p1 → (((p5 → p5) → (p2 ∧ (True → True))) → p2))) → p4)) → (p1 ∧ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198455598490968115296355858686 : ((p5 ∧ ((p5 ∨ (p5 ∨ p5)) ∨ (p3 ∧ p4))) ∨ (False → ((p5 → ((p2 ∧ (False ∧ p2)) ∧ ((p5 ∨ p5) ∨ True))) ∧ ((p3 → True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46355869548747140948697369700 : ((((p4 ∨ (p3 ∧ (p2 → ((((True ∧ p4) → True) → (True ∨ p1)) ∨ True)))) → ((p1 → (p2 → False)) → (p5 ∧ p4))) ∧ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762344317101225859519117210248 : (((p3 ∧ ((((((p4 ∨ p4) ∨ (False ∧ True)) ∨ (True ∨ ((p5 ∨ p3) ∧ p1))) → p2) ∧ ((p1 ∨ False) ∧ p5)) ∨ ((False ∨ p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117731472255313399542746787366 : ((p3 ∧ (p4 → (((p1 ∨ (True → p5)) ∨ p2) ∧ (((p5 ∨ (p3 ∨ (p1 → p3))) ∨ False) ∨ (p1 ∧ (False ∨ (p5 ∧ p3))))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137723195859496066098493066504 : ((p1 ∨ ((p2 → p5) → (((((((p3 → (True → p2)) ∨ (True → (p2 ∧ p5))) → p4) → False) → False) → p5) ∨ p4))) ∨ (False → (p4 ∧ False))) := by
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
theorem thm_5_vars_14460321443598821364189648039 : (((((((((p5 → True) ∨ (True ∧ (p2 ∧ (p1 ∧ (p1 ∧ True))))) ∧ p3) ∨ (p5 ∧ p4)) ∧ p3) ∧ (p5 → False)) ∧ p5) ∨ (p2 → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322286071072726792014855693507 : (p5 ∨ ((((p5 → ((p1 → (((p1 → p2) ∨ (p1 ∧ p5)) → p4)) ∨ (((True → (p1 ∧ p2)) ∨ (False ∨ p3)) → p1))) → p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65933909892787172429320204802 : ((p4 ∨ (False ∨ (((p1 → (((p5 → (((p2 → p5) → ((False ∧ (p2 ∨ p4)) ∨ p4)) → p4)) ∧ (p2 ∧ p5)) ∧ p2)) ∨ p2) ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_49708770298518674021421525412 : ((((p2 → p2) → ((True ∧ ((p3 ∧ (p5 → (p4 → True))) → p3)) ∨ ((((p3 → p2) ∨ p5) ∨ p2) → p2))) → (p3 ∨ (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60198994593072148075084721780 : (((p5 ∨ p5) → (((p2 → (((p5 ∨ False) ∨ (((p2 ∧ p1) → True) ∧ p3)) → ((p2 → p4) ∨ (p5 → p3)))) ∧ (p4 → p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345472149543794854728439417874 : (p3 → (((((p3 ∨ p5) ∨ (p2 ∧ (p2 ∧ (True → p3)))) → ((p5 ∧ p2) ∧ ((p5 ∨ (p1 ∧ p3)) ∨ p5))) ∨ (p2 ∨ (p5 ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48990230024791579521219858503 : (((((True → True) → ((p4 ∨ (True → (((p5 ∧ (p1 ∧ (p2 ∨ p4))) ∧ (p1 ∨ p2)) → p3))) ∨ p5)) ∨ p4) ∨ ((p5 ∨ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249957044149420361597615455883 : ((True → p2) ∨ ((((p2 → ((p2 → (p2 ∧ p3)) → ((p4 ∨ ((p5 ∧ (p5 → ((p2 ∨ True) ∧ p1))) ∨ True)) → p1))) ∨ p4) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620171617933444214932418016116 : (((((p2 ∧ p3) ∨ (((False → (p3 → False)) ∧ ((p2 → p5) → (((p3 ∨ (False ∨ False)) → p5) ∧ ((p5 → p4) ∨ p2)))) ∨ True)) ∨ p2) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62563905454145314932424016816 : ((p3 ∧ (p5 ∨ (((p4 → p3) ∧ p4) ∧ ((p4 ∧ (False → p4)) ∨ (((p2 ∧ p3) ∧ p3) → (((p5 ∧ p2) ∧ (p1 ∨ p3)) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785852502072042595082770519117 : (((p4 ∨ ((p4 → ((((((p4 → (((p2 ∧ (p4 ∨ p4)) ∧ (p5 ∨ p2)) ∧ p2)) ∨ p4) ∧ p4) ∨ p2) ∧ (p2 → False)) → p2)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321205389893543330880736443914 : (p4 ∨ (p3 ∨ ((p1 ∨ p4) ∨ ((p2 → (p4 ∨ (((p4 → p1) ∨ (p5 → (p1 → ((p4 ∨ p2) ∨ p4)))) → p5))) ∨ (False → (p1 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353760125120625806246524130150 : (p4 → (True → (p2 ∨ (p2 → ((True ∨ ((True ∨ p4) ∧ ((p3 → False) ∨ p5))) → (p5 → ((False ∧ p5) ∨ (p2 → (p2 ∧ (p2 ∨ p5)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h20
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147338134885011600003221469423 : ((((p3 ∨ (((True → ((False ∨ (True ∧ (p1 → p4))) ∧ p2)) → (p5 ∨ p4)) ∨ True)) ∨ (p2 ∨ False)) ∨ False) ∨ (p2 ∨ (p4 → (p2 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60854948939050861774203416755 : ((True ∧ (p4 ∨ ((p3 ∨ (p4 ∨ (((((p2 ∨ (p1 ∨ False)) ∨ False) ∨ True) ∨ (p5 ∨ p1)) ∨ ((p5 → p4) ∨ (p5 → p3))))) ∧ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58898032039461367587777821410 : (((False ∧ p4) ∨ ((False ∧ p2) ∨ ((False ∨ p4) → (((False ∧ (p1 ∧ (p4 ∧ p2))) → ((((False → p5) ∧ False) → p3) → p5)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141932571805258632355495001342 : (((p2 ∧ p3) → (p2 ∧ (False ∧ (((((((p4 ∨ p2) ∧ p1) ∧ (False → p4)) ∨ (True ∨ p4)) ∨ False) ∨ True) ∨ p5)))) → ((True → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137453451137206114129919611533 : ((p4 ∧ ((True → (p3 ∨ False)) → ((False ∨ (((p2 ∨ p1) ∨ p3) → False)) ∨ (((False ∧ p5) → p5) ∨ (False ∧ False))))) ∨ ((p2 → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120917782219495918746130707284 : ((((((False → p5) ∨ p4) → p2) ∧ (p2 → ((p4 → p5) → (p3 ∨ ((p3 ∨ p3) ∧ (((True → p2) ∨ p4) ∧ p3)))))) ∨ p2) → (p2 ∨ p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False → p5) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116201949356691449949711677171 : ((((True → True) ∧ p2) ∨ ((p3 ∧ True) → (((p4 ∨ p3) ∧ p4) ∨ ((p4 ∧ ((False ∧ ((p4 ∨ p3) → p5)) ∨ p1)) ∨ True)))) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259479019202041486275771799931 : ((False → p4) → (p5 ∨ (((((p2 → (((True ∧ p5) ∨ p2) → False)) ∨ True) ∨ (((p5 ∧ p3) ∧ (p2 ∨ False)) ∧ (False ∧ True))) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_97258980258482746007016752350 : ((p2 ∨ ((((False ∧ ((((False ∨ True) → p2) ∨ False) → p1)) → p5) → ((p1 ∧ False) → ((p5 ∧ p4) ∧ p4))) → ((p5 ∨ p4) ∧ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((False ∧ ((((False ∨ True) → p2) ∨ False) → p1)) → p5) → ((p1 ∧ False) → ((p5 ∧ p4) ∧ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h4
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54838879438394993344753791721 : (((p4 → (((True ∧ p1) ∨ (True → True)) ∨ p3)) → (((p5 ∨ (((True → (True ∨ p4)) → p2) ∧ True)) ∨ False) ∨ (p4 ∨ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168366479523834133231409221508 : (((p1 ∨ p5) ∨ (p1 ∨ (((p5 ∨ p2) ∨ p1) → ((p3 ∨ (True ∨ p4)) ∧ (p2 → p2))))) → (p4 → (((p3 ∨ p2) ∨ True) ∨ (p2 ∨ p5)))) := by
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114622224135614747458995516827 : ((((((p5 ∧ (True ∨ False)) ∧ p1) ∧ (False ∨ (False ∨ (True → (True → p5))))) ∧ p5) ∨ (True ∨ ((False → (p5 → p2)) → p2))) ∨ (p4 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655645545253330868328959078702 : (((((((p3 ∨ p1) ∨ (((p1 → ((p2 ∨ (p3 ∧ p1)) → (p3 ∧ True))) ∨ True) ∨ p1)) ∧ p1) ∧ ((p2 ∨ False) → p1)) ∨ (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758918274757596603638368884812 : (((p2 ∧ (((True ∧ (((p3 ∨ False) → ((p4 → (p5 ∧ p3)) → (p4 ∨ (p5 ∧ True)))) ∧ p4)) ∨ (p5 ∨ (True ∧ (p5 → p1)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121563500829893289606401421700 : (((((p5 ∨ ((p4 ∧ p2) ∨ p1)) ∧ ((True ∧ p5) ∧ (((p2 → (p1 ∧ (p1 ∨ p3))) → p1) ∨ p1))) → (False ∨ p5)) → p2) → (p2 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ ((p4 ∧ p2) ∨ p1)) ∧ ((True ∧ p5) ∧ (((p2 → (p1 ∧ (p1 ∨ p3))) → p1) ∨ p1))) → (False ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h5.left
        let h18 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h5.left
        let h25 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h30 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h30
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h31 : (((p5 ∨ ((p4 ∧ p2) ∨ p1)) ∧ ((True ∧ p5) ∧ (((p2 → (p1 ∧ (p1 ∨ p3))) → p1) ∨ p1))) → (False ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h32
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h36.left
      let h39 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h41 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h39
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h34.left
        let h47 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h46.left
        let h49 := h46.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h50 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h49
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h34.left
        let h54 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h55 := h53.left
        let h56 := h53.right
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h57 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h56
        case inr h58 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h56
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h59 := h1 h31
  -- One of the premise coincides with the conclusion.
  exact h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137416953486083577435466602513 : ((p4 ∧ ((p3 ∨ (False ∧ (((((p5 ∧ (p2 → p3)) ∧ p5) → p3) ∨ (p1 ∧ p3)) ∨ (p4 ∨ (p3 ∧ False))))) ∧ True)) ∨ (p2 → (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117715707304596146209539064142 : ((p3 ∧ (p1 ∨ ((p2 → ((p4 ∨ p4) ∨ (p2 ∧ p5))) ∨ (True ∧ (p1 → (((p4 ∧ p5) ∨ (False ∧ (True ∨ p3))) ∧ False)))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206432127776017240227369286427 : ((p4 ∨ ((p4 ∧ (p1 ∧ p1)) ∧ False)) ∨ (True ∨ ((p2 ∨ True) → (((p4 → p1) ∧ p1) ∧ (((((p3 ∧ True) ∨ p4) ∧ False) → False) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314863064546749761773377796919 : (p3 ∨ (((True → ((p2 ∨ (p1 → True)) ∨ (p5 ∨ p4))) → (p3 ∧ p1)) → ((((((p4 ∧ p4) ∧ p4) ∨ (True → False)) ∧ p3) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159205892590868345467032731002 : ((p2 → ((False ∧ (p3 ∧ (((True ∧ False) ∨ (p1 ∨ p3)) ∧ False))) ∨ (True ∨ (p1 ∨ (False → p4))))) ∨ (p1 ∧ (p5 ∨ (True ∨ (p1 ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141028192821706127238884780727 : ((((p5 → (p3 → False)) ∨ ((False ∧ True) → p1)) ∧ (False ∨ ((p5 → (((p1 → p1) → (True ∨ False)) → p4)) ∨ p4))) → ((p1 ∨ True) ∨ p4)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51986536933205350712141458217 : ((((True → p2) ∨ ((p2 → ((p5 ∧ ((p5 ∨ False) ∨ (p4 ∨ p2))) ∧ p5)) ∧ p1)) ∨ (p2 ∧ ((p3 ∧ (p2 → p1)) ∧ (p4 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387561676403783998912632368217 : (((((p3 ∨ ((((p3 ∨ (p2 ∨ ((True ∨ False) → (True ∧ p3)))) ∨ (p2 → (p2 → p1))) → p5) ∨ p2)) ∨ (p4 ∨ (p3 → p4))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_346642288257823580291269687363 : (p3 → ((True → (((((p1 ∨ ((p1 → p3) → p2)) ∨ (p5 ∧ (p2 ∧ p1))) → p4) ∨ (p3 ∧ (False ∧ p5))) → p5)) ∨ (p3 → (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733297069212197905297040065257 : ((((p3 ∧ p4) ∧ (p1 ∨ (((p1 ∨ (p1 ∨ (False → (((False ∨ p5) → (p5 ∨ True)) → p2)))) ∨ False) → (False ∨ (p5 → (True ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720193983576159415068062299500 : (((((p3 ∨ (p4 → p1)) ∧ p2) → (((True → (((((p5 → p5) ∧ (p3 → False)) → p5) ∨ False) ∨ (True ∧ p5))) → p3) → (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51601673086848327352415910913 : (((p4 → ((((p4 → p1) → ((p1 → False) → ((p5 → True) ∧ True))) ∧ p2) ∨ (True ∨ False))) → (((p3 → p5) ∨ p5) ∨ (False → False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138582949869647879375251418511 : ((((((p1 ∨ p5) ∧ p1) ∨ ((p1 → (p3 ∨ (p4 → ((p5 ∨ False) ∨ False)))) ∨ ((False ∧ p1) ∨ p1))) → p1) ∧ p3) → (False ∨ (p1 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ p5) ∧ p1) ∨ ((p1 → (p3 ∨ (p4 → ((p5 ∨ False) ∨ False)))) ∨ ((False ∧ p1) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52493915312005503500600942310 : (((p4 → ((p5 ∧ ((p2 ∨ ((False ∧ (p1 ∨ p3)) → False)) ∧ p1)) ∨ True)) ∧ ((p1 ∨ (False → p2)) ∧ (((True ∧ p5) ∧ p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67646014582605798028906000461 : ((p1 → (p2 ∨ ((p5 → (True ∧ (((p5 ∨ False) ∧ (((p1 ∨ (((p4 → p3) ∧ p2) → False)) → p4) ∧ (p5 ∧ p2))) ∨ False))) ∨ p1))) ∨ p4) := by
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
theorem thm_5_vars_688994507925946807999177655584 : ((((((p3 → ((p2 → p3) ∧ (p4 ∨ (False ∧ (p3 ∧ (p4 ∧ p2)))))) ∨ False) ∨ p2) ∨ ((p3 ∨ (p5 ∨ (True ∨ (p5 ∨ True)))) ∨ p1)) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117620168169790054104584534811 : ((p3 ∧ (((p2 → (((((p3 ∧ p5) → p3) → p3) ∨ (p4 → p4)) → (p3 ∧ (False ∧ p5)))) → (True ∧ (p5 ∧ p1))) ∧ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110878551080426779023703671475 : (((((((p2 ∧ (p5 → p4)) ∨ (((p3 ∨ (True → p4)) → True) ∨ p4)) ∧ (p1 ∨ p3)) ∧ (p4 ∨ (p5 ∨ p1))) → p4) ∧ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246036381604499070272742261666 : ((p4 ∧ False) ∨ ((p5 → ((True → p4) ∨ ((p4 ∧ False) ∧ p2))) → (p2 ∨ (((False → p3) → False) ∨ ((p2 ∨ True) ∨ ((p3 ∨ p1) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810377990151291680893213541312 : (((p5 → (((((p3 ∨ p2) → p5) → p2) ∨ (p2 ∧ (p1 → False))) → ((True ∧ p5) ∧ ((((p1 → p4) → p5) → (p3 ∧ False)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58176523524403412656668722729 : (((p3 ∧ p2) ∧ ((p3 → (((False → p2) ∨ (((p4 ∧ p1) ∧ (False → ((p5 → p3) → (True ∧ True)))) → p4)) ∧ False)) → (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157404573100093004572829065114 : (((((p4 → p1) ∨ ((((p2 ∨ (p2 → p2)) ∧ p5) ∨ p1) ∨ p1)) → (p1 → p5)) ∧ (p2 ∨ p4)) ∨ (True ∧ (((p1 ∧ p1) → True) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336244327685089051923356608198 : (p1 → ((((((((((p3 ∨ False) ∨ p3) ∧ (True ∨ True)) → p5) → p2) ∨ (True ∨ False)) → p2) ∧ p2) → ((p1 → p3) ∨ (p4 ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319747809222120063000048907289 : (p4 ∨ (((False ∨ p5) ∧ (False ∧ (p5 ∨ p2))) ∨ (((p1 ∧ p4) ∨ ((p3 ∧ False) ∧ (p3 → p1))) → (p2 ∨ (p3 → (p2 ∨ (p5 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305703488032537699988055439786 : (p1 ∨ (((p2 ∨ ((p3 ∨ p2) → ((p4 → False) ∨ p4))) → True) → ((((p4 → p2) ∨ ((p4 ∧ (p2 ∨ (p4 → p5))) ∨ True)) ∨ p3) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257385774666469291297918322684 : ((p2 ∨ p5) → (((p3 ∧ p4) ∨ ((True → p5) ∨ ((p3 ∨ (True ∨ (False ∨ p1))) ∨ ((p1 ∨ False) → p4)))) → (p1 → (p4 ∨ (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h21
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- False on the left can always be used.
              apply False.elim h23
            case inr h24 =>
              -- Disjunctions on the left can always be decomposed.
              cases h1
              case inl h25 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h25
              case inr h26 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29



