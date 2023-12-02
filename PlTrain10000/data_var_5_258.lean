variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656673461806263134092349701526 : ((((((p1 ∧ (p3 ∧ (False ∧ True))) ∨ p3) ∧ ((p4 ∧ ((p5 ∨ (True ∧ ((p4 → p5) ∨ False))) ∨ p5)) ∨ (p5 → True))) ∨ (False ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756111606786612369758983162771 : (((p1 ∧ ((((((False ∨ p2) → (True ∧ (False ∧ ((p2 ∧ (True ∧ p3)) → p5)))) → p5) ∨ (False ∧ (p4 → p5))) ∨ p2) ∧ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66677737136148233408132985004 : ((True → ((p4 → ((True → p1) → p4)) ∧ (((p4 ∧ ((False → p3) → True)) ∧ (p5 ∧ ((p1 ∧ (True ∨ (False → p5))) → p4))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708798418841934645694031623586 : (((((p5 ∨ ((p5 ∧ (True ∧ p3)) → p2)) → True) → ((((((p5 → (p4 → p1)) → (p1 ∧ False)) ∧ p1) ∧ p3) ∧ (p1 → p5)) → p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223773319044379171358893495600 : ((p2 ∨ (p3 → True)) ∧ ((((((p5 ∨ p1) ∧ p2) ∧ p4) ∨ (p1 → (False ∨ True))) → False) → (((p5 ∨ (p1 ∨ p5)) ∨ p4) ∧ (True ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 ∨ p1) ∧ p2) ∧ p4) ∨ (p1 → (False ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190020029658612443336162270611 : (((((p1 ∨ p3) ∨ ((p5 ∧ p1) → p2)) ∧ p1) ∧ False) ∨ (p2 → ((p3 ∧ p2) ∨ ((p3 ∨ ((p2 ∧ True) ∨ (p2 ∨ p5))) → (p1 → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172304450548413128929893268466 : (((((False → p1) ∧ p1) ∨ (p2 ∧ (False → p4))) → (p4 → ((p5 ∨ p3) ∧ p3))) ∨ (((((True ∨ True) ∨ p4) → False) → p2) ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676138196517649189039119380074 : (((((((p2 → p3) ∧ True) ∨ p2) ∨ ((p4 ∨ (True → p4)) ∨ (True → (False ∨ ((True → True) ∨ True))))) ∧ ((p5 ∧ p2) → (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135490933220597333625440380964 : ((((True → p1) ∨ ((p5 ∨ ((p2 ∧ True) ∧ True)) ∧ (p4 ∨ (True ∨ ((True ∨ p5) ∧ p3))))) → (p4 ∨ (p4 ∧ p2))) ∨ ((p3 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240014202446538126492350033555 : ((p4 ∨ True) ∧ (((False ∧ p2) ∨ (p5 → ((((True → p3) ∧ p4) ∧ ((False ∨ p2) → (p3 ∨ (p3 ∧ p4)))) ∨ p5))) ∨ ((p5 ∨ True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_150519509147874409067298054719 : (((((p5 ∨ p2) ∨ (p4 → (((p2 ∧ (p2 ∨ True)) ∧ True) ∨ p4))) → ((False ∧ (True ∧ p1)) ∧ p2)) ∧ p4) → (False ∧ (p4 → (p2 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ p2) ∨ (p4 → (((p2 ∧ (p2 ∨ True)) ∧ True) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : ((p5 ∨ p2) ∨ (p4 → (((p2 ∧ (p2 ∨ True)) ∧ True) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h14 := h10 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : ((p5 ∨ p2) ∨ (p4 → (((p2 ∧ (p2 ∨ True)) ∧ True) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h21 := h17 h19
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356272080231165798615591818462 : (p5 → ((False ∨ ((((p4 ∨ p2) → False) ∨ p3) → ((False ∧ p3) ∨ ((p2 → p3) ∨ True)))) ∨ (p5 ∨ ((p3 ∨ (p5 ∨ (p5 ∨ False))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322642626711301843609693922083 : (p5 ∨ (((((p3 ∧ (p1 ∨ (False ∨ p1))) ∨ p3) ∧ ((((p1 ∨ p1) ∨ p4) → False) ∧ ((p2 ∧ p2) → (True → (p3 ∨ p4))))) ∧ p1) → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : ((p1 ∨ p1) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h5.left
        let h18 := h5.right
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h19 : ((p1 ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h20 := h17 h19
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h5.left
    let h23 := h5.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h24 : ((p1 ∨ p1) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h25 := h22 h24
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55286485764157177523017460534 : (((p1 ∧ ((False → p1) ∨ (True ∨ p1))) ∨ (p3 ∨ (p4 ∨ (((((False ∨ (p1 ∧ p3)) ∨ (p4 ∧ p1)) ∧ False) ∧ (True ∨ True)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196828735820590016734060716232 : (((p2 ∧ ((p5 ∨ p3) ∨ (p3 ∨ p3))) ∧ False) ∨ (True ∨ (p4 ∧ (p2 ∨ (((True ∨ ((p5 ∨ p3) ∨ (False ∨ p2))) ∨ (p5 ∨ p4)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_13733806639915480066310421444 : (((((((p5 → p3) → p3) ∨ p4) → (((((p1 ∧ (((p2 → p5) → False) ∧ True)) → False) ∨ p4) ∨ p3) ∨ p4)) ∨ True) ∧ (True → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114368975779088200404965690353 : ((((((p1 ∨ (p5 ∧ ((False → p5) ∧ p2))) ∧ False) ∨ (False ∧ (p4 ∨ (False ∨ p2)))) ∨ p5) ∨ (False ∨ (p1 → (p5 ∨ True)))) ∨ (p2 ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215484973702781132397565509753 : ((p4 ∧ ((p5 ∧ p5) ∧ p5)) ∨ ((p1 ∧ (((p3 ∨ True) → (p4 ∨ (p1 ∨ True))) → True)) ∨ (((False ∧ True) ∨ False) → (p5 ∨ (False ∨ p5))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60341266450647592580798738350 : (((p2 → p2) → ((p5 ∨ (((False ∨ (p3 ∨ p3)) ∧ (p3 ∨ (True ∧ (p3 → (p3 → (True ∨ True)))))) ∨ (p3 ∧ p1))) ∨ (True ∨ p2))) ∨ p1) := by
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
theorem thm_5_vars_135749754380847445405648317474 : ((((True ∨ False) ∧ ((p2 ∧ False) ∨ ((True ∨ ((p2 ∧ True) ∧ p3)) → p1))) ∨ ((p5 ∧ (p3 ∨ (p5 ∧ p3))) ∨ p4)) ∨ ((p3 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669930869664169485817085055807 : (((((p5 ∧ ((p2 → (p1 → False)) → (True ∧ (True ∧ p5)))) ∧ (p5 ∧ (((p5 ∨ (p2 ∨ True)) → p1) → p2))) ∨ (p3 ∨ (p2 ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_47702144522907706863248122136 : ((((p4 → ((p2 ∧ p4) ∨ (((((((p2 ∧ p2) ∨ p4) ∧ p5) ∨ False) → p4) ∨ ((p2 → p1) ∧ False)) → p1))) ∧ p3) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47183558488634110996901156870 : ((((((p4 → (p4 → (p5 ∨ ((True ∨ p2) ∧ p4)))) → p3) ∧ p5) ∧ (((p2 ∨ True) ∧ (p2 ∨ (p4 → p4))) → p4)) ∨ (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48786637918862651948502748631 : (((True ∧ (((True ∨ True) ∨ (p5 ∧ (p1 ∨ (((p4 → False) → p1) ∧ ((p1 ∨ (True ∧ p3)) → p2))))) → p2)) ∧ (True ∨ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40897423018877788627114688445 : (((((True ∧ p1) ∧ (((p1 → ((((True ∧ p4) ∨ True) ∨ p4) ∨ (p2 ∨ p5))) ∧ (p5 → (False ∧ p4))) → False)) ∧ (True ∨ False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59349149550705721634036987682 : (((p5 ∨ False) ∨ (p5 ∨ (((((p3 ∧ p4) → p4) → (p3 ∧ (p4 ∨ ((((True → p5) ∧ p3) ∨ (False ∨ p3)) ∨ p4)))) ∧ p1) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307847444732176741710427418735 : (p1 ∨ (p5 → (((p2 ∨ ((((((p5 → p3) ∧ p3) ∧ p3) ∧ p1) ∧ (p5 → (p4 ∨ p1))) ∨ ((p4 ∧ (p1 ∧ p5)) ∧ False))) ∧ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40030452794784086908234211446 : (((((((p3 ∨ ((((p4 ∨ p5) → (((p3 → p5) → p3) ∧ False)) ∨ p5) ∧ (p3 ∨ p5))) ∨ p2) → (p2 ∨ False)) ∧ p2) ∧ False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49443835584944569668861498813 : (((((p1 ∧ (p3 ∧ ((p5 → False) ∧ (p1 ∨ p4)))) ∧ (((p1 → False) ∨ p5) ∨ ((True → p1) ∧ True))) ∨ p5) → (False ∨ (p5 ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353535005821759918840714003820 : (p4 → (p3 ∨ ((True ∧ (p2 ∧ (((p1 → p2) → p3) ∨ ((True → p3) → (((((p2 → (p4 ∧ p1)) ∧ p4) ∨ False) ∧ p3) → p4))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186470799771467774708859581205 : ((((((p3 → False) → p1) ∧ p3) ∨ (p2 ∨ p3)) ∧ (p5 → p5)) → ((p4 → p2) ∨ (False → (p1 → ((p2 → (False → p3)) ∧ (True ∧ p1)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346299261703140321385812895939 : (p3 → (((p2 ∧ ((((p5 → False) → (((p2 ∧ (p3 → p2)) ∧ ((True → p5) ∧ True)) ∨ (True ∧ False))) ∧ p4) ∧ p3)) ∨ p1) ∨ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64956068200842059055391161736 : ((p2 ∨ (((p5 ∧ (((p1 ∨ p4) ∧ p2) ∨ p4)) ∧ True) ∨ (((p5 ∧ (((p1 ∧ False) ∨ p1) → ((p1 → True) ∨ False))) ∧ p5) → p5))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261035009156348472089413953286 : ((p4 → p2) → (((((p4 ∨ p4) ∧ p2) → p1) ∧ ((True ∨ p5) ∧ p4)) → (p1 ∧ ((((p4 → p5) ∨ p3) ∧ (p4 ∨ p2)) ∨ (p4 ∨ p2))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∨ p4) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : ((p4 ∨ p4) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65331017203417096218721683768 : ((p3 ∨ ((((p5 → (((p3 ∨ p2) → False) ∨ (p4 → ((True ∨ p2) ∧ (p4 ∨ p5))))) → p3) ∨ True) ∨ (p1 ∧ (True ∨ (False ∧ p1))))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321590874529269732519550586056 : (p4 ∨ (p3 → ((((False ∧ True) ∨ ((p3 ∧ p4) ∨ ((((((p3 ∧ p1) ∨ p1) ∧ (p2 ∨ p4)) ∨ p2) ∨ p3) ∨ p1))) ∨ (p2 → False)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173137819183317114486115989196 : ((p3 ∨ (((p4 → ((((p1 → p5) ∧ (False ∨ p4)) → p4) ∧ p4)) ∧ p1) ∨ p2)) ∨ (((p5 → False) ∧ p5) → (((p4 → p1) → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62758216079022793096418944993 : ((p4 ∧ (((((p3 → p5) ∧ p1) ∨ (p3 ∧ (((p2 ∧ (((p4 ∨ p5) ∧ p4) ∧ p5)) ∧ p5) ∧ False))) → p4) ∧ ((True → p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208597880629104572446947669529 : (((p3 → p1) → ((True ∧ False) ∧ p1)) → (((p3 ∨ p2) → ((((p3 ∨ p2) ∧ p2) ∨ p2) → False)) ∨ (p5 → ((False → p3) ∨ (p1 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218333183385068361733429076411 : (((False → p4) ∨ (p5 ∧ p4)) → (((((p3 → p2) ∧ p1) → (((((False ∧ p2) ∨ False) ∧ True) ∨ p5) → p4)) → (p1 ∧ False)) ∨ (False → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41579256274812332468121928036 : (((((p2 ∧ (p1 ∧ ((p1 → p5) → p2))) → p5) ∧ (((True → p4) ∨ (((p3 → p2) ∨ p2) ∧ ((p1 ∧ False) → p4))) → p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40331403014490456631002143499 : ((((((p1 ∧ (True ∧ ((((p2 ∨ True) ∧ (p5 → (p4 → False))) ∨ (p1 → True)) ∨ (p2 ∧ True)))) ∨ (p4 ∧ p4)) ∨ True) ∨ p4) ∨ False) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158224540747822629931276223288 : (((False ∨ (p2 → p4)) ∧ (p5 ∧ (((p1 ∨ p4) ∨ (((p2 ∧ p1) → True) → p3)) ∨ (False ∨ p3)))) ∨ (p2 → ((p2 ∧ (False ∨ False)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68345343753228909896262575485 : ((p3 → (((p1 ∧ (((True ∧ p3) → p2) ∨ (p3 ∨ False))) → p2) ∧ ((False ∧ ((p1 ∨ ((True ∨ p1) ∨ p3)) ∧ (p1 ∨ False))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941131203686061286809208688376 : (((((p5 ∨ True) ∨ (p1 ∧ (p3 ∨ p4))) → ((((p4 ∨ True) ∨ p3) → ((((p5 ∧ p4) ∧ ((p5 → False) ∨ p4)) → p2) ∧ False)) ∧ True)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ True) ∨ (p1 ∧ (p3 ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598462826294596672399584406078 : ((((((p2 ∧ p1) ∨ p5) → (p4 ∨ ((p1 ∧ (p2 → (p4 → p4))) → (p2 ∨ ((False ∧ (p2 ∧ True)) ∧ ((p2 → True) ∨ p2)))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206992433436676071713391242125 : ((((p4 ∨ p1) ∧ (p1 → p3)) ∧ p3) → (((((False ∨ ((p2 ∨ False) → ((True ∨ p5) → False))) ∨ (True ∧ (p2 → False))) ∧ p4) ∨ True) ∧ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322271707461936734034115276053 : (p5 ∨ (((True → (((p1 ∨ False) → (p1 → p4)) → ((((True → p2) ∧ p2) → ((False ∧ (p3 ∨ p2)) ∨ p3)) ∨ (p1 ∧ p5)))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233319017985928826418891403918 : ((True ∨ (True → p3)) → (((False → ((False ∧ False) → p5)) → False) ∨ (p5 → ((p2 ∨ False) → ((False ∨ ((p3 ∧ p3) ∨ (p5 ∨ p3))) ∨ False))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769518215696169585481163246863 : (((p5 ∧ (p3 ∧ (p2 ∨ ((p2 ∨ ((False → ((p2 ∧ (True → (p2 ∧ (True ∧ p4)))) ∨ (p5 → ((p3 ∨ p5) ∨ p3)))) → p5)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116995857047834839580592000577 : (((True ∨ p3) → (((((p1 ∧ p4) → True) ∧ (True → (False ∧ (False ∨ ((p5 ∧ p2) ∨ False))))) ∧ (False → False)) → (p1 ∧ p4))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h25 := h18 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118273144315436804910245932408 : ((p1 ∨ (((p2 → p1) ∧ (p2 ∨ p1)) ∧ (p4 → ((p3 ∨ p5) ∨ (False ∧ (((p2 → True) → False) ∨ (p5 ∨ (True ∧ p1)))))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199226675496804221756452463942 : (((p5 ∨ ((p5 ∧ (p1 → True)) ∨ p2)) ∧ p2) → ((((p4 ∧ False) ∨ ((True → p2) ∨ ((p5 ∨ p1) ∧ ((p3 → p4) ∧ True)))) → p4) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
theorem thm_5_vars_173890353467857182351509101650 : ((((True ∧ ((True ∧ p2) → (False ∧ (p3 → ((p3 → p1) → p5))))) ∨ False) → True) → (((p5 ∧ p5) ∧ p1) → (p3 → ((p4 ∧ False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585305680201778746649012918995 : (((((((((p2 → (((p4 ∧ p4) → ((p5 ∧ p3) ∨ p3)) ∧ (False ∨ (p1 → p1)))) ∨ (p1 → True)) → p1) ∨ p2) ∧ p1) ∧ p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135586624805671176235053214897 : ((((p5 ∧ ((p3 → ((p1 → p2) ∨ (p4 → False))) → (p4 ∧ True))) ∧ (p2 → p4)) ∨ (p4 ∧ (p5 ∨ (p1 ∧ p2)))) ∨ ((p3 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124330808504216176468271606584 : (((p1 ∨ (True → ((p2 ∨ p3) → (False → p4)))) ∧ ((p4 → ((True ∨ p1) → p4)) ∧ (p1 ∧ (((p2 → True) ∨ p1) → p3)))) → (p4 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606961305419453372042602869439 : (((((((p5 ∧ (((p4 ∧ (p4 ∧ p3)) ∨ p4) → (p1 → (p5 → p3)))) ∨ p4) ∧ ((((p3 ∨ True) ∧ True) ∧ True) ∨ True)) ∧ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42562247685035240341990251865 : (((p1 ∨ (p1 → (p5 ∧ (((p5 ∨ (((p3 → (p3 ∧ (True ∧ (False ∧ p4)))) ∧ p4) → (p4 → p2))) ∨ p5) ∨ (p5 ∨ p3))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46864926961992606032221888289 : ((((p1 ∨ (((p5 ∧ (True ∧ p4)) ∨ (p4 ∧ (((p1 ∧ False) ∧ True) ∧ p4))) ∨ (((p2 ∨ p4) ∧ False) → False))) ∧ True) ∨ (False ∨ False)) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253081596208430743050349669604 : ((True ∧ p4) → (((p5 ∨ (p5 ∨ (True → False))) ∧ p4) ∨ ((p2 ∨ ((p1 → p4) ∧ (p5 → p1))) ∨ ((p2 ∧ (False ∧ p4)) → (p2 ∧ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173684128949824039690850781772 : ((((p5 ∨ ((((p5 ∧ ((p2 ∨ True) → p3)) ∨ p5) ∧ p5) ∧ p2)) ∨ p2) ∨ p5) → (p1 ∨ (p1 → ((p1 → p3) → (p1 → (True ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172045719910304254754538774318 : (((p3 → (((p1 ∨ ((p1 ∧ (p3 ∨ p2)) ∧ p1)) ∧ p5) ∨ p4)) ∨ (p3 ∨ True)) ∨ ((True ∧ (True ∨ (True ∧ ((False ∧ p2) ∨ p3)))) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350094406452436257539478683584 : (p4 → ((((p4 → (((p2 → (p3 → ((False ∧ True) → p3))) ∨ (p1 ∧ p1)) → p1)) ∧ ((p1 ∧ p1) ∧ p3)) ∨ ((True ∨ p1) ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397965642055678870349997751343 : ((((p4 ∨ (((((p4 → p1) ∧ (p3 ∨ ((p3 → (p5 → p2)) → p1))) ∧ (True ∧ ((p5 → True) → (p3 ∧ False)))) ∨ p5) ∨ p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_37497968469273163271358395415 : (((((p5 → (p5 ∧ p4)) → (False ∨ ((((p3 → ((p4 ∨ p5) ∨ (p4 ∨ p5))) ∧ True) ∧ (p3 ∨ p5)) ∨ (p1 → p5)))) ∨ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158324637609433237941796757695 : (((p4 → (p3 ∧ p2)) → ((True ∧ ((p5 → (p2 → True)) ∧ p5)) ∧ ((p2 ∨ (p5 ∧ True)) → False))) ∨ ((p5 ∨ (p3 → (p4 → p3))) ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759353933152195716704082993559 : (((p2 ∧ ((((True ∨ (True ∨ (((p4 ∧ p4) ∨ p1) → (False ∨ (p3 ∨ True))))) ∧ ((p2 ∧ p5) ∨ True)) ∧ p3) ∨ ((True ∨ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41246409954899492468485462331 : (((((((p4 ∨ p5) → True) ∧ ((((p5 ∧ (True ∨ (True → p2))) ∧ p2) → False) ∨ p2)) ∨ p1) ∨ ((p1 ∨ p3) → (p2 → True))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606171160158184723837849481458 : (((((((((p3 → (p4 → (False ∨ (p3 ∧ (p4 → p3))))) → (((True ∧ p2) ∧ p3) ∨ p4)) ∧ p5) ∨ (True ∨ p3)) ∧ p5) ∧ p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114248903025833428485577449348 : (((p5 ∨ ((((p2 → False) → ((p4 ∧ False) ∨ ((p2 ∧ p5) → p5))) ∨ True) ∨ (p2 → (True → True)))) → (p4 → (p1 ∧ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244390410450676210477990207060 : ((False ∧ p1) ∨ (((((p5 → ((((True ∨ p1) ∨ (True ∧ p1)) ∨ p4) → p1)) → False) ∨ True) ∨ True) ∨ (((p3 ∨ p4) ∧ p4) ∨ (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51331669934460903108629000775 : (((p2 → (((((False → p5) ∨ False) → (True → ((False → (p4 → p1)) → p4))) ∧ True) ∧ p1)) ∨ (((p4 → (p1 ∧ True)) ∨ p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216025983317528972826659055345 : ((p5 ∨ ((False ∨ p4) ∨ p4)) ∨ (((True ∧ p3) → False) ∨ ((p5 → False) ∨ ((((p2 → p2) ∨ p1) ∨ (p1 ∨ p1)) → (p2 ∨ (True ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677460398510453001924453078434 : ((((((p5 ∧ ((p3 → p5) ∧ (((False ∨ p2) ∨ p4) ∧ p4))) ∨ (p2 ∧ (True ∨ (p1 → True)))) ∨ p2) ∨ ((p3 ∨ False) ∨ (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159900354807508205914278406151 : (((((((p3 ∨ p3) ∧ p4) ∨ p5) ∧ (True ∧ (((False ∧ (p5 ∧ p3)) ∧ p4) → p4))) ∨ False) → p1) → ((p4 ∨ (p3 ∨ (p3 ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134843449922484485765549119494 : (((p4 ∨ ((((((True → p1) ∨ False) → (p2 ∧ p1)) → (False ∧ p5)) → (True ∧ ((p1 → p3) ∧ p4))) ∨ p5)) → False) ∨ ((p4 ∧ p3) → p4)) := by
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
theorem thm_5_vars_136295328472545408724556717596 : (((p4 ∨ ((p5 ∨ (False ∨ p1)) → p1)) → ((((((p3 ∨ (p5 ∨ True)) → (True ∧ False)) ∨ True) ∨ True) → p3) → p3)) ∨ (p3 → (p4 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((((p3 ∨ (p5 ∨ True)) → (True ∧ False)) ∨ True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((((p3 ∨ (p5 ∨ True)) → (True ∧ False)) ∨ True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162858059477070753937105663349 : ((((False ∨ (((p1 → (p3 ∧ p5)) ∨ p3) ∨ (p2 ∧ p2))) ∨ (p5 → False)) ∨ (True ∨ p3)) ∧ (((False ∨ (p4 ∨ (False ∧ False))) → p4) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64703175218658226155848941385 : ((p1 ∨ (p1 → (((((p2 → False) ∨ (False ∧ (p5 ∨ p5))) ∨ ((p1 ∧ (p4 ∨ p4)) ∨ p1)) ∨ ((p2 ∨ (p2 → False)) ∨ p1)) ∧ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148408833703909107200811444753 : ((((((p5 → p1) → (((True → False) → (True ∧ p2)) ∨ False)) ∨ True) ∨ p5) → (p1 → (p3 ∨ (p2 ∧ p1)))) ∨ (True ∨ (p4 ∧ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112771382057180332526172801403 : ((((True → ((p4 ∨ (((p3 ∨ True) ∨ p5) ∨ p5)) → p4)) → (p5 ∨ (p4 ∨ ((p4 ∨ False) → ((p4 ∧ p4) ∨ True))))) → p5) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117217549445632785325905429748 : ((True ∧ (((p1 ∧ p4) ∨ p5) → (p4 → (True → (p2 ∧ (((True ∧ p5) → (p2 → (p5 → p4))) → (True → (p1 ∧ False)))))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187417888749622533523184116827 : ((p5 ∧ ((((True ∧ False) → (p4 ∧ p5)) → (True → p2)) ∨ p2)) → (((p3 → (p1 → ((((p3 ∧ False) ∧ p3) ∧ False) ∨ True))) → p3) ∨ p2)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∧ False) → (p4 ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
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
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h5
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110792508825575440226006179623 : ((((((p4 → p3) ∨ ((True ∧ (p5 ∨ ((((False → False) → p2) ∧ p2) ∧ (True ∧ (p5 ∧ p5))))) → True)) → p1) ∨ p4) ∧ p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300407140792701156813617839627 : (False ∨ ((False ∨ (p4 → (((((p2 ∨ p4) ∧ p3) ∨ p2) ∨ (p5 ∧ ((False → p3) → ((p5 → p2) ∨ p3)))) ∨ p4))) ∨ (False → (p4 → p1)))) := by
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
theorem thm_5_vars_351727849044845910920230946952 : (p4 → (((p1 ∨ ((p5 → (p2 ∧ True)) → ((False → p4) ∧ p2))) ∨ (p3 ∨ p2)) ∨ ((p3 ∨ p4) ∨ (p5 ∧ (False ∨ ((False → p2) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46994381042982869621510125465 : ((((((p5 → (p5 ∨ p3)) ∨ ((p1 ∧ p1) ∧ False)) → ((p4 ∧ (p4 ∨ (p5 → (p2 → (p2 ∨ p5))))) ∧ p5)) → p5) ∨ (True → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (p5 ∨ p3)) ∨ ((p1 ∧ p1) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312423221704452917455827598651 : (p2 ∨ (p4 → (((True ∧ p5) → ((((p3 ∧ ((False ∧ p4) ∨ False)) ∨ p2) ∧ ((p5 → p2) ∧ (p3 ∧ (p1 ∨ p1)))) ∨ True)) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356148516189263225789684892450 : (p5 → (((p5 ∨ ((((p4 ∨ False) ∧ p4) ∨ (p4 → p4)) → ((p3 ∨ (p3 → p3)) ∨ p4))) → False) ∨ (p3 ∨ ((p3 ∧ p2) ∨ (True → True))))) := by
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
theorem thm_5_vars_681610405057336934447248418109 : ((((p2 → (((p2 ∧ (True → ((False ∨ p2) ∨ False))) ∧ (True ∧ (True → True))) ∧ ((p2 → True) ∨ p2))) → (p4 ∧ ((True ∨ False) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174026689246285506601782930127 : (((False ∨ (((p2 ∧ ((p2 ∨ p1) ∨ p1)) ∧ (p5 ∧ p1)) ∨ (False ∧ p1))) → p2) → (((False → (p5 → False)) ∧ (p1 ∨ (True → p1))) → p1)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264157592248244800461992927745 : (True ∧ ((((((p2 → p4) ∨ False) ∧ p1) → p2) → False) ∨ (p2 → (p1 → ((p1 → ((p5 ∨ ((p3 ∨ p4) ∨ p5)) ∨ (p3 ∨ p2))) ∨ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203456390246733075328753171988 : ((True ∨ (((p4 ∨ p2) → True) ∨ p4)) ∧ ((p1 → True) → ((p1 ∧ False) ∨ (((p5 → p3) ∧ (((True ∨ p3) ∨ (True ∧ p1)) ∧ p4)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153249663678233092696432950588 : ((False ∨ ((p3 ∨ ((True ∨ (((p2 ∨ True) ∨ (((p2 ∧ p4) ∨ (p5 ∨ p5)) ∨ True)) ∧ p5)) ∨ False)) → p1)) → ((p5 → p4) ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ ((True ∨ (((p2 ∨ True) ∨ (((p2 ∧ p4) ∨ (p5 ∨ p5)) ∨ True)) ∧ p5)) ∨ False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193848594696887336105030094043 : ((True ∨ (((p5 ∧ p1) → (p4 ∧ p2)) ∨ (p3 ∧ p2))) → ((((p3 ∨ p5) ∨ p1) ∨ True) ∧ (p2 → (False → ((False ∧ (p2 ∧ True)) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309340086513993709364384364408 : (p2 ∨ ((((((True ∨ p2) → (p5 ∨ ((p1 ∧ p2) ∨ (((p2 ∧ False) ∨ p2) → p3)))) → False) → p4) ∨ ((p4 ∧ p1) ∧ False)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340875739766383735955058230490 : (p2 → ((((((((p4 ∧ p5) ∧ True) → p2) → (p4 ∧ (p4 ∧ (p5 ∨ p2)))) ∨ p2) ∨ p5) ∨ (((True ∨ (True ∨ p2)) ∨ p4) ∧ p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669761698172292015921612050321 : (((((((p1 ∧ False) ∧ False) ∨ ((p3 → (p5 ∧ p5)) ∧ ((p4 ∧ True) ∨ p4))) ∨ ((p1 → p1) ∧ (True ∧ p1))) ∨ ((p4 ∧ p3) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_49576102326175655820230775239 : ((((((False ∨ ((False → (p1 → p5)) ∨ p1)) ∧ p5) ∨ ((False → p2) ∨ p4)) ∨ ((p4 ∨ p4) ∨ (False → p3))) → ((p3 ∧ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



