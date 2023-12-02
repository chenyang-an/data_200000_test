variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647358247114446197602821066105 : ((((p4 → (((p3 → (p3 ∨ True)) ∧ ((p1 → True) ∨ ((p4 ∧ True) ∨ p1))) → (p2 ∨ ((p2 ∨ ((p3 ∧ True) ∨ p1)) → p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41306213856388553653409267026 : (((((True → (((((True ∨ True) ∨ False) ∧ ((p2 ∨ False) ∧ p3)) ∨ p5) ∨ True)) ∧ p2) ∧ ((False ∨ False) ∨ ((p4 ∨ False) ∨ False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138038354399815635305281364256 : ((True → (((p4 ∨ p3) → ((p3 ∨ (False ∧ p4)) ∨ (p2 ∨ p5))) ∧ ((p2 ∨ ((p4 ∨ p3) ∧ (p3 ∨ p2))) ∨ p4))) ∨ (False → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172997566092455983492292901094 : ((p5 ∧ (((p2 ∨ (p4 ∧ ((p2 → p5) → p1))) ∨ p5) → (p4 ∨ (False ∨ p2)))) ∨ ((p2 → True) ∨ (((p5 ∧ False) ∨ p2) ∧ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151174522920114887168347619856 : ((((p4 ∨ (False ∨ (p3 → ((p4 → p5) ∨ ((p5 ∨ p3) ∨ p3))))) → ((p2 → p2) → (p3 ∧ p1))) → p4) → (((True → True) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111916961934497965875330875709 : (((((False ∨ p1) ∨ (((p5 ∨ (p1 ∨ (True → p1))) ∧ p4) ∧ p1)) ∨ (((p4 → ((p1 → p5) ∧ p4)) → True) ∨ p4)) ∨ p1) ∨ (p2 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_686130858901362061658339421756 : (((((p5 ∨ ((False → ((False → True) ∧ (True → (p5 ∧ p5)))) ∧ p1)) ∨ ((p1 ∨ p4) ∨ p3)) → ((True ∧ p2) → ((p4 ∨ True) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55477668456953866336229976942 : (((((p1 ∨ p3) ∨ p3) ∨ (p5 → p5)) → (p4 → (True ∧ ((p4 ∨ (False ∧ True)) ∧ (((False ∨ (p4 ∨ (True ∧ p2))) → False) → False))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h13 : (False ∨ (p4 ∨ (True ∧ p2))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h14 := h9 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h16 : (False ∨ (p4 ∨ (True ∧ p2))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h17 := h9 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h19 : (False ∨ (p4 ∨ (True ∧ p2))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h20 := h9 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h22 : (False ∨ (p4 ∨ (True ∧ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h23 := h9 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683588272140414591860461902784 : ((((((p2 → (((((p2 → (False → True)) → (False → p5)) → p1) ∨ p2) → p4)) ∨ p4) ∧ True) ∨ (p5 → (((p5 ∨ p5) → p1) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245069105182702296590866843802 : ((p1 ∧ p5) ∨ (((True ∨ p2) ∧ p2) ∨ ((p4 ∧ (True ∧ ((p1 ∧ (p4 ∧ (p5 ∨ True))) ∨ p3))) ∨ (True ∨ (True ∨ ((p3 → False) ∧ p2)))))) := by
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
theorem thm_5_vars_123667077776142647223158129346 : (((((False → p2) ∧ p1) → ((p2 ∧ p3) ∧ (False ∧ (((p2 ∨ False) → p1) ∨ False)))) → (((p1 → p5) ∨ (p5 → True)) ∨ True)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44497945289162448314949607936 : (((((False → p1) ∧ (p3 ∨ (p1 → (p1 → (p2 ∨ p1))))) ∧ (((False ∧ ((True → p2) → (False ∨ (p4 → p3)))) ∨ True) → False)) → p1) ∨ p3) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ ((True → p2) → (False ∨ (p4 → p3)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∧ ((True → p2) → (False ∨ (p4 → p3)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65871884094298217656267949374 : ((p4 ∨ ((p2 ∨ p3) ∨ (p5 → ((((((((p3 ∨ False) ∨ False) ∧ True) ∧ (p3 ∨ p5)) ∧ p5) ∨ (p5 → p4)) ∨ (False → True)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113590972593188760872443401451 : (((p4 ∧ (False ∧ ((p4 ∨ ((p2 → (p3 → (p5 ∧ p2))) → (((p4 → p2) ∧ (p2 ∧ p2)) → False))) ∧ p3))) ∨ (p4 → True)) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39379035213013861947549203712 : (((p3 ∧ ((p3 ∧ p5) ∨ (False ∨ (p4 ∨ ((p5 → ((p5 ∨ p4) ∨ ((p3 ∧ True) ∧ p3))) → (p2 → (True ∨ (p4 ∧ p4)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184141735532936076803283192737 : (((p5 ∧ (((p4 ∨ p4) ∧ p4) ∨ (p1 ∨ (p4 → p5)))) ∨ True) ∨ ((p4 ∨ p2) → ((p2 → p1) ∨ ((p3 → ((p5 → p2) ∧ p3)) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338624367516181174223365291400 : (p1 → ((True → (p5 → p2)) → ((((p4 → p5) → (p3 ∧ p2)) ∨ ((p4 ∧ p2) ∨ p5)) → ((False ∧ (False ∨ p5)) ∨ ((True → p1) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141363296989278583469431685488 : (((True → (True → (False ∧ p5))) ∨ ((p4 → (p5 ∧ (False → (((False → p1) → False) ∨ ((p3 ∨ p3) ∧ p4))))) ∧ p4)) → ((False ∧ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157512737359997996044624689484 : (((p5 ∧ (p2 ∧ ((p3 ∧ ((p3 → p3) ∨ p5)) → ((p3 ∧ p1) → (p4 ∨ p2))))) ∨ (True ∧ p4)) ∨ (p2 → ((p1 ∨ (p3 ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_607723253144372156061558911273 : (((((False ∨ ((((p3 ∨ p3) → (p5 ∧ p3)) → p1) ∧ (((p2 ∨ (True → (p1 → ((True → p3) ∧ p5)))) ∧ p4) ∧ p3))) ∧ p5) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_50026818846277828003775356415 : ((((False ∧ ((p1 ∧ p5) ∧ False)) ∨ ((True ∧ (p4 ∧ p1)) ∧ (p4 ∨ (p2 ∧ (p1 → (p1 ∧ True)))))) ∧ (p5 ∨ (p5 ∧ (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245065796060605455076295962265 : ((p1 ∧ p5) ∨ (((p1 → ((True ∨ p2) → False)) ∧ p1) → (((((p2 ∧ (True ∨ False)) ∨ (p5 → (True ∧ p4))) ∧ p5) ∧ True) ∧ (p4 → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h17
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h20 := h18 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158880188460679765478062453002 : ((False ∨ (False ∧ ((p1 → p3) → ((p3 → ((p4 ∧ p5) ∨ (p4 ∨ p3))) → ((False ∧ p4) ∨ p5))))) ∨ ((True ∧ (True ∧ True)) ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65684237019798648157087957986 : ((p4 ∨ ((((p4 → p4) ∨ False) ∨ ((p3 ∨ (((p2 ∧ True) → p1) → (p2 ∨ (((False ∨ False) ∨ p5) → (p4 ∧ p5))))) → p2)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625979211843944157829156463664 : ((((p2 → (((p3 → p5) ∧ ((p3 ∨ False) ∨ (p1 → (p4 → p3)))) ∧ ((p1 → ((((True → True) ∧ p4) ∧ p3) ∧ True)) ∧ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65426769123363674029519227775 : ((p3 ∨ (((False → p5) → p4) → ((((p1 ∨ (((((p2 ∧ (p4 → p3)) ∨ (p1 ∨ p2)) ∧ p3) → p5) ∨ True)) ∨ p2) → False) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40314157764226129914301554157 : ((((((p2 → p2) ∧ ((((p1 ∨ ((False ∨ p3) ∧ False)) ∧ p2) ∨ ((True ∨ p4) ∨ p2)) → ((p1 ∨ p2) ∧ p2))) ∧ False) ∨ p5) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342139712624817444771467797342 : (p2 → ((((((True ∨ p3) ∨ (((False → False) ∧ p4) ∧ p3)) → ((p1 ∧ p1) → p5)) → (p2 → p1)) ∧ p1) ∨ (((p2 ∨ p2) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983355776808327480330568772102 : (((p1 ∧ (((((p1 → (True ∧ p1)) ∨ p5) → False) ∧ p2) ∧ (True → (p5 → ((((p1 → p2) ∨ ((False → p4) ∨ True)) ∨ p1) ∧ True))))) → p5) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 → (True ∧ p1)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56176217478872249983709630360 : (((p2 ∧ (p4 ∧ (p3 ∧ True))) ∨ ((p2 → (((p4 ∨ True) ∧ ((((p2 ∧ True) ∨ p4) ∧ p3) → False)) → p4)) ∨ (True ∨ (False ∨ True)))) ∨ p4) := by
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
theorem thm_5_vars_164618221090096462861184881603 : (((p4 ∧ ((p4 ∨ ((p5 ∧ p5) ∨ ((p3 ∨ p5) ∨ True))) ∨ ((p1 ∧ p4) → False))) ∧ p2) ∨ (((p1 ∧ (False → False)) → (p4 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303112812775975116718035500907 : (False ∨ (p3 → ((False ∨ ((False → p4) → (((p1 → True) → True) ∧ ((p2 → p4) ∧ (((p3 → p5) ∧ (p4 ∧ False)) ∨ (False ∧ p4)))))) → p1))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46270754300916395261318605557 : ((((((p3 ∧ (p4 ∨ True)) ∨ ((False ∧ (p4 ∧ ((p5 → False) → (p3 ∧ p1)))) ∧ False)) ∧ p4) ∧ ((False → p4) ∧ True)) ∧ (p2 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318847992026469600462792970470 : (p4 ∨ ((((p3 → p5) ∧ ((p1 → (p4 → (False ∧ ((p3 ∧ ((p4 ∧ p1) ∨ p4)) ∨ (p4 → p1))))) ∧ True)) ∧ p4) ∨ ((p2 ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205723900497475406152459797052 : (((p3 → p5) ∨ (True ∧ (p1 → p4))) ∨ (((((p1 → (True ∨ True)) ∧ ((p3 → (p3 ∨ p3)) → p4)) → False) ∧ (p2 → (p3 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61590078691196309148341920256 : ((p1 ∧ ((p2 ∨ (True ∧ p5)) ∧ ((p4 ∨ ((p3 → (p1 ∨ ((False ∨ p1) ∨ ((p2 → p1) → (False → True))))) ∧ False)) ∧ (p4 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149862152436361662523894189174 : ((p2 ∨ ((p4 ∧ ((p3 ∨ p1) ∧ (False ∨ (p5 → ((p2 → (p5 → p3)) ∧ ((True → p2) ∧ True)))))) ∧ True)) ∨ (True ∨ (p2 → (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337138978758499493153852799020 : (p1 → ((p4 ∨ (p5 ∧ ((p2 ∧ p1) ∧ (((p5 ∨ p3) → p2) → ((p4 ∨ (p1 → ((p2 ∧ True) ∨ (p2 ∨ p2)))) → p5))))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117382753418688649365484695202 : ((p1 ∧ ((((((p5 ∨ p1) ∨ (p2 ∨ p2)) → p3) ∨ ((p1 → (p3 → ((False ∧ True) ∧ p3))) → p1)) ∧ (True ∧ True)) ∧ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342485948641992670854096580831 : (p2 → (((p5 ∧ ((p4 → True) ∨ (p4 ∨ p2))) → ((p3 → False) ∨ (True → p2))) ∨ (p1 ∨ ((((True ∧ (p3 → p3)) ∧ p3) ∧ True) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62622694838725434904013642308 : ((p4 ∧ (((True → (p4 ∨ ((((p3 ∧ False) ∧ False) ∧ (p5 ∨ p5)) ∨ ((p3 ∧ p5) ∧ False)))) → ((p4 → p2) ∨ (p5 ∧ p5))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43371514302020158322362071722 : (((((p1 → (p1 → ((((p5 → True) ∨ p3) ∧ p2) → ((p3 ∨ (p3 → p5)) → ((p2 → p4) ∨ p2))))) → (p3 → p4)) ∨ False) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340150211689990010252540775734 : (p1 → (p4 → ((((((p2 ∧ p3) → (p2 ∧ True)) → ((p3 ∨ p2) ∧ p5)) ∨ p1) ∧ (p4 ∧ (False ∨ ((p1 ∨ (p5 ∨ False)) ∨ p4)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713872165927155505611417296003 : ((((((p3 ∨ False) ∨ (p2 ∨ True)) ∨ False) → ((((False → True) → (p4 → (p2 → ((False ∧ ((p1 → p5) ∧ True)) ∨ False)))) → p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_449464850258066816030148298 : ((True → ((p1 ∨ (((p4 ∨ ((p4 ∨ p1) ∨ ((p4 → (True → True)) ∧ (p5 ∨ p5)))) ∧ p1) ∨ p5)) ∨ (p5 ∨ (False → p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344816775210581623293144683296 : (p2 → (p4 → (p1 ∨ (False ∨ ((((p5 → False) ∨ (((p2 ∨ ((p3 ∧ p2) ∧ p5)) ∨ p2) → p4)) → ((p2 → False) ∨ (True → True))) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
theorem thm_5_vars_54936828798251384768427714014 : ((((p2 → (True ∧ (p1 ∧ False))) → False) ∧ (p5 ∨ (((p2 → (p5 ∨ (p3 ∧ (p3 → (True ∧ (p2 ∨ (p4 → False))))))) ∨ p1) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247347011248699276763408899591 : ((False ∨ p1) ∨ ((((True ∧ p5) ∧ ((((p4 → (True ∨ p3)) ∨ p5) ∧ p4) ∧ ((((p4 → p1) → p2) ∧ p1) → True))) → (p4 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627879443907272574159754081820 : ((((((((p3 ∧ p5) ∨ (p5 → True)) ∨ ((p2 → p4) ∨ (p1 ∧ p4))) → (False ∨ (p4 → (p5 ∨ (p1 → (p1 ∧ p2)))))) ∧ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147997740112771277792704360943 : ((((((p5 ∧ True) ∧ ((p5 ∨ (False → p4)) → p3)) → (p1 → ((p1 → p4) ∧ p5))) → p5) ∨ (p3 ∨ p2)) ∨ (((p3 ∧ p5) ∧ p2) → p5)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324116403516941203682718573793 : (p5 ∨ (((True → p3) ∨ (p1 ∧ ((p5 ∨ (True ∧ p1)) → (p2 ∧ True)))) → ((((p3 ∨ p1) ∧ (p5 ∨ p5)) → (p4 → p2)) ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h14 : (p5 ∨ (True ∧ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h15 := h7 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h18 : (p5 ∨ (True ∧ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h19 := h7 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h22 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h23 : (p5 ∨ (True ∧ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h24 := h7 h23
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h27 : (p5 ∨ (True ∧ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h28 := h7 h27
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943407514303225113128248153941 : ((((p1 ∧ (p3 → (p1 → p3))) ∧ ((p5 ∧ ((((p4 → (p2 ∧ p2)) → False) ∧ (p1 → (p3 ∨ p4))) ∧ p2)) ∨ ((p1 ∨ p2) → False))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : (p4 → (p2 ∧ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h13
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114666132235009328535929390610 : ((((False ∨ True) ∧ ((((p4 ∧ p1) ∨ p1) → (((p1 ∨ p3) ∧ p5) ∨ p5)) → p1)) ∨ (((True ∧ (p5 ∨ p3)) ∨ p5) → p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117709557916114464314715853422 : ((p3 ∧ (p4 ∧ ((p1 ∧ p1) ∧ ((False ∨ ((p1 → (((p1 ∨ p1) ∧ (p4 ∨ True)) → True)) ∨ p1)) ∨ (p3 → (p5 ∧ p1)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135285594341091974376061165204 : (((p2 → (True → (((False ∨ (p3 → ((p1 → (False → ((p1 ∧ True) → p5))) → True))) → p1) ∧ p2))) → (True → p3)) ∨ (p5 ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638258609438084375900527798234 : (((((p1 → ((p4 ∧ False) → (True ∨ (p2 ∧ p2)))) → ((p1 ∨ (p2 ∨ (p5 ∨ p1))) → (True ∨ (((p5 ∨ p2) ∨ p1) ∨ p5)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736448817361798563843582975346 : ((((p1 → False) ∧ (True → (p3 ∧ (((((p3 → p1) → (p4 ∧ p3)) ∨ p2) → (((((p2 ∧ p1) → False) ∨ p1) → p2) → p4)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689637660068065017490100067974 : ((((((p4 ∨ (True ∨ p2)) ∧ True) ∧ ((p1 ∨ ((p3 → p2) ∧ p4)) ∧ (False ∨ p1))) ∨ (True ∨ ((p3 ∨ p2) ∨ ((True ∧ p2) ∧ p2)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_311793295682036667568247693739 : (p2 ∨ (False ∨ (p2 → (((((p5 ∨ p3) ∨ p5) ∨ True) ∧ ((((p3 → p2) → ((True ∧ ((False → True) → p2)) → p3)) → True) ∧ False)) ∨ True)))) := by
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
theorem thm_5_vars_117746525485242835634975158528 : ((p4 ∧ ((((True ∨ p4) → ((((((p4 ∨ p2) ∧ (False → (False ∧ p3))) ∨ p3) → p1) ∨ p4) ∨ (p2 ∨ p3))) ∨ p1) ∨ p3)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52659320344045348746218385257 : (((p3 ∧ ((((p2 → p5) → (p3 ∨ (False ∧ p5))) ∧ p1) ∧ (p2 ∨ p2))) ∨ ((p3 ∧ False) → (p4 ∨ (((False → p5) → False) → False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_173128489077476902566038935891 : ((p2 ∨ (p5 ∧ (p1 → ((((p5 ∨ p4) ∧ p2) ∨ ((p1 → p2) ∧ True)) ∨ p3)))) ∨ ((p4 ∨ True) ∨ ((p2 ∨ p1) → ((p3 → p2) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810450865232553407982040736787 : (((p5 → ((p4 ∧ (True → (True ∧ (True ∧ (p3 → p5))))) → (((p2 → True) → False) → ((p1 → p2) → (p2 ∨ ((p4 → False) ∨ False)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619706608532844989371401043949 : (((((p5 ∧ p2) ∧ ((p4 ∧ ((p4 ∧ p4) ∧ True)) ∨ (p1 ∨ (p2 ∧ ((False ∧ p3) ∨ ((p1 ∧ p1) ∨ ((p4 ∧ p3) ∨ p3))))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645884577868977666337413774052 : ((((True → (((((p4 → p1) ∨ False) ∧ ((p2 ∧ ((p2 ∧ False) ∧ p5)) ∧ p4)) ∨ ((p1 ∨ p5) ∨ ((p5 → p3) ∨ p3))) ∨ p2)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50539120297921106379072437767 : (((((((((p1 → (p3 ∨ p2)) ∧ p2) ∧ p2) ∧ (p2 ∨ p2)) ∧ True) ∨ (p5 → (True → p4))) ∨ p5) → (p1 ∧ ((p3 ∨ p5) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352338332884566160374144292096 : (p4 → ((True ∧ (False ∨ p4)) ∧ ((True ∨ ((p4 → (True ∧ p3)) → (p3 → p5))) → ((True ∧ ((p2 ∨ (p2 → False)) ∧ p1)) ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173139692811974234572630193534 : ((p3 ∨ ((p1 ∧ ((((True ∨ p4) ∧ p3) → (False ∨ (p3 → p2))) ∨ p3)) ∨ True)) ∨ ((False ∨ ((p1 → p5) ∨ (p5 ∨ p2))) → (True ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_514797415672317462170898910624 : ((((p4 ∨ p5) ∨ (p1 ∨ (((((False ∨ p5) ∧ p5) ∨ (True ∨ p1)) ∨ (((True ∧ (False ∨ (False ∧ p4))) → (False → p4)) → True)) ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323915604070721412776549133450 : (p5 ∨ ((p4 → ((((((False → p3) ∨ (p4 ∨ False)) ∨ p2) → (False → p2)) ∨ p1) → p3)) ∨ (((p2 ∨ (p5 → (p4 ∨ False))) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174121587195577581289475232702 : (((True → (((p1 → True) ∨ (p2 ∧ p4)) ∧ (False ∧ (True → p1)))) ∧ (p4 → p5)) → ((p1 → (False ∨ p1)) ∧ (((p3 ∧ p5) → p1) → p4))) := by
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125930051882569414673683851298 : (((False ∨ False) → (p1 ∧ ((((False ∧ ((p2 → p4) ∨ ((p3 → p3) ∧ ((p5 → (True → p5)) ∨ p4)))) ∨ p3) ∧ p4) → p4))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43590406729944401566882085058 : ((((((p1 ∧ (p5 ∧ p1)) → ((True → (((True ∨ True) → (True ∧ False)) → (p5 ∨ (p4 → p2)))) → (p3 ∨ True))) ∨ False) → p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117379793530901289135486469435 : ((p1 ∧ (((((((((True ∧ (p2 ∨ p3)) ∨ p1) → False) ∨ False) ∨ p4) ∧ (p4 ∧ (p3 ∨ p1))) ∧ (p2 ∨ p5)) ∧ p5) ∧ False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354923485036775793187503651582 : (p5 → ((p2 ∨ ((p1 ∨ ((p2 → ((p1 ∨ (True → (p3 → False))) → (p3 ∨ p4))) → p1)) ∨ (p4 → (((p5 → True) ∧ p1) → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341975659263726969700680483088 : (p2 → ((((False → p2) ∧ ((p4 ∧ (False → ((((p5 ∧ p1) ∨ (p4 ∧ (p4 → False))) ∧ p5) → p2))) → True)) → p3) ∨ ((p1 ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134213071232563228712960375709 : (((((((p4 ∨ True) ∨ (p2 → p1)) ∨ p1) ∨ True) → (p2 → ((True → (p3 ∨ ((p4 ∧ p2) ∨ True))) ∧ True))) ∨ p2) ∨ ((p1 ∨ p3) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137865800648551850475285249871 : ((p3 ∨ (p3 ∨ (((False ∨ p3) ∨ ((p4 ∧ (p3 ∨ ((p4 ∨ p3) → ((p5 ∨ False) ∧ p4)))) ∨ p5)) ∨ (p5 → p1)))) ∨ (False → (p3 ∧ p4))) := by
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
theorem thm_5_vars_54666758460754938002932175651 : ((((p1 → ((True → (False ∧ True)) → p4)) ∨ p4) → ((True ∨ p5) → (True ∧ (((p3 ∧ True) → ((p5 ∨ p4) ∧ p4)) ∨ (p4 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185308144998500981214448903634 : ((p3 ∧ ((p1 ∨ ((True ∧ ((p5 ∨ p5) ∧ p1)) ∨ p3)) ∧ p3)) ∨ (True ∨ ((p4 ∧ ((((p3 ∨ p2) ∨ False) ∨ p5) ∨ False)) ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160505110999232292467485940685 : ((((False → p5) ∧ ((((p4 → p3) ∨ (p1 ∨ p2)) ∨ True) → False)) ∧ (p4 ∨ ((p3 ∧ p2) → p5))) → ((p5 ∨ False) ∨ ((p4 ∧ p2) ∧ True))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (((p4 → p3) ∨ (p1 ∨ p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (((p4 → p3) ∨ (p1 ∨ p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60859647559186726104841976052 : ((True ∧ (p4 ∨ (True → (p5 ∧ (True → ((p2 ∧ True) ∨ ((p4 ∨ ((p1 → False) ∨ False)) → (((False ∧ True) → p4) → (p4 → p3))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169056584506222806827603506225 : ((p3 → (((((p1 ∨ p4) → ((p3 ∧ p2) ∨ (False ∨ p4))) → (p3 ∧ p2)) → p4) ∨ False)) → (((True ∧ (p5 ∧ p2)) → p3) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245101126011626805924973913085 : ((p2 ∧ True) ∨ ((((((p4 ∧ p4) ∧ p3) → p4) → p1) ∨ (p2 ∨ (p2 → ((False → (p3 → (p2 ∨ p5))) ∨ (True → (p1 ∨ p2)))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37404238406264953496481618354 : (((((p3 ∧ ((False ∧ (((False ∨ False) ∧ (p2 ∨ False)) ∧ p5)) ∨ ((((p1 → p4) ∨ p4) → p5) ∧ p1))) ∧ (False → p1)) ∨ True) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746515518767905908125919086139 : ((((p2 ∨ p4) → ((p4 → True) ∧ (((p3 ∨ (p2 ∧ (((p3 ∧ True) → p3) → (p1 → (p3 ∧ False))))) ∨ ((True ∨ False) → p2)) ∨ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53995449344785881949404228890 : ((((p4 ∨ (False ∨ (((False → False) ∨ p5) ∨ False))) ∨ p3) → (True ∧ ((True ∧ (False ∨ ((p5 ∨ (p1 ∧ (p5 ∧ p4))) ∨ False))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304789503277031578918810916814 : (p1 ∨ ((p5 → ((p5 → ((p4 ∨ p4) ∨ (p1 ∧ ((((p4 ∨ False) → p1) ∨ p2) ∨ (p5 → (p5 ∧ True)))))) ∨ (p5 ∨ True))) ∨ (p1 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135724262122926819089005249227 : ((((((p2 → p1) ∧ (p2 ∨ (p3 → p4))) → ((p4 ∧ p3) ∨ True)) ∧ p4) ∨ ((((p2 ∧ p4) ∨ p1) ∧ False) → p5)) ∨ (p3 ∧ (p2 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58269951833118461551514428477 : (((p5 ∧ p4) ∧ (p3 → (p4 → (p2 ∧ ((((p1 → False) → p2) ∨ (p3 → ((((True ∨ p2) ∧ p2) ∨ p1) ∧ (p2 ∨ True)))) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70487605179838888463667658342 : ((((((True → p3) → (p4 → ((p5 ∨ p4) → p1))) → (p1 → (p1 ∧ (False ∧ ((True → p5) ∨ False))))) ∧ ((p1 → p5) → p2)) ∧ p1) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True → p3) → (p4 → ((p5 ∨ p4) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42248431864693513570428168911 : (((False ∧ (p3 → (p2 ∨ ((p1 ∨ (((p1 → True) → (p4 ∧ p2)) ∧ ((p4 ∧ p2) ∨ p3))) → (((p4 ∧ p1) ∨ p5) → p5))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650697496487417875980738265571 : ((((((((((False ∨ False) → p3) ∨ p3) → p1) → p3) ∨ True) → ((p1 ∨ (p2 ∧ p3)) ∨ (True ∧ ((p4 → True) ∨ False)))) ∧ (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601482040966864908822248362638 : ((((p3 ∧ ((p4 → (((p2 ∧ (p2 → ((p2 ∧ (p2 ∧ p4)) ∧ p1))) → ((p2 ∨ p5) ∨ p4)) → ((False ∨ True) ∧ p5))) ∨ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355446532437456004094797643375 : (p5 → (((p4 ∧ (((p5 ∧ ((True ∧ p4) ∧ (p1 ∨ p2))) ∧ p1) ∨ ((True ∧ (p4 ∧ (p3 ∨ p1))) → p2))) ∨ (True ∨ p4)) ∧ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51652373111153365393906768565 : (((((((((p1 → p4) ∧ p2) → p3) → ((False ∧ p3) ∧ p4)) ∧ p4) ∧ p3) → False) ∧ ((((True ∨ p5) → p1) ∨ p5) → (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353405732639049493266479079373 : (p4 → (p1 ∨ (((((p1 ∧ (p1 ∧ (((False ∧ False) ∨ p3) ∧ p4))) ∨ (((p1 ∨ p2) → p4) → p2)) ∧ (p5 → p4)) → (p1 ∨ p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h16 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((p1 ∨ p2) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h21 := h16 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257204745134172883358250113987 : ((p2 ∨ p2) → ((False ∨ (p3 → (((True ∨ p5) ∧ (p2 → (p4 → (p3 → p1)))) ∧ (p4 ∧ p3)))) ∨ (p3 ∨ ((p3 ∨ True) ∨ (True ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_299383415987709872409181950975 : (False ∨ (((p4 ∨ True) → (((p2 ∨ ((p5 ∧ (((p1 ∧ p5) ∧ (p3 ∨ p5)) ∨ (p5 ∨ p4))) ∨ p4)) ∧ ((p4 ∧ True) ∧ True)) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192168143477971642820519476359 : ((((p1 ∨ (((p2 ∧ False) ∨ p5) → p5)) ∧ p2) ∧ p2) → (False ∨ (((p5 ∧ p1) ∨ (p4 → True)) ∨ (p2 → ((False ∨ (p1 → p2)) ∧ p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



