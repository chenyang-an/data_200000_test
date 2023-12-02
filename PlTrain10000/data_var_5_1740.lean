variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48922317935998540396976774893 : (((((((p2 ∨ (True → p5)) ∨ p3) ∨ (((p5 ∧ (True ∧ True)) → p4) → (p4 ∧ (p2 ∧ p4)))) ∨ False) ∧ p5) ∨ ((p1 → p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_400100600699535175952729026362 : ((((p4 → (p2 ∨ (((((p4 → (((p2 ∧ True) ∨ (p2 ∨ p4)) ∧ p3)) → False) ∨ (True ∧ ((p5 → p5) ∧ True))) ∧ True) ∨ p5))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53569139630511998543004928204 : (((((True ∧ p4) ∨ ((p4 ∨ (True ∨ p1)) ∧ True)) ∨ p5) ∧ (((True ∨ (((p5 ∧ (False ∨ p3)) ∧ p4) ∨ (p3 → p2))) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801181527630369863707757363196 : (((p2 → ((((p1 ∧ p4) → p1) → (True → ((p4 ∧ (p4 ∧ (((p1 → False) ∨ False) ∨ p5))) ∨ p3))) → (p4 → (p5 ∧ (True → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300828691053396789469076067242 : (False ∨ ((p2 ∨ (((False ∧ (((True ∧ ((p1 ∨ p4) → p3)) → p2) ∧ p3)) ∨ p3) ∨ True)) → (p2 ∨ (((p1 ∨ True) → False) → (p4 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
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
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- False on the left can always be used.
        apply False.elim h11
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h18 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149565939880033334674660392845 : ((p2 ∧ (False ∧ ((p3 → (False ∨ (False ∨ (p1 ∨ p4)))) ∨ ((p3 → (p4 ∧ (p4 ∨ p2))) ∧ (p5 → p1))))) ∨ (True ∨ (p5 → (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190134779946012990770796556087 : ((((p2 ∨ p5) ∧ (p1 ∧ (p2 ∨ (p4 → p5)))) ∧ p3) ∨ (p4 → (((p3 → p1) → (((p1 ∧ p4) → p3) → True)) ∨ (True ∨ (p2 ∨ p1))))) := by
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
theorem thm_5_vars_701361400911831579025020678218 : (((((((p5 → p5) ∧ True) ∧ p5) ∨ (p3 ∨ (p3 ∧ False))) ∧ (False ∨ ((p3 ∨ False) ∨ (((True ∧ p5) ∨ (p2 → (p2 → False))) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616867688661446598145427270788 : ((((((p5 ∧ (p1 → ((p2 ∧ (p2 ∧ p2)) ∨ p1))) → p3) → ((((p1 ∨ (p4 → p5)) ∧ p2) → (p1 ∨ False)) → (p5 ∨ p5))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_234718017891558979425598230623 : ((p4 → (p3 ∨ p2)) → ((((p1 → p3) ∨ ((True → ((p3 → (p3 ∧ False)) → ((True ∨ (p4 → (p1 ∨ p1))) ∧ p2))) ∧ True)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166808729244966674316504517170 : (((((p3 ∨ (False → False)) → ((p4 ∧ (True → p4)) ∧ ((p5 ∨ p2) ∧ False))) ∧ p1) ∧ p4) → (p3 ∧ (((p5 ∨ True) → (p3 ∨ p5)) ∧ True))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : (p3 ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h24 := h20 h22
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261042128149953561778736494333 : ((p4 → p2) → (((p3 → p2) ∨ p2) → (((((((p3 ∧ True) → p3) ∨ p2) → (p4 ∧ True)) ∨ p4) → p1) ∨ (p1 ∨ (p4 → (p4 → p4)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57493295970097388962636866935 : (((p2 → (True ∧ False)) ∨ ((((p1 → ((p2 ∧ (True → (p2 ∨ p5))) ∨ p2)) → (p4 ∧ ((True → True) → (False ∨ p2)))) ∨ False) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44609892987664909853986577169 : ((((p5 ∧ ((((True → p5) ∧ p1) → p3) ∨ p4)) → (((p5 ∨ ((False ∨ p4) ∧ (p4 → True))) ∧ True) ∧ ((False → p5) ∨ p1))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76741947654844056047313404195 : ((((((True ∨ (p5 → (p1 ∧ (p5 ∧ ((p2 ∧ p4) ∨ True))))) → p2) ∨ True) ∨ ((False ∨ ((p3 → True) → True)) → (True ∨ True))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ (p5 → (p1 ∧ (p5 ∧ ((p2 ∧ p4) ∨ True))))) → p2) ∨ True) ∨ ((False ∨ ((p3 → True) → True)) → (True ∨ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192573864545788558789169605949 : (((p5 ∨ ((p5 ∨ (False → (False → p4))) ∧ False)) ∨ p1) → (((p2 ∨ ((False ∧ (p4 ∨ p1)) ∧ (p5 ∧ p2))) ∧ (False ∧ p1)) ∨ (False → p3))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184275687437746770949571356690 : ((((p2 ∨ ((True → p3) ∧ (p5 ∧ p4))) → (False ∧ p5)) → p2) ∨ ((p4 → ((p1 → (p2 ∧ p1)) → p4)) ∧ (p4 ∨ (p1 → (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45720098875648049127314432295 : (((True → ((p2 ∧ (p3 ∨ (p2 ∧ p1))) ∧ (True → (p4 ∧ ((p5 ∨ (p2 → p2)) ∨ (((p3 ∨ (True → p1)) ∨ p2) ∧ p5)))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304915691960217012724573639398 : (p1 ∨ (((((((((False ∨ p3) ∨ p3) ∨ (p2 ∨ p3)) ∨ p2) ∧ (True → p5)) ∨ (p2 → (True ∧ p3))) ∨ True) ∨ True) ∧ (p4 ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215389359611578693045993284915 : ((p2 ∧ (p3 ∧ (p4 ∨ p3))) ∨ ((((p5 → (p5 → p4)) ∧ False) → (p2 ∧ p1)) → ((((p5 ∧ ((p2 → p5) ∨ True)) ∨ True) ∨ p2) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54410036871225012724313289103 : ((((p5 ∧ ((p5 ∨ p3) ∧ (False ∨ p4))) ∧ p4) ∨ (p2 → ((p4 → (True ∧ (False ∧ ((p3 ∨ False) → (p3 ∧ False))))) ∨ (True ∧ p2)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715071311151708438381117398273 : ((((p3 ∨ ((p3 ∧ (False → p5)) ∨ p3)) → (((p1 ∧ ((p4 ∧ ((False ∨ (p1 ∧ p1)) ∨ True)) ∧ p1)) ∨ ((p5 ∧ p2) → p1)) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169465019863358202138150104809 : ((((p5 → ((p5 ∨ (False ∨ False)) → p1)) → (p1 ∨ ((False ∧ True) ∨ True))) ∨ p5) ∧ ((((p1 ∨ p3) ∨ False) ∧ ((p1 ∨ False) ∧ p1)) → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47023445494011124562998021664 : ((((p5 ∨ (((p3 → False) ∧ ((True → True) ∨ (p3 → False))) ∨ (((((p2 ∧ p4) ∨ p2) ∧ p3) ∧ p3) ∧ p1))) → p5) ∨ (True ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68136465084913427260074954679 : ((p3 → ((((((False → False) → (((False ∧ p5) → p1) → p4)) ∧ (p3 ∨ ((False → (True ∨ (p1 → False))) ∧ True))) → p5) ∨ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192353688665160986780844715455 : (((False → (((False → p1) ∧ (False → True)) ∧ p5)) ∧ p2) → ((p5 → False) → ((((True ∧ (p5 ∨ p5)) → (p1 ∨ (p1 ∨ p4))) ∨ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208503325512475910346859026626 : (((p2 ∧ True) → (p2 ∨ (p2 ∨ p3))) → (p5 → (p3 ∨ ((p5 ∧ (False ∨ (((False ∨ p2) ∧ ((p5 ∨ p2) ∨ p3)) ∨ (p2 ∨ True)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54386550074166326635732295119 : (((p4 → (p5 ∧ ((True → False) → (True ∨ p4)))) ∧ (p1 ∨ ((((((p5 ∧ (False ∨ p4)) ∨ p1) ∧ p5) ∨ True) → (p3 → p2)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115356098843500145356082232484 : (((((((False → True) → p1) ∨ p5) ∧ p3) ∨ p2) ∧ ((True ∨ p3) ∨ ((p1 ∧ (p1 ∧ (((False → p4) → p2) ∧ p3))) ∨ p1))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184381955759946746325519625884 : (((False → (p4 → (((p5 ∧ p1) ∨ p2) → (p3 → True)))) → p1) ∨ (((p4 ∧ (p2 → p2)) ∧ (False ∧ (p3 → p1))) → (False ∨ (p5 ∧ p1)))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582134785199581893923314958287 : (((p4 → (p1 → (((p4 → p2) → (False → p5)) ∧ (((p3 ∨ p1) → ((p1 → (p3 ∧ (False ∧ (p4 → (False ∧ True))))) ∨ p4)) ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191333541836035410175561773499 : (((p4 ∧ False) ∨ ((p5 ∨ ((p1 ∧ p4) ∨ p4)) → p1)) ∨ (((p1 ∨ (((((p5 ∧ False) → p1) ∧ True) ∨ p5) → (p5 ∧ p1))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343216434435401605870603634028 : (p2 → (((p5 ∧ p5) → p1) → (((p4 ∧ (p2 → ((p4 ∧ ((((p5 → p5) ∧ (p1 ∨ True)) → p1) ∧ p5)) ∧ True))) ∨ (False ∨ True)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234822444265304080001528874840 : ((p5 → (p1 ∨ True)) → ((((True ∧ (p2 ∨ (False → (p4 ∨ (((False → ((p2 ∧ p1) ∨ p3)) → p5) ∧ (p3 → p3)))))) → p3) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56439699074915810502644319268 : ((((p1 ∧ p2) ∨ (p5 ∨ p1)) → ((p1 → (p4 ∨ ((p5 ∨ p5) ∨ (False → ((p5 → p3) ∧ (((p4 → p2) ∧ p1) ∧ p2)))))) ∨ p2)) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64651205550192014197041435411 : ((p1 ∨ (p5 ∧ (p4 ∧ (False ∨ (((p5 → p3) ∧ ((p5 ∨ (((p2 ∧ (p4 → p2)) ∨ (p1 → p3)) ∨ (p1 → True))) ∨ p5)) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783393338499768962979575897272 : (((p3 ∨ (((((False ∨ True) ∧ p2) ∧ (((True ∧ True) ∨ p1) → (p3 ∨ (True ∧ p5)))) ∨ p1) → (True ∧ ((True → (True ∧ p1)) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187129699247555714073313535005 : (((p1 ∨ p2) ∨ ((False → ((p2 ∨ (p2 ∨ True)) → p2)) ∧ p1)) → ((p3 ∧ True) ∨ ((((False ∧ False) ∨ p2) ∧ (p5 ∨ p2)) → (p4 ∨ p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h26
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h30
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303778037099007432453219152219 : (p1 ∨ (((p3 ∨ (p2 ∧ (((p3 → (p5 ∨ p2)) → ((p5 → (False ∧ (p5 ∨ (p5 → p5)))) ∨ (p2 ∨ p3))) ∨ (p1 ∨ p5)))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254469810609996878714190850604 : ((p3 ∧ True) → (((p5 ∨ (((p4 → p2) ∧ ((p5 ∨ (False ∧ p4)) ∨ False)) ∨ ((True ∨ p4) ∨ p4))) ∨ p5) ∨ (((p2 ∧ False) → p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_246709976933151695593818075076 : ((p5 ∧ p4) ∨ (((p4 ∧ False) → p1) → ((False ∨ (p2 → (((False → p4) ∧ ((True → p1) → False)) ∧ p2))) ∨ ((p4 → (p4 ∧ p3)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41485778528605582805887648515 : ((((p3 ∨ (p5 → ((p3 ∧ ((p2 ∨ p1) ∧ p5)) ∨ (p4 ∨ p5)))) ∨ (False ∨ (p5 ∧ (True ∧ ((True → (p4 ∧ p3)) → False))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246329876439388013299773471503 : ((p4 ∧ p5) ∨ ((((((p4 ∨ True) ∨ ((p5 → True) → p2)) ∧ p5) → (False ∧ p2)) ∧ (True → (p1 ∧ (True → p3)))) ∨ (True ∧ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265543961805286959913922188378 : (True ∧ (False ∨ ((p2 ∧ (p1 → True)) → ((True ∨ (False → p4)) → ((((p2 → ((p2 → p2) ∧ p2)) ∧ p4) ∧ p4) → ((p2 → p3) ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68218533789328770456357829141 : ((p3 → ((((((p5 → False) ∧ (p4 → (p3 ∨ p2))) → (((p4 ∨ p3) → ((p2 ∨ True) ∨ p5)) ∧ (p3 → p5))) ∨ p3) → p2) → p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 → False) ∧ (p4 → (p3 ∨ p2))) → (((p4 ∨ p3) → ((p2 ∨ True) ∨ p5)) ∧ (p3 → p5))) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229716494706285837801429540473 : ((p4 → (p2 ∧ p5)) ∨ (True → (((p2 ∨ (p2 → (((((True ∨ (False ∧ p2)) → p2) → (p4 ∧ True)) ∧ (p5 → p2)) → p1))) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241866988997154965958085371009 : ((p1 → p1) ∧ (p4 ∨ ((p4 ∧ (False ∨ (p2 ∧ p1))) ∨ ((False ∨ ((True ∨ ((True ∧ p2) ∧ (p1 ∧ (False ∧ (p5 → True))))) ∨ p2)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137005886515336046243570873825 : (((False ∨ p5) → (False ∧ (p2 → (True → (((False ∧ (False ∨ p4)) ∨ ((p3 ∧ False) ∨ (p1 ∨ p5))) ∨ (p4 ∧ p4)))))) ∨ ((False → p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60685181148669034943402837483 : ((True ∧ (((p4 ∨ (p1 ∨ p2)) ∧ (p3 → (p2 ∨ ((p5 ∧ True) ∧ True)))) ∧ (((True ∨ ((p1 ∨ (p5 ∨ False)) ∨ p1)) → True) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4467276434503792786503657718 : (p2 → (((((p3 ∨ ((p2 ∧ p2) ∧ (p1 ∨ p1))) ∨ (False ∧ ((p1 ∧ p1) ∧ p2))) ∨ p2) ∨ True) → ((p4 ∧ p1) ∨ (p1 → p1)))) := by
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
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h9.left
          let h12 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156645337212251235760556374608 : (((((((True ∨ (False → ((p3 → p5) ∧ (p3 ∧ p4)))) ∧ False) → (True ∨ p1)) ∨ p1) → False) ∧ True) ∨ (((p4 ∧ False) ∧ p1) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135017578047479920876301253502 : (((True → ((((p2 → ((p3 ∧ True) → False)) → ((p2 ∧ True) ∧ (False ∧ False))) ∧ p2) ∨ (p3 → p2))) ∧ (p5 ∧ p5)) ∨ ((True ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299261871053379331895045221470 : (False ∨ ((((((True → (True ∧ (p2 ∧ p5))) → (p5 ∨ True)) ∨ p4) → (p5 ∧ (p5 ∨ (False ∧ p5)))) → (p2 ∧ ((False ∧ p3) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620781445971178550106883578394 : (((((p5 ∧ p1) → (((True → ((p3 ∨ p3) ∨ (p2 ∧ False))) → (False ∧ (p3 → (p5 ∧ ((p5 → (True → p5)) → p2))))) ∨ p1)) ∨ False) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168323668197669051009258079270 : (((p2 → p2) ∧ ((p2 → p1) ∨ ((p2 ∨ (False ∧ (p5 ∨ (p5 → (p3 ∧ p4))))) ∨ p5))) → ((p3 ∨ (True ∨ ((p5 ∧ p4) ∧ False))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806663951922099675173147909230 : (((p4 → ((True → ((p2 → ((((p5 ∧ ((p4 → p5) → (p2 ∧ (p5 ∧ (p5 ∧ True))))) ∨ False) ∨ p3) → (True → False))) ∧ False)) → False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354882803558644011319869896618 : (p5 → ((p2 ∧ ((((False ∨ (((((True ∧ p2) ∨ False) → p3) ∧ p4) ∨ (p5 ∨ (p5 ∨ p4)))) ∧ (p3 → p5)) → (True ∧ True)) → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53771742343639505829470589679 : (((((((p5 ∨ False) ∨ (p1 → True)) → p2) → p4) ∨ p1) ∨ ((((((((p3 ∨ False) → False) → p1) ∧ p2) ∨ p2) ∧ False) ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57098716719417768518381125917 : ((((p5 ∧ p3) ∧ p1) ∨ (((p1 ∨ ((((p5 → False) ∧ (True ∧ p2)) → (p5 ∧ p1)) ∧ (p3 ∧ True))) ∧ (p3 ∧ p5)) ∧ (p3 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599696533374512699085493606780 : (((((p2 → p1) ∨ (False ∨ (p1 ∧ ((((p3 ∨ ((p5 ∨ True) ∨ False)) → ((p4 → p2) ∨ p4)) ∧ p1) ∨ (p4 → (p1 ∨ False)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350265260324602556275728928304 : (p4 → ((p3 ∧ (((((p3 ∨ p1) ∧ ((p1 ∨ p5) ∨ (((p3 ∨ p2) → ((p3 ∨ p3) ∨ (p1 → p1))) → p5))) → False) ∨ p2) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256203886276366634485997847541 : ((False ∨ True) → (p3 → (((True ∨ False) ∧ ((p3 ∨ p2) → (((p5 ∨ False) ∨ (p4 → (p2 ∨ p5))) → p5))) ∨ ((True ∨ p5) → (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40675197502057631350226713829 : (((((p1 ∨ ((p2 ∧ p2) ∨ (True → ((p5 ∧ p3) → (p5 ∧ ((p2 ∨ True) ∧ (p2 ∨ False))))))) ∧ ((p5 → True) → p3)) → p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113503894155658948390321166790 : ((((True ∧ (False ∨ (p5 ∨ ((p1 → True) ∧ (((p4 ∧ False) ∨ p4) ∧ p5))))) ∧ ((False ∧ p4) ∨ (p5 → p4))) ∨ (True ∨ True)) ∨ (p5 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179374694089319215552909817386 : ((p2 ∨ (p1 ∨ (((p2 ∨ p4) ∨ (p5 ∨ (True → (p5 ∧ p3)))) ∧ p1))) ∨ ((p5 → ((((p1 ∧ False) → p3) ∧ p4) ∨ (True ∧ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231515567568441329498378263219 : (((p4 → False) ∨ p5) → ((p2 → ((((p3 ∧ (p2 ∧ True)) → False) ∨ p1) ∧ False)) ∨ (((True ∨ p4) ∨ ((p3 ∨ True) ∨ p4)) ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_260524991890665162601250199127 : ((p3 → p1) → (((((p4 → ((((p1 ∧ False) → False) ∧ p4) ∨ ((p5 ∨ ((False ∨ p5) → p1)) ∧ p5))) ∧ p2) → p3) ∧ (True ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805955159860775954576512811251 : (((p4 → ((((((p2 ∨ False) ∧ (p1 ∨ ((((p2 ∨ (p1 → p5)) ∨ True) ∧ p3) ∨ (p4 → p1)))) ∧ p5) ∨ p5) → (p2 ∧ p3)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601759640579565532370555050487 : ((((p4 ∧ ((((p4 ∧ (p2 → p3)) → (((((p4 → p2) ∧ (p2 ∨ p5)) → ((p2 ∧ False) → False)) ∧ p1) ∨ p3)) ∧ p4) → p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133846065556884209604062308097 : (((True ∧ ((p2 ∨ p5) ∧ (((((p3 → p1) ∧ p5) ∧ (p1 ∨ False)) → p2) → ((p3 ∨ (p1 → p3)) → p1)))) ∧ p5) ∨ ((p4 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151236751873154280472222989941 : ((((False ∨ False) ∧ (((p5 ∨ True) ∧ False) ∨ (((False ∨ (p5 ∧ True)) ∧ p1) ∨ ((p3 ∨ p4) → p4)))) → True) → ((p3 → (p5 ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54659266675985825140913843792 : (((((p4 ∨ p5) → (p2 ∨ (p1 → p2))) ∨ p4) → (p3 ∨ (((p3 ∧ p3) ∧ p3) ∨ (((p4 ∧ p1) ∨ (p4 → False)) → (True ∨ p1))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246451925628816849832179422203 : ((p5 ∧ False) ∨ (((p4 ∨ (p2 ∧ ((True ∨ (p4 ∧ ((p4 → p2) ∧ (p4 → p1)))) → ((p2 ∨ False) ∨ p2)))) ∧ p1) → ((p5 ∧ p5) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808946376167376602587082017661 : (((p5 → (((((((p5 ∧ p4) → p5) → True) → ((((p2 → (False ∧ p2)) ∨ p3) → p5) → True)) ∨ False) → (p1 ∧ (p3 ∧ p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156605422471814494084874017982 : ((((((p3 → (p4 ∨ p5)) ∨ p1) → (p2 ∧ (((p2 ∧ p1) ∧ p5) ∨ (p1 ∧ False)))) ∧ False) ∧ p2) ∨ (p2 → ((True → p5) → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27478177941581780009462991300 : (((p3 ∧ p4) → (((((True ∧ p3) ∨ False) → ((p5 ∧ ((p3 ∨ False) ∧ (((p2 ∧ (p2 ∧ p3)) ∨ True) ∨ False))) ∨ p1)) ∧ p2) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654756927815386452987579516 : (((True ∧ ((p4 ∨ ((False → p4) ∨ p4)) ∨ (p3 → ((p4 → p3) ∧ ((True ∧ (p2 ∧ p2)) ∨ p2))))) → (p4 → (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168121148519689737510424014339 : (((((False ∨ True) ∧ False) ∨ p4) → ((((False → False) ∧ ((p4 ∧ p1) → p5)) → p4) ∧ p4)) → ((False ∨ (True → ((p5 ∧ p1) ∧ False))) → p1)) := by
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
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40053307037142026007895330933 : (((((((p5 → (False ∨ ((True → (True ∧ p3)) ∨ (p1 ∧ (p1 → p2))))) ∨ (((p4 ∨ False) ∨ True) ∧ False)) → p4) ∨ True) ∧ p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208876699230686749142155284876 : ((p4 ∧ (True ∧ ((p2 → p5) ∨ p3))) → ((True → ((p4 ∧ p2) ∧ p2)) → (((p4 ∧ ((p5 → p5) → False)) ∨ True) ∨ ((p1 ∨ p1) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
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
theorem thm_5_vars_315473027439402459938669002101 : (p3 ∨ (((p3 → True) ∨ p5) → ((p5 ∧ p2) ∨ (((((False ∨ p5) ∨ True) → False) ∧ (p5 ∨ (p3 ∨ (False ∧ (p4 ∧ p5))))) → (p3 → p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((False ∨ p5) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : ((False ∨ p5) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h23 : ((False ∨ p5) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h24 := h20 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h27 : ((False ∨ p5) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h28 := h20 h27
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41210665104211322996144541603 : ((((((((p2 ∧ False) ∧ (p4 ∨ ((p2 → False) ∧ p2))) ∨ (p4 ∨ (p5 ∨ p2))) ∧ False) ∧ p4) ∧ ((p2 ∧ p1) → (True ∧ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58975115674965571402810116557 : (((p2 ∧ p4) ∨ ((((p4 ∧ (((p5 ∨ p1) ∨ ((p2 → False) ∧ p3)) ∧ ((p5 ∧ p5) ∧ p5))) → p3) → False) ∨ ((False ∨ False) → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590120414103753617718398749362 : (((((((((p5 ∧ True) → True) → (p2 → p1)) → (p5 ∧ p3)) → (p3 ∧ ((p3 ∧ p3) ∧ ((p2 ∨ (p3 ∧ p5)) → p5)))) → p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40770795024009734490203086991 : (((((p5 → True) → (((((p1 → ((p1 ∨ (p5 ∨ (p4 → False))) ∨ p2)) ∧ (p3 ∧ p1)) → True) ∧ p1) ∨ (True → True))) → p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689602554260047552080704402935 : (((((((p5 ∧ p5) → True) → (p1 ∧ p2)) ∨ (p3 → (((p1 ∧ p2) → False) → p3))) ∨ (p3 ∨ (p2 ∨ ((p1 → False) → (p1 → p3))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69077706096181280231989474287 : ((p5 → (((((((p3 → p1) ∧ p5) ∨ False) ∧ ((p3 ∧ p3) ∧ (p4 → (p4 ∧ p3)))) ∨ p5) → (p4 ∨ ((p4 ∨ p4) ∧ p4))) → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p3 → p1) ∧ p5) ∨ False) ∧ ((p3 ∧ p3) ∧ (p4 → (p4 ∧ p3)))) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148392009313613404918158093288 : ((((p2 → True) → ((p1 ∨ p1) → (((p1 ∧ p1) → (p4 ∧ False)) → p3))) ∨ (True ∧ ((p5 → p3) ∧ False))) ∨ ((p3 ∨ (p5 ∧ p5)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149557229128153572165616116934 : ((p2 ∧ ((((p2 → p5) ∨ p3) ∨ p2) ∧ ((((((p4 → True) ∨ p1) ∧ p3) → p5) ∧ p3) ∧ (p5 ∧ p5)))) ∨ (((p2 → p2) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90920368235334306837264193274 : (((True → False) ∧ (((p4 ∨ (p1 → p5)) ∨ (p4 ∨ ((p3 ∧ (((p5 ∨ p2) → True) → p5)) ∧ (True → p1)))) ∨ ((p4 ∧ False) ∨ p4))) → p1) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h21
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h29 := h2 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56586388009018558801103359975 : (((p1 → (p4 → (p5 ∨ p1))) → ((p4 → p5) ∨ (((p4 ∧ ((((p1 ∧ p4) ∨ p5) ∨ False) ∧ p2)) ∨ ((p4 → p2) → p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678261185654763540883993417660 : (((((((False ∨ p1) ∧ ((p4 ∧ p2) → False)) → p4) ∧ ((p1 ∨ True) → ((False ∨ True) → (p5 → False)))) ∨ (((False → False) ∨ p5) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214700798614739688753930152312 : (((False ∧ False) ∨ (p4 ∧ p4)) ∨ ((p3 ∧ ((((p2 ∧ (p1 → (p5 → (p5 ∧ (False ∨ p1))))) ∧ (False ∨ p1)) → p4) ∧ p4)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134940204701391994165040447320 : ((((((p4 ∧ p1) ∧ (((True ∨ p3) ∧ p4) ∧ (p5 ∨ ((p5 → p4) → False)))) ∨ p5) ∨ (p1 ∨ p1)) ∧ (p1 ∨ p2)) ∨ ((True → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53630315836698359863104156912 : (((((p1 ∧ False) ∧ (p4 ∨ p5)) ∨ ((p1 ∧ p4) → p5)) ∧ (((((p5 ∧ (p2 → True)) ∨ p4) ∨ ((p2 ∧ p1) ∧ True)) → p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178790804964105478900458721537 : ((((p5 ∧ p1) ∧ True) ∨ ((False ∨ (p4 → ((p5 ∧ p2) ∨ True))) ∨ p3)) ∨ ((p3 → True) → (((p5 ∨ (False ∧ True)) ∨ True) → (p4 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303187874290786305788031619196 : (False ∨ (p4 → ((True ∨ (((p1 ∨ (p4 ∧ p3)) → p2) ∨ (False → (p4 ∨ p2)))) → (p1 → (((((False → p1) ∧ False) ∨ p5) ∨ p4) ∧ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714132346608161735743966996841 : (((((p4 ∧ ((p1 ∧ False) ∧ p5)) → True) → (((((p1 → (p1 ∨ True)) ∨ (p5 → ((p1 ∧ False) → (p1 ∧ p3)))) → p3) ∨ True) ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60316123838759114002619678127 : (((p1 → p4) → (p2 ∨ (((p1 ∧ ((False ∨ p1) ∨ True)) → ((((p5 → p2) → (False ∨ True)) ∧ p1) ∧ p5)) → ((p2 ∨ True) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43559984662448771206672191895 : (((((((((p1 ∨ p2) → ((p2 ∨ p3) → (False ∧ p5))) → p2) → False) ∧ (p1 → (p4 ∨ ((p4 ∧ p4) → True)))) ∧ True) → p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



