variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184125701734098446265474563818 : (((False ∧ ((p1 → ((p4 ∨ p3) ∨ True)) → (p4 → p3))) ∨ p5) ∨ ((p1 ∧ (True ∧ p4)) → ((False → p4) ∨ ((p5 → True) → (p4 → p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49500167800886481068354980988 : ((((p4 ∧ ((((((p5 → p3) → p2) ∨ ((True ∨ p4) ∨ True)) → ((p4 → p3) ∧ False)) → p1) ∨ False)) → p5) → ((p2 → p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53635627377872403892419043198 : (((((p1 ∧ p3) ∧ (p3 → p1)) → (True ∧ (False ∨ p2))) ∧ ((((p2 ∧ p3) → p1) → ((p3 → (p3 ∨ (True ∧ True))) ∨ p3)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590201081381392224064641026994 : (((((((False ∨ (p3 → True)) ∨ (p5 ∧ p1)) ∨ ((((p5 ∧ ((False → p5) → False)) ∧ (p1 → p4)) → (p1 ∨ p4)) ∨ p5)) → p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308725620363902943537720075867 : (p2 ∨ ((p1 → (((p2 ∨ p4) → (((p3 ∧ False) ∨ ((p2 ∧ ((p4 → False) → p3)) ∨ False)) ∧ ((p3 ∧ p5) ∧ (p2 → p5)))) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609588876452030698751276622167 : (((((p5 ∧ ((p5 ∧ (((p4 → p4) ∨ (p4 → (True ∧ p4))) → ((p5 ∧ (p4 ∧ p3)) ∨ ((p2 → True) ∨ p2)))) ∧ False)) ∨ False) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_975839045749981665114893045932 : ((((p5 → p5) → ((p1 ∨ p1) ∧ ((((True ∨ p1) → ((p1 ∧ p3) ∧ p5)) ∧ False) ∧ ((p3 ∧ (p2 ∨ ((p4 ∧ True) → True))) ∧ p4)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60187430095381526085889289734 : (((p5 ∨ p2) → (p3 → (True → ((((True → ((p2 ∨ p3) → False)) ∨ True) → p5) → ((p3 ∧ (False ∨ False)) ∨ ((p1 ∨ True) ∨ p5)))))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38727081467023158206078819010 : (((((p4 ∧ p4) ∧ (p5 ∨ (p5 ∧ p5))) → (p2 ∨ (((p3 ∧ p4) → p2) ∧ ((((p3 ∨ p2) ∨ True) → (p2 ∧ p2)) ∨ p4)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209501095593957482019533027787 : ((p3 → (p4 → ((p5 ∨ p3) → p1))) → ((((p3 ∧ p5) ∨ ((p1 ∧ p3) → ((p3 → True) → p4))) ∨ (((p1 ∧ p1) ∧ p3) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232294701208872192474129861612 : (((p3 → True) → p2) → (((p5 → (((p4 ∨ ((False → p1) → p4)) ∧ p4) → (p3 ∨ (p2 ∨ p5)))) ∧ p3) ∨ (((p4 → p1) ∨ p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42516116615718860264293064600 : (((False ∨ (p2 ∧ (p5 ∨ (p4 ∨ (p2 → ((p4 ∧ False) → (False ∧ (((p1 ∧ ((True ∨ p4) ∧ p1)) ∨ (False → p1)) ∧ False)))))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197452828670932652918715430886 : ((((True → (p2 ∨ p5)) ∨ p5) ∧ (p1 → p5)) ∨ ((((p3 → (p5 ∨ True)) → False) → p3) ∨ ((True ∨ (p2 ∨ (p4 → p5))) ∧ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217645055709566815652311123134 : ((((p5 ∧ p5) → p4) → p3) → (((True ∨ True) → (False ∧ p2)) → ((((p4 → p2) ∧ (True ∨ p5)) ∨ p4) → (p4 ∧ ((p4 ∧ p5) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200204561962132993514283877990 : (((False → (p2 ∨ True)) ∨ ((p5 ∧ p4) ∨ True)) → ((((((p3 ∨ True) → p4) ∨ False) → False) ∧ (p3 → (((p2 ∨ p5) ∧ True) → p1))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_351732756227260348863476714609 : (p4 → ((((p2 ∧ (p5 ∧ False)) ∨ p1) ∨ (True → (p3 ∧ ((True → p1) ∧ p2)))) ∨ (True → (True ∨ (((p1 → (p5 → p2)) ∨ False) ∧ False))))) := by
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
theorem thm_5_vars_40673662988535448646558233982 : ((((((True ∨ (((p4 ∧ (p4 ∨ p1)) → p1) ∧ False)) ∧ (p1 ∨ (((p2 ∨ True) ∨ p3) ∧ p4))) ∧ (p1 → (p2 ∧ True))) → p3) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105457173526356125336721417671 : (((((p5 → (p5 ∨ p5)) ∧ (((p2 → (False ∧ p2)) → (p5 ∧ p1)) ∧ p1)) ∧ (p1 → p1)) ∨ ((True → p3) ∨ (p3 → True))) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58092118851082829698989787522 : (((p1 ∧ p1) ∧ (((p1 → (True ∨ (p2 ∧ p1))) ∨ ((((p4 ∧ p5) ∨ False) ∧ p1) ∨ (p4 ∨ (p1 ∧ (p4 ∧ p5))))) → (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172715046953795020838066495561 : (((p4 ∨ False) ∨ (((((True → p3) → p4) ∨ p5) ∨ (False ∨ p4)) ∨ (p1 → True))) ∨ (True → ((False ∧ (p4 ∨ p5)) → (p4 ∧ (p5 ∧ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234259822306674536604131620708 : ((False → (p5 ∨ p5)) → ((p4 → p4) → ((p1 → (((p2 ∧ (p3 ∧ p4)) ∧ (((True ∨ ((True ∧ True) ∨ p5)) ∧ p4) ∨ False)) ∨ p1)) ∨ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22117891505539003191120167225 : (((((True → (False → p5)) → p3) ∨ (p3 ∧ p3)) ∨ ((((p1 → (False ∧ False)) ∨ p2) ∧ False) ∨ (p3 ∨ ((p3 ∧ (p2 ∨ p2)) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87412555787150665808654707049 : (((False ∨ ((p5 ∨ p2) ∧ (p3 → True))) ∧ (True → ((False → (((((p3 ∨ True) ∨ p5) → p5) ∨ (p4 ∧ (False → p3))) → p3)) ∧ False))) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790278343164535033471728192155 : (((p5 ∨ (p2 ∧ ((p4 ∧ ((((p2 ∧ (((p1 → p1) ∨ (True ∨ True)) ∨ (((False ∨ p3) ∧ p2) ∨ p2))) ∧ p5) ∨ p4) ∨ p1)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51295262185357586411584314551 : (((p5 ∧ (True → ((p2 ∨ p2) ∧ ((False → (((True → (p1 → p5)) → p3) ∧ False)) → False)))) ∨ ((False → (False ∨ p4)) → (True ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117082882472819559365282326761 : (((False → p2) → ((p3 ∨ (False ∧ p1)) ∨ ((p1 → (p2 → (((p2 → p4) ∧ (p4 → p2)) ∨ ((p3 → False) ∨ p3)))) ∨ p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300595553199373043974459518015 : (False ∨ ((((((True ∨ (p1 ∧ (p2 → p3))) → ((False ∨ p2) ∨ False)) → p4) → False) ∨ ((p3 ∨ p2) ∧ p4)) → (((p3 ∨ p2) ∧ True) ∨ True))) := by
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
theorem thm_5_vars_461406034068750061877080616226 : (((((((p1 ∧ (p3 ∨ (p5 ∧ True))) ∨ False) ∧ p4) ∨ ((True → (False ∨ p3)) ∨ True)) ∧ (p2 ∨ ((p3 → False) → ((True ∨ p4) ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111159963787782572706643967870 : ((((p3 ∨ ((p3 ∨ p2) ∨ (False → p3))) → (p2 ∧ (p5 → ((((p5 ∨ False) ∨ True) ∧ p1) → (p3 → (False ∧ p4)))))) ∧ p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259952786939285608338643333234 : ((p1 → p5) → ((True ∧ p2) → (((p5 ∧ ((p4 → p5) → ((True → p1) ∧ ((((p1 ∨ p4) → p2) ∨ (p1 ∨ p1)) ∨ False)))) ∧ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50861690224154917880032821316 : ((((((False ∧ False) ∧ (False ∧ p5)) ∨ ((p3 ∧ (p4 ∧ (p5 → p5))) → (True ∧ p2))) ∨ True) ∧ (((p2 ∧ p5) ∨ p3) ∨ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262257412838231207437273330776 : (True ∧ ((((((p5 ∧ p2) ∨ p5) ∧ (False → p3)) ∨ (p2 → (((((p2 ∨ p3) ∨ p4) → p1) ∨ True) → p3))) ∨ ((False ∨ p3) ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171892632053970513244095441290 : (((p3 ∨ ((p4 ∨ (True ∧ ((((p5 ∧ p5) ∨ p3) → p4) ∧ True))) ∧ True)) → False) ∨ ((p2 ∨ p1) → (False → ((p5 → (True ∨ p4)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804546946920571885284642772916 : (((p3 → ((False ∧ (p2 ∨ (p3 ∧ (p3 ∨ False)))) ∨ (False ∨ (True → (((p1 → p3) → ((p3 ∧ ((p4 → False) ∧ p5)) ∨ p5)) ∨ True))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261285515089248330651978067759 : ((p5 → True) → ((True → (p4 ∧ p2)) → ((p1 ∨ p5) ∨ (p3 → (((p2 ∨ True) ∧ (True ∨ ((False → (True → True)) ∧ (p5 ∧ p5)))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349286462813728897739010147063 : (p3 → (p2 → ((p5 ∨ ((p5 ∧ ((p2 ∧ ((p5 ∨ ((False ∨ (p1 ∧ True)) ∨ (p2 ∨ True))) ∧ p1)) → False)) ∧ (p4 → True))) ∨ (p2 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300402918784768984876305689528 : (False ∨ ((p3 ∧ (((False ∧ (((((p4 ∨ p5) ∧ p2) ∧ (p5 ∨ p1)) → p5) → False)) → (p2 ∧ (p2 → p2))) → False)) ∨ (p4 → (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67548945730775331655832535522 : ((p1 → ((p2 → (p5 ∨ p3)) ∨ (p3 ∧ (p4 ∨ (((p2 ∨ p4) → (p5 → (((False → p1) ∨ (p2 ∨ (p2 ∧ False))) ∧ True))) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160942655458566934517964064634 : ((((True ∨ p1) ∧ p1) ∧ ((p3 ∧ (p4 → p5)) ∧ (p2 ∧ ((True ∨ (p4 ∨ p2)) ∨ (p4 ∧ False))))) → (((True → (p4 ∧ p5)) ∨ p1) ∨ p2)) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h23.left
    let h27 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642964892548405861766057439035 : ((((p2 ∧ ((((False ∧ True) ∨ True) ∨ (p1 → p1)) ∧ (((((p5 ∧ p5) ∨ ((p2 ∨ False) ∧ (p5 → p1))) ∧ p1) → p2) ∨ p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57103264695138745280199866850 : ((((True ∨ p4) ∧ p5) ∨ (p2 → (((p1 ∧ True) ∨ ((((p2 ∧ ((p5 ∧ True) ∧ p2)) ∧ (p3 → p2)) → True) ∨ True)) → (p2 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156807680580343370653901176681 : (((False ∨ ((((((p4 ∧ p3) → p5) → (p1 ∨ p5)) ∨ True) → p3) ∨ (p4 ∨ (False → p5)))) ∧ True) ∨ ((p2 → p2) ∧ (p3 ∧ (p5 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617199900778065148468344035609 : (((((((p1 ∨ p1) → p4) ∧ ((p4 ∧ p4) ∧ p1)) ∨ (((p2 → (p4 ∨ (p2 ∨ True))) → (True → False)) ∨ ((p3 ∧ False) → p5))) ∨ p3) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51560857014560084208105278915 : (((False ∨ (((p2 ∨ ((False ∨ ((False ∧ (False → p2)) ∧ (p1 → p5))) → p2)) ∧ p1) ∧ p2)) → (p4 → ((p4 ∧ (p5 → p3)) ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118582692099465383166522065095 : ((p4 ∨ (((((p4 → (p4 ∨ (((p3 ∧ p4) → p2) ∧ (p5 ∨ p5)))) ∨ (p3 ∧ (False ∨ p2))) ∧ (True ∨ p5)) ∧ p4) → p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215905952043654529188596756831 : ((p3 ∨ ((p3 ∨ True) → p4)) ∨ (p1 → (p2 ∨ ((p2 ∧ ((False → True) ∧ ((p1 ∧ ((p3 ∧ p5) ∧ False)) ∨ False))) ∨ (False → (p5 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157504601347203019915884685771 : ((((p3 ∨ p4) → ((p4 ∨ p3) ∧ (((p4 ∨ p5) → (False ∨ p1)) ∧ (p3 ∨ p3)))) ∨ (p4 ∨ p3)) ∨ ((p5 → (p5 ∨ p5)) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349215515997403634204438331310 : (p3 → (p1 → (((p1 → False) → (True ∧ (((p3 ∧ ((p1 ∧ p4) ∧ p2)) ∨ ((p3 → ((p3 ∨ (p2 ∨ p4)) → False)) ∧ p4)) ∧ p4))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37700324132960255978592083416 : (((((((p4 ∨ (p4 ∨ False)) ∧ ((p5 ∧ (p3 ∧ ((p3 ∨ False) ∨ True))) ∨ (p2 ∨ True))) ∧ p2) ∨ ((p2 ∨ p2) ∧ p3)) → False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685422399699420735784969566337 : (((((((((((((p1 ∨ p1) ∧ p4) ∨ False) ∨ p4) → p5) ∧ False) ∧ p3) ∨ p1) → p2) ∧ True) → ((True → (p1 ∨ p3)) ∨ (p1 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48085262313134817431938358340 : ((((((p1 → (True ∨ p5)) ∧ p1) ∨ p5) → ((p2 → (((False ∨ ((p3 ∨ (p1 → p1)) → p4)) → p4) ∧ p4)) ∨ p3)) → (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68774210574630722816912089772 : ((p4 → (((p2 ∧ (p1 ∧ p2)) ∨ (False ∨ (p2 ∧ (True ∨ p4)))) ∨ ((False → (p4 ∧ False)) ∨ (((p3 → p1) ∧ (p4 → p3)) ∨ p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161425456868085497715473309249 : ((p2 ∧ ((((p5 ∧ p5) ∧ (p2 ∧ (p4 ∧ p1))) → ((False ∨ False) ∧ (True ∨ p2))) ∨ (p4 ∨ p4))) → (((p4 → p4) → (p3 ∧ False)) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p4 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p4 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h17
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317896594256666589334145973487 : (p4 ∨ ((p1 ∧ (p4 ∨ (p5 → (((False ∨ (p4 ∨ (False → ((p5 → p4) ∨ p5)))) → (((p4 ∨ False) → (False ∧ p2)) ∧ p4)) ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40254766976990840279093558126 : ((((p1 ∨ (((False ∨ (p4 ∨ (p5 ∨ (p2 ∧ ((p1 ∧ p4) ∨ p2))))) → p1) ∧ ((p1 ∧ p2) ∨ (False ∧ (True → p3))))) ∧ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159921972933600775204953528097 : (((((p4 ∨ (((((True ∨ p2) ∨ (p4 ∧ p4)) ∧ p4) ∧ p1) → p5)) → (p4 → False)) → p2) → p4) → (p2 → ((True → p5) ∨ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∨ (((((True ∨ p2) ∨ (p4 ∧ p4)) ∧ p4) ∧ p1) → p5)) → (p4 → False)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806408818639490299523745907347 : (((p4 → ((p4 → ((p3 ∧ p1) ∧ (p2 ∧ (((p4 ∧ p2) ∨ (False → p2)) → ((True ∨ p1) ∧ ((p4 ∧ p5) ∧ (False ∨ p5))))))) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62745999078166129994564288055 : ((p4 ∧ (((((p5 ∧ p4) ∧ ((p5 → (p4 → (False ∨ ((True ∨ True) ∨ p5)))) ∧ (p4 → p5))) ∨ (p2 → True)) ∧ True) → (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148440433796587519897010735877 : (((True → (False ∨ ((((p5 ∧ p1) → False) ∧ p2) ∧ (p2 → (True ∧ p5))))) → (p1 ∨ ((p5 ∨ p4) → p3))) ∨ (p4 ∨ (p2 → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45921275355188727233389489378 : (((p4 → ((p3 ∨ True) ∨ (True ∨ (((p3 → (p1 ∧ ((p1 → (p4 ∧ p5)) → p4))) ∧ p4) → (((p1 ∧ p3) ∨ p4) ∧ p2))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209398710057742323552753844797 : ((p1 → (p1 ∨ ((True ∨ False) → p5))) → (((p4 ∨ ((False ∨ p3) ∨ False)) ∧ p1) ∨ (True ∧ (True ∨ (p5 → (True ∨ (p5 ∨ (False ∨ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_149925477767527500650830715061 : ((p3 ∨ (((p5 → (((False ∨ p5) ∨ ((True ∨ p1) → True)) ∧ p4)) ∧ False) ∨ (((p2 ∧ p3) ∧ p5) ∨ p3))) ∨ (False → ((True → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62461193861566452856504937749 : ((p3 ∧ ((p4 ∨ p5) ∧ (p5 ∨ (p5 ∨ (False → (p1 → (((True ∨ p2) → p4) → (p2 → (((p2 → p4) → (p4 → p4)) ∨ True))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347537256093926111780412869306 : (p3 → ((True → ((p3 ∧ p1) ∨ (False ∧ p3))) → (((p5 ∧ ((p4 → p4) → (p2 ∨ (((p3 → p5) ∧ True) ∨ p4)))) ∨ (p1 → True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763751345489708341959662402836 : (((p3 ∧ (p1 ∨ ((((p2 ∧ p2) ∧ (p4 ∧ p4)) ∨ p1) ∨ ((((True ∧ ((p3 ∨ p4) → (p5 ∧ p1))) ∨ p1) ∧ True) ∧ (p1 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329640086479235988119300199269 : (True → ((p1 ∧ p5) → (((((False → True) → (((True → ((p3 ∧ True) → (p1 ∨ False))) ∨ False) → p5)) → (True ∨ (False → p1))) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205209752061896753250423059758 : (((p4 → (p1 → p3)) ∧ (False ∨ p5)) ∨ (((((False ∧ (p5 ∨ ((p2 → p3) → p3))) → p1) → p2) ∧ (p2 ∨ (True ∧ (False ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159697146276861784432040861294 : ((((p2 ∨ ((((((p3 ∨ False) ∨ p1) → True) → (True → True)) ∨ False) ∨ p3)) → (p2 → True)) ∨ p5) → (((True → False) ∧ (False ∨ p1)) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230681033442096145193383094305 : (((p4 → True) ∧ p2) → ((p2 → (p2 → p5)) ∨ (((p3 → False) ∧ p1) ∨ ((True ∨ p5) ∨ ((((False → p4) ∧ (p3 ∨ p1)) ∨ p3) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_133817854725641520044449507233 : ((((False ∧ False) ∨ ((p1 ∨ (False ∨ p4)) → ((p2 → p2) → (p4 → (p4 ∧ ((False ∧ False) ∧ (p5 ∧ False))))))) ∧ p1) ∨ (p4 → (True ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165798128388565069355144770744 : ((((p1 → p2) ∧ False) ∧ (True ∧ (((p5 ∧ p3) ∨ True) ∨ ((p2 → p2) ∨ (p5 → True))))) ∨ (((p5 ∨ p4) ∨ (p4 ∧ p3)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168184150069460224946831595206 : (((p2 → (p4 ∧ p3)) ∧ (((p2 → p1) ∨ (p5 → (True ∨ (p2 ∨ p3)))) → (p3 ∨ True))) → (p1 ∨ (((p3 ∨ (p3 ∨ p4)) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597693097660451233526161066823 : ((((((p1 ∧ p1) → (p5 → p1)) → ((((((p2 ∨ p2) ∨ ((p4 → p1) ∨ p1)) ∧ True) ∧ (False → False)) → (p4 → p5)) → p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64318007265332334210274300135 : ((p1 ∨ (((p5 → ((((((p4 ∧ p5) → p1) → p4) ∨ (((False → p3) ∨ (p3 → p1)) → p3)) ∨ p2) → p4)) ∧ (p4 → p1)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187345018841715898037623298169 : ((p2 ∧ (p1 ∧ (p3 ∧ (p4 ∨ ((p4 → (False → p3)) ∨ p5))))) → (p3 → (((p1 → p2) ∧ (False ∧ (p2 ∧ ((p4 → False) ∧ p4)))) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49042893923159953305636587893 : ((((True → (((p1 ∧ p1) ∨ p5) ∨ (p4 ∧ ((p2 → p3) ∨ (((p5 ∧ (p3 ∨ p5)) → p5) ∨ p5))))) → p1) ∨ ((False → p5) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68630287388861271895239543355 : ((p4 → ((p2 ∨ (((p5 → (p3 ∨ p4)) → False) ∨ ((((True ∨ (p5 ∧ p4)) ∧ (p2 ∧ False)) → p5) ∨ ((False → p4) → p2)))) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136441869726911690959074124120 : ((((p2 → False) → (p5 ∨ True)) → ((p2 ∨ (((True ∧ p4) → p4) ∨ (True ∨ p5))) ∧ (p1 ∧ (p2 ∧ (p2 ∨ p4))))) ∨ (True ∨ (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339978800185680606925976630573 : (p1 → (p1 → (((((p2 ∧ (((((p4 → p3) ∨ False) → p4) ∨ p4) ∧ p5)) → (p3 ∧ p4)) ∧ p3) ∧ ((p5 ∧ p1) ∧ True)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_116535742448542614588032816300 : (((True ∨ p5) ∧ (((p1 ∨ ((((p3 ∨ p3) ∨ ((p1 ∨ p4) → (p3 ∨ (False ∨ (True ∧ p1))))) ∧ True) ∨ p1)) ∨ False) ∨ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137451411175449703926103526304 : ((p4 ∧ ((False → (False ∨ True)) ∧ (p2 ∧ (p4 ∧ (((p3 ∨ (p3 ∨ p3)) → ((p1 ∨ (True → p2)) ∨ False)) → p1))))) ∨ (False → (False ∧ False))) := by
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
theorem thm_5_vars_199904651304678580208463965064 : (((((p2 → p2) ∧ p3) → p2) ∨ (p1 ∨ p3)) → (((p2 ∨ ((p4 ∧ p1) → p1)) → (((p2 ∧ ((True ∧ p5) ∨ False)) ∨ False) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43818768985077497681482655079 : ((((p4 → (((p2 ∨ (False → p1)) ∧ p4) ∨ (p5 → ((((False ∨ p2) ∨ (p3 ∧ p1)) → (True → p3)) ∨ (p4 ∧ p5))))) → True) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209032020252398854977386909469 : ((False ∨ (p2 → ((False ∧ False) → p1))) → (p2 → (False ∨ ((p1 → ((((p3 → p1) ∨ p4) → p3) ∨ ((True → (p2 → p1)) ∧ p1))) ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306068483884473125293736172430 : (p1 ∨ ((True → (p5 ∧ (p2 ∧ p3))) → ((((p4 ∧ (p3 ∨ p2)) → p4) ∧ (((((True → p1) ∨ (p1 ∧ p3)) ∨ p5) → p5) → False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((True → p1) ∨ (p1 ∧ p3)) ∨ p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h16 := h1 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h19 := h4 h5
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105772881537518659736316852304 : ((((p5 ∧ ((p4 → p3) → (p3 ∨ ((p5 ∨ p1) ∨ (p5 ∧ (p4 → p2)))))) ∧ p4) → (p1 ∨ (p3 ∨ ((False ∧ False) ∨ p5)))) ∧ (p4 ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301354529471935791807580860662 : (False ∨ ((p2 → ((p5 → p1) → p2)) ∧ (((p3 → ((((p1 ∨ ((p1 → (True ∨ (p5 ∨ p3))) ∨ p4)) ∨ p4) → p3) → p5)) ∨ p5) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61447546101899979301463469909 : ((p1 ∧ ((p4 → (((False → (p3 → p5)) → p5) → ((p4 ∧ (((False → p2) ∧ p3) → p3)) → ((True ∨ p2) → (p4 → p3))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47779640757188357855017814949 : ((((p4 → (p5 → (p4 ∨ ((True → (True ∧ (False ∧ (p5 ∧ ((p5 ∨ (p5 ∧ (False ∨ False))) ∧ True))))) ∧ p4)))) ∨ p5) → (False ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624987062953768399825659460511 : ((((p5 ∨ (p4 ∨ (True → (((p4 → True) → p3) ∨ ((p2 → (p1 ∧ (False ∧ (p5 → p1)))) → ((p5 ∧ (True → p3)) ∨ True)))))) ∨ p5) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399347958198851743316372738937 : ((((p2 → (((((((False → (False → p3)) ∧ p3) → False) ∧ (p3 → ((False ∧ p2) → p4))) ∨ (p3 → p3)) ∨ (False → p4)) ∨ False)) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317602756904103887516384243978 : (p4 ∨ (((p1 ∧ (((p2 → (p4 → ((True → ((p3 ∨ True) → False)) ∨ ((p5 ∨ True) → ((p4 ∧ p1) ∧ p5))))) → p1) ∨ p1)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49045278066868316884929512103 : ((((p3 → (((p5 ∨ p5) ∨ p2) → ((p1 ∨ (p2 ∨ (p4 → (p2 ∨ (p1 → p2))))) → (False ∨ True)))) → p1) ∨ ((False → p3) ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184604661170803285160691876626 : ((((((p4 → False) ∨ p4) ∨ False) ∨ p5) ∧ ((p1 ∧ p1) ∨ True)) ∨ (p2 → ((p2 → p4) ∨ (p1 ∨ (((p1 ∨ (p5 → p2)) ∨ p1) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_590342885500808985170556447531 : ((((((p3 ∨ (p4 ∨ p3)) ∨ (True → ((p5 → ((p2 ∨ (p5 → (p1 → p4))) ∧ (p2 ∨ (False → (p3 ∧ p5))))) ∧ p1))) → p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260527158429525537822758195682 : ((p3 → p1) → (((p1 ∧ p3) ∨ ((False ∨ (True → (False → (((p1 ∨ p4) ∧ False) → (p3 → p1))))) ∧ ((True ∨ (p4 → p4)) → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177672389753691884431020371892 : ((((((True ∨ p4) ∨ (p5 → (p5 ∧ (False ∧ p4)))) → p2) → False) ∧ p3) ∨ ((((False ∧ p2) ∨ (False ∨ (p4 ∨ p2))) ∨ (p1 ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41681851236373747544778446079 : ((((p1 ∧ (((p3 ∨ p5) ∨ False) → p4)) ∨ (True ∧ ((((p1 → (p1 ∨ p3)) → p1) ∧ ((False → p4) ∨ (p1 ∨ p3))) → p5))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68266425905319590235238014909 : ((p3 → (((p4 ∧ (p1 ∧ (p1 ∧ ((p5 ∨ p3) → (p2 ∨ False))))) ∨ (p3 ∨ ((p1 ∨ ((p3 → p1) → p2)) ∨ p2))) ∨ (p1 ∧ p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56011176821421867523029733184 : (((((False ∨ p1) ∨ p1) ∨ p3) ∨ ((p3 → ((p5 ∨ False) → ((True ∨ p2) ∧ p3))) ∧ ((p5 ∧ ((p3 ∧ p4) ∧ False)) ∨ (False → p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



