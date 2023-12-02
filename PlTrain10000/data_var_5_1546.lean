variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302827077911151482283674838206 : (False ∨ (p5 ∨ ((True ∧ (((p4 → p3) → p4) ∧ p3)) ∨ ((True → ((False ∨ (((p3 → p4) → p1) ∨ p4)) ∨ ((p2 ∨ True) ∧ p5))) → True)))) := by
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
theorem thm_5_vars_61107189901428445843927609100 : ((False ∧ ((((True ∧ p4) → (p4 → False)) → (((p5 ∨ p5) → (False ∧ p2)) ∨ p5)) → (((True → p1) → p4) ∧ (p1 → (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167868393700701113676777245911 : ((((p4 ∧ (p2 ∧ (((p5 ∧ p5) ∨ p2) → p3))) → p3) → (((True → p2) ∧ False) ∧ p1)) → (p1 ∧ ((((p2 → True) → False) → p4) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (p2 ∧ (((p5 ∧ p5) ∨ p2) → p3))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p5 ∧ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : ((p4 ∧ (p2 ∧ (((p5 ∧ p5) ∨ p2) → p3))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : ((p5 ∧ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h13
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787239760354626100609616046224 : (((p4 ∨ (False ∧ (((False ∧ p4) ∨ (p1 → (False ∨ ((False ∧ (p3 ∧ False)) ∧ True)))) ∨ (False → (p5 → (p3 → ((p5 → p2) ∨ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165855200392755720422507675385 : (((p1 ∧ (p4 ∧ p3)) ∨ ((p3 ∨ p1) → ((p5 ∧ p3) ∨ ((p3 → (p5 ∧ True)) → False)))) ∨ (p1 ∨ ((p3 ∧ True) → ((p3 ∧ p4) → p4)))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246439252621418576377108985975 : ((p5 ∧ False) ∨ ((True → ((p1 → True) → (False ∧ (p5 ∧ (p1 → (((True ∨ p5) ∨ (p4 ∧ ((p1 ∨ True) ∨ p1))) ∧ (p1 ∧ p1))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355716832546605280588222241609 : (p5 → ((((p2 ∧ p4) → p3) ∨ (((p4 ∨ p1) → ((p4 → ((True ∨ p3) → p1)) ∨ ((False ∨ False) ∨ (p4 → p1)))) → p3)) → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337954857302956723708696723397 : (p1 → (((p3 ∧ True) ∧ (p4 ∨ (((p5 → True) ∧ p4) ∧ (p5 ∧ p3)))) ∨ ((True ∨ False) ∧ ((p3 → p3) ∨ (p1 ∨ (p5 ∨ (p3 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82341264048245302132664491593 : (((((False → (p3 → ((p2 → p1) ∨ p4))) → ((p5 ∨ p1) ∧ False)) ∧ (p4 → (p1 ∧ (False → p3)))) ∧ ((p5 ∨ p4) → (p5 ∧ p4))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p3 → ((p2 → p1) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115741197105524339479371753170 : ((((p1 → p4) ∧ ((p3 ∨ True) ∧ p4)) → (((p5 → p5) ∧ p2) ∧ ((((p3 ∨ True) ∨ (p5 → (False ∨ p5))) ∧ p4) ∨ p3))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123519027421439441053420702147 : ((((p5 → p5) ∧ ((p5 ∧ (p5 → p4)) ∨ (p5 → (p3 ∨ ((False ∧ p5) ∨ True))))) ∧ ((p3 ∧ (p3 ∨ p4)) ∧ (p4 → p1))) → (p1 → p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20765238654872182826645639902 : (((((((p4 ∨ p3) ∨ ((p2 → p5) → p4)) ∧ p3) ∨ p1) ∧ p3) ∨ (True ∧ ((False ∧ (True ∨ (False → p2))) → ((p3 ∨ p4) ∧ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165291703638812483551776532400 : (((((p5 ∨ (True ∧ p4)) ∨ True) → ((p2 → (True → p1)) ∧ (p2 ∧ p1))) → (p3 ∨ False)) ∨ ((p2 → (p3 ∨ True)) → ((p4 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43739362604039187190854636300 : (((((p5 → False) ∨ (p2 → (((p2 ∧ True) → (((p5 ∧ p3) → ((p4 ∨ p4) ∧ ((p2 ∨ p1) → p2))) ∨ p1)) ∧ p5))) → p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57252735873923842453308363333 : ((((p5 ∧ p2) → p4) ∨ ((p4 → (False → (False ∧ True))) ∧ ((p1 ∧ (True → ((p3 ∧ p4) ∨ (p5 → (p3 → p2))))) → (True → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319059885570442613770297831182 : (p4 ∨ ((p4 ∧ (True ∧ ((p1 ∧ (p5 → ((p1 ∧ ((p5 ∨ p1) → p3)) → p1))) → (p1 ∧ (p3 ∧ p5))))) ∨ (p4 ∨ ((False ∨ True) ∨ True)))) := by
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
theorem thm_5_vars_677506326852579831837734788067 : ((((((p3 ∧ p1) ∨ ((p4 ∧ p1) ∨ ((p4 ∧ ((p3 ∨ p1) ∧ ((False ∨ p4) ∧ p3))) → p1))) ∨ False) ∨ ((p2 → p1) ∨ (p5 ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_141336770487496604899843332865 : ((((p3 → (p3 ∨ p3)) → p2) ∨ ((False ∧ (((False ∨ p4) → (True ∨ p3)) ∧ True)) → ((False ∨ (p4 → p1)) ∧ p5))) → ((p5 → p3) ∨ True)) := by
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
theorem thm_5_vars_385478896343107372765197388339 : (((((((((((((p2 → p1) → p4) → p2) → p5) ∨ p3) ∨ ((p5 ∨ (p5 → p4)) → p1)) ∧ p4) ∨ p3) → p3) ∧ (p5 → p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_158959417530997895953124718005 : ((p2 ∨ (p2 ∨ (((((p1 → p4) ∨ (p4 → p5)) → (p5 ∧ p4)) → p2) ∧ (True ∨ (p5 ∧ p3))))) ∨ (False ∨ (p4 → (True ∨ (p1 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49502866177525192479473084495 : ((((p1 ∨ ((p2 ∨ p1) ∨ (True ∨ ((((False → ((False → p4) ∧ True)) ∨ (p5 ∧ False)) ∧ p2) ∧ False)))) → p2) → ((p4 ∨ p2) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p2 ∨ p1) ∨ (True ∨ ((((False → ((False → p4) ∧ True)) ∨ (p5 ∧ False)) ∧ p2) ∧ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629876651351730583781557902535 : ((((((p5 → (((p3 → p2) → True) ∧ (False ∨ True))) ∧ (((((p4 ∨ p2) ∧ p5) ∨ p1) ∨ (False → p3)) ∧ (p1 ∧ p2))) ∨ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41695649200340629028123114580 : (((((p1 → (p4 ∨ (p2 ∧ True))) ∨ True) → ((p1 ∧ p1) ∧ ((False ∧ (((True → p5) ∧ p3) ∧ ((True ∨ True) ∧ p4))) ∧ p2))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138029939702341212512407003220 : ((True → ((((p1 → True) ∨ False) ∧ ((p4 → ((p5 ∨ ((p3 ∧ p1) ∧ p4)) ∨ p2)) → (p1 ∨ False))) → (p4 → p3))) ∨ (p5 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822548738776666543219852619947 : (((((((p4 → True) ∨ (((True ∨ p3) → False) ∧ p1)) ∨ p1) → ((True ∨ (p5 → True)) ∧ (p3 → ((p1 ∨ (p1 ∧ p3)) ∧ p2)))) ∧ p3) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → True) ∨ (((True ∨ p3) → False) ∧ p1)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62336921776841243799465656437 : ((p3 ∧ ((p2 ∨ ((p4 → p3) ∧ ((((((p2 ∧ (p3 ∨ p4)) ∧ p3) ∨ True) ∨ p2) ∧ (p1 → p2)) → True))) ∧ ((p3 → p4) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197724341034136573064833906420 : ((((p1 ∧ p5) ∨ p1) ∧ (True ∧ (p1 ∧ True))) ∨ ((p3 → (False ∧ p3)) ∨ (p1 → (((((True → p4) ∧ False) ∧ True) ∨ p4) → (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231173347884311011374106198339 : (((p2 ∨ p3) ∨ True) → ((False → (((False ∨ (False ∧ (p4 → (p1 ∧ p4)))) ∧ p2) → True)) → (((p3 ∨ False) → p2) ∨ ((p2 ∧ True) → p2)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612790776650059418589108138614 : ((((((True ∨ p5) ∧ (True ∧ ((((p3 ∨ ((p4 ∨ p5) ∨ ((p5 ∨ p3) ∨ (p4 ∨ p2)))) ∨ p3) → p5) ∧ True))) ∨ (True ∨ False)) ∨ p1) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158410934185979919063619601596 : (((p1 ∧ p1) ∨ (False ∨ (((p4 ∨ (p1 ∨ p2)) ∧ (p4 ∨ ((p3 ∨ (p1 ∧ p3)) ∧ p3))) ∧ True))) ∨ ((p1 → p1) ∨ ((True ∨ False) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44309468864556700924759125416 : (((((True ∨ (p5 ∨ ((p5 ∧ (False ∨ p5)) ∧ ((True ∨ p2) ∨ (True ∧ True))))) ∨ p1) ∨ ((((p1 → p4) → False) → p5) ∧ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601881502552722687032127649707 : ((((p4 ∧ ((p2 ∧ (p1 ∧ True)) → ((True ∧ p5) ∨ (((True ∧ p3) ∨ (p5 → ((p4 ∨ (p5 ∧ False)) ∧ p4))) ∧ (p3 ∧ False))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317582631342546612038767220030 : (p4 ∨ (((((((p5 ∨ True) ∧ (p2 ∧ p3)) → True) ∨ ((True ∨ ((p4 ∨ (p1 → p3)) ∨ ((False ∨ p3) ∨ p1))) ∧ True)) → False) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165689421377214103357650438107 : ((((p1 ∧ p5) → (p3 ∧ (False ∧ p3))) → ((((False ∧ p3) ∧ (p3 ∨ p4)) → p5) → p5)) ∨ ((True ∧ (p1 → ((p5 → p5) ∨ p5))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46076446794431819573891779752 : ((((((p4 ∧ ((p2 ∧ (((p4 ∧ p2) ∨ (p4 → (True ∧ p4))) ∧ (True → p2))) → p2)) ∧ p4) → (p2 ∨ p2)) ∨ p4) ∧ (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40002276634582577453464340777 : (((p5 → (((p2 ∧ (p2 → ((p4 ∧ p2) ∨ p5))) → (p4 ∧ p2)) → (p4 ∧ (p3 ∧ (((p3 → p5) → True) ∧ (p3 ∨ p4)))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313105747073361880439965195837 : (p3 ∨ ((((True ∨ p4) → (((((p4 ∨ p5) ∨ p3) ∧ p5) ∧ p5) ∧ (((p4 → (False → p4)) ∨ p1) ∨ p5))) ∧ ((p1 → p2) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747252408646485484311757717928 : ((((p5 ∨ p2) → ((p2 ∧ (True ∧ ((((p5 ∨ (True ∧ p3)) → False) → (p3 ∨ (True → (p5 ∧ p5)))) ∧ p1))) ∨ ((p4 ∧ p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25066624698698648513019945919 : (((p3 ∨ (False ∧ p3)) ∨ (((True ∧ p2) ∨ False) ∨ ((((((p5 ∨ p1) ∨ p4) ∧ ((p2 → True) ∨ (p2 ∧ p1))) ∨ p3) ∨ p5) → True))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38069576461410122053868212903 : (((((p5 ∨ (((p2 → p2) ∨ p1) ∧ p3)) → (False → (((False → (p4 → p5)) → ((False ∧ p2) → p4)) ∧ p4))) → (p5 ∨ p4)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190910670116842743615811276447 : (((p3 → (((True ∨ False) ∨ p1) ∧ p4)) → (False ∧ True)) ∨ ((((p1 ∧ (p2 ∨ (((p4 ∧ True) ∨ p2) → (False ∧ True)))) ∧ True) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228799617929584650235051821147 : ((p3 ∨ (False ∨ p5)) ∨ (((False ∨ False) ∧ ((p5 ∧ (p1 → p5)) ∧ False)) ∨ ((p1 ∧ ((p2 ∨ (False ∧ p5)) → (p1 ∧ (p1 ∨ p1)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597731911658763606155234355244 : (((((p5 ∧ ((p2 ∨ p2) ∨ p3)) → ((((p5 ∧ ((((True ∧ p3) ∨ (p5 ∨ p1)) → (False ∧ p4)) ∨ p5)) ∧ p1) ∧ False) ∨ p4)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309954650608827523919656375129 : (p2 ∨ ((((p2 ∧ p2) → (((p5 ∨ (False → p2)) → True) ∧ (((p1 → p5) → p2) ∨ p5))) → p2) → ((p4 ∧ ((p3 ∨ p4) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458661791728513975116427985744 : ((((p5 ∨ ((p2 ∨ ((p4 → p1) ∨ (p2 → ((False ∨ p4) ∧ ((True ∨ p1) ∨ p5))))) → p4)) ∨ ((False ∧ (p3 ∨ p4)) → (p5 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258906909746693642252938342438 : ((True → p2) → (((((p4 ∨ p1) → (p3 ∧ True)) → p5) → ((False ∧ False) → (p4 → p4))) → ((p2 → (p4 ∧ (False ∨ False))) → (False ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h11
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68910615877514674404736987567 : ((p4 → (False ∨ ((p5 → (((False ∨ p5) → True) → (((True ∨ ((p1 → p5) → (p4 ∧ p5))) ∧ (p4 → (p4 ∨ True))) → p1))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135078415150269485890756914591 : (((((p3 ∧ ((((p2 ∧ True) → p4) ∧ (False ∧ p4)) → p4)) ∨ (p3 ∨ p2)) ∧ (True ∧ (False ∨ p1))) ∨ (p4 ∨ True)) ∨ ((p3 ∧ p5) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340205431224142398587147056038 : (p1 → (p5 → ((((p5 ∧ p4) ∨ (p2 ∨ (p3 → (False → (p2 ∨ (True ∧ p3)))))) → (p3 ∨ ((p5 ∧ ((True ∧ p5) ∧ p2)) ∨ True))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58322930043684162199222804267 : (((False ∨ False) ∧ ((((True ∧ ((p1 ∧ p5) → ((p4 ∨ False) ∧ ((p4 ∨ True) ∨ True)))) → p3) → (p3 ∨ p4)) → ((p2 ∧ p3) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749477070102390669142174625442 : (((True ∧ (((((True → p3) ∨ False) ∨ (p1 → p5)) → ((False ∧ p2) ∨ (((p2 ∧ p5) → (False ∧ p2)) → ((False ∨ p3) ∨ p4)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606334392893460083016915564072 : ((((((((p2 ∨ ((p4 ∨ False) → (((((p5 → p5) → p3) ∨ p3) ∧ p3) → (p4 → True)))) ∧ (p4 → False)) → p4) ∨ False) ∧ p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_763957112176928225222144920890 : (((p3 ∧ (True → (p3 ∧ ((((False ∧ True) ∧ (p5 ∧ p4)) ∨ (p2 ∧ ((((True → False) ∧ p2) ∨ ((p4 → p4) ∨ p2)) → p5))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329699861392951486737288985402 : (True → ((p5 ∨ p2) → ((p5 ∧ ((p4 ∨ (p1 → (p1 ∨ p4))) ∧ p2)) ∨ (p4 ∨ ((p1 ∨ p5) → (True → (p3 ∨ ((p5 ∨ p1) → True)))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639221543602117298488297934281 : (((((p2 → (p2 ∧ (p2 → p1))) ∨ ((((((((p2 ∧ True) ∧ p5) ∧ p3) → p2) ∧ False) → p1) → (p3 → p5)) → (p4 ∧ p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114659946454171336689515087123 : ((((True → (p1 ∨ (p5 ∧ p3))) ∨ ((((p4 ∨ p5) → (p4 → p4)) ∧ p4) → False)) ∨ (False → (p3 ∧ ((p4 ∧ p2) ∧ p2)))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191313799391946111265347018538 : (((p5 → p4) ∧ ((((p2 → p1) ∨ p4) ∨ True) ∧ p1)) ∨ ((((p4 ∧ (p1 → True)) → (False ∧ p2)) → (p2 → p1)) → ((True → False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116174385168669654605083971107 : (((p1 → (p2 → p3)) ∧ (p4 ∧ (p3 ∧ ((((p5 → (True ∧ False)) ∧ (p3 ∧ p4)) → ((p2 → False) ∧ False)) ∧ (p1 ∧ p3))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114524138141653521479576615263 : (((p5 ∧ ((((True → p4) → p5) → p1) ∨ (((False ∨ (p5 ∨ (p5 → p5))) ∨ p2) → p4))) → (p2 ∧ (p5 → (False → p4)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37591470321688913450094176798 : ((((p4 → ((False ∨ ((((p1 ∨ p4) ∨ (p1 ∨ p1)) ∧ p4) ∧ p3)) → (((p2 ∨ ((p2 → p5) ∨ p5)) → p2) ∧ False))) ∨ p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184387061245192452794942647832 : (((p2 → ((p2 → True) ∧ (p5 ∨ (p5 → (p3 → p4))))) → p1) ∨ (p5 ∨ (((p5 ∨ p5) ∨ ((False ∨ False) ∨ p3)) ∨ (True → (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117294772801786405638791099324 : ((False ∧ (((((p1 ∧ ((False ∧ p2) → ((p3 ∧ (False → p2)) → p4))) ∨ (p1 → (p2 ∧ p5))) ∧ p2) ∨ p3) ∧ (p2 → False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61500383892951354493097099032 : ((p1 ∧ (((p5 ∧ ((((p2 → p4) → ((True → p3) ∨ False)) → p2) → ((p1 → p2) → p1))) ∧ False) ∧ (p1 → ((p5 ∨ p4) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616954443904127773766856973327 : (((((p5 ∨ (((p5 ∧ (False → p2)) ∨ p2) ∨ (False ∧ p5))) → (p2 ∧ (((True ∨ ((p3 → p1) ∨ p2)) ∧ p2) → (p3 → False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_256957504194771175342115882435 : ((p1 ∨ p5) → (((((((p5 ∧ (True ∨ (True → (p3 → p3)))) ∨ (p3 ∧ True)) ∨ p4) ∧ p2) → p3) → (p4 ∨ p5)) ∨ (False → (p3 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158575790182912751785379567648 : ((True ∧ ((p2 → (False ∨ p3)) ∧ ((True ∧ (p1 → ((p1 ∧ p2) → ((True → False) ∧ p2)))) → False))) ∨ (p3 → (p4 → ((True ∧ p1) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62283671669388115698125300227 : ((p3 ∧ (((p5 ∨ (p4 ∨ p3)) ∨ (p3 ∨ (False ∨ (p5 ∧ ((p2 ∧ False) ∨ (False ∨ ((((p3 ∨ p3) ∧ p1) → False) → p3))))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323572428361186995276968029873 : (p5 ∨ ((((p5 → p4) ∨ True) ∧ (((p1 ∨ ((((p2 ∧ p2) → True) ∨ False) ∨ ((p5 ∧ p2) ∨ p2))) ∧ False) → p1)) → (False ∨ (p1 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58949264231142439945147786226 : (((p2 ∧ True) ∨ (p3 ∧ (((((p3 ∨ p3) ∧ True) ∧ False) ∧ (p2 → p5)) ∨ (((p3 ∧ False) ∨ (False ∧ p2)) ∨ ((p5 → p2) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166432693629953060366367225854 : ((p1 ∨ (False ∨ (p5 ∧ ((((p3 → p5) ∨ p4) → ((p5 ∧ False) → False)) → (p4 → p5))))) ∨ ((p2 ∧ False) → (((p1 → p3) ∨ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161508940059613532066129191680 : ((p4 ∧ ((((True ∨ p3) → p1) → p4) → (False → ((p3 ∨ (((False → p5) ∨ False) → True)) ∧ p5)))) → (((p3 → (p5 → True)) → p5) ∨ True)) := by
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
theorem thm_5_vars_47423986065457707517488662692 : (((p1 ∧ ((p4 → (True ∧ p5)) → ((((p1 ∧ (True → (False ∨ ((p3 ∨ p2) → (p2 → p3))))) → p2) → p1) ∨ p5))) ∨ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225385914156668116565367900098 : (((p2 ∨ p2) ∧ p4) ∨ (p1 → ((p2 ∨ ((((p5 ∧ (p3 → (p2 ∨ p5))) ∧ True) ∨ (p2 ∧ True)) → (False ∨ p3))) ∨ (p5 → (p4 → p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217892804871823714828704285861 : (((p2 → (p1 → p5)) → True) → ((p5 ∧ ((False → False) ∧ False)) ∨ (((p4 → p3) ∧ ((p1 → p3) → (p5 ∨ p4))) ∨ ((p5 → p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55828084394553412770730500179 : (((True ∧ ((p1 ∨ True) ∨ p1)) ∧ ((((p3 ∧ (p3 → False)) → False) ∧ ((p4 → p3) ∧ p3)) ∨ ((((p4 ∨ p4) ∨ p3) ∧ p5) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304684409511954910240735845200 : (p1 ∨ ((((p5 ∨ (((False ∧ (p3 ∨ ((p4 ∨ p5) ∨ (((p4 → p3) ∨ True) ∨ (p5 ∨ False))))) ∨ True) ∧ p4)) ∧ p5) ∨ p3) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192293510265315329519686119576 : ((((True ∨ p1) → (((p2 ∧ p5) ∧ p1) ∧ p4)) ∧ p5) → (p1 → (((p1 ∨ True) ∨ (((p1 → p5) ∧ p3) → False)) → ((p3 ∨ p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51178073333671439606118715774 : (((((p1 → ((p1 ∧ ((p5 → p1) → p4)) ∧ p5)) ∧ (p5 → (p3 → p5))) → (p5 → p1)) ∨ (((p3 → (p1 ∨ p4)) ∧ False) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234112350947219603321083662557 : ((True → (False ∨ p4)) → (((((p1 ∧ p1) ∨ p2) ∨ ((False ∧ (p4 → p3)) ∧ (p3 → p4))) → (False ∨ (((True → p5) → p4) ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351293469655674544738533144629 : (p4 → (((False → ((True → (p4 ∧ ((p2 ∨ (((p2 → p3) ∧ (p4 ∨ p2)) ∨ p1)) ∧ p1))) → False)) ∨ (True ∧ p3)) → ((True → p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_815898793952579917597884569066 : (((((((p3 ∧ ((p5 → (p1 ∨ (p2 ∨ (p1 ∧ p4)))) ∧ (p5 → ((p2 → ((p2 → p1) ∨ p1)) ∧ p4)))) → False) ∨ p5) → False) ∧ p5) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ ((p5 → (p1 ∨ (p2 ∨ (p1 ∧ p4)))) ∧ (p5 → ((p2 → ((p2 → p1) ∨ p1)) ∧ p4)))) → False) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699374802767485539486781893960 : (((((p2 ∧ (p1 ∧ (((p4 ∧ p4) ∧ p2) → (p4 ∧ p4)))) ∧ p2) → (p1 → (((p2 ∨ (p3 ∨ ((p3 ∧ p5) → p4))) ∨ True) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164857136817824214506150076718 : (((p1 ∨ (((False ∧ ((((p3 ∨ p4) → (True → p1)) ∨ p3) ∧ p3)) ∧ True) ∨ p2)) ∨ p5) ∨ ((True ∧ p3) ∨ (((True → p2) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192255062674554238478000348520 : ((((p3 ∧ (True ∨ False)) ∧ ((p3 → p2) → p2)) ∧ p1) → (((((p2 → (False ∧ (p5 ∨ (True ∨ p1)))) ∨ p1) → p5) ∨ (True ∨ p5)) ∨ p3)) := by
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234507767156643498831513873359 : ((p2 → (p1 → True)) → ((((p4 → p5) → (((((p4 ∨ p2) ∨ ((p5 ∧ p2) ∨ p2)) ∧ p3) ∧ p3) → p5)) ∧ p5) ∨ ((p4 ∧ False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164964864333586518379269177264 : (((((((p1 → p3) ∨ True) ∧ (p3 → p5)) → (p1 ∧ (p4 ∨ p5))) ∧ (p1 → p2)) → p4) ∨ (((p2 ∧ True) ∧ ((p4 ∧ True) ∨ p5)) → p2)) := by
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344728436072926090054932117436 : (p2 → (p3 → ((p3 ∨ (((p4 ∧ p1) ∨ (((((False ∨ p2) → p3) ∨ p5) → p2) ∨ p2)) ∧ ((p2 → p3) ∨ p2))) → (p4 ∨ (True ∧ p2))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65632343444451633120951090061 : ((p4 ∨ ((((p1 → p1) ∧ ((((p2 ∨ (p1 ∨ p3)) ∧ p1) ∧ (p3 ∧ False)) ∧ ((p3 ∧ (p2 ∨ True)) ∨ p1))) ∧ (p4 ∨ p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669911218362428025056041439947 : ((((((p1 → (((p1 ∧ True) ∨ False) ∨ (True ∨ p1))) ∧ p2) ∧ (p5 ∧ ((True → False) → (p1 → (p5 ∨ p3))))) ∨ (p4 → (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777343003487286714694558885795 : (((p1 ∨ (((p1 ∨ ((p1 ∨ True) ∨ p2)) → (((p4 ∨ ((p3 ∨ p2) ∧ p2)) → (p2 ∧ True)) ∨ p2)) ∨ ((p3 → (p1 → p4)) ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_61716983377524971917421635978 : ((p1 ∧ (True → ((p3 → ((True → False) ∧ (True ∧ (((p4 ∨ ((p2 → (p2 ∧ ((p1 ∨ p2) → p1))) ∨ p2)) → p4) ∧ p4)))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180213070336632905594644174336 : ((((False ∨ p3) ∨ (False → ((p3 ∨ ((False → p3) ∧ p5)) → True))) → p5) → (p4 → ((p4 ∧ ((p5 ∨ True) ∧ (p5 ∨ (p2 ∧ True)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ p3) ∨ (False → ((p3 ∨ ((False → p3) ∧ p5)) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633001416963490729287502374544 : ((((((p1 → (p3 → ((True ∨ True) ∨ ((p1 ∧ True) → False)))) → ((((p1 → (p4 ∨ p3)) ∧ True) ∧ p2) → False)) ∧ (True ∨ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310306489352843974357710114243 : (p2 ∨ (((p4 ∨ p4) ∨ ((p3 ∨ (p5 ∧ (p5 ∧ p3))) → False)) ∨ (((False → (p5 → (p4 → p2))) → (True → ((True → True) ∨ p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328821692126774625745880627257 : (True → (((((p4 ∧ p3) → (True → p3)) → True) → (p5 ∧ False)) → (p5 ∧ (p5 ∧ ((p1 ∨ p4) ∨ ((p3 → (p1 → True)) ∧ (False ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ p3) → (True → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (((p4 ∧ p3) → (True → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (((p4 ∧ p3) → (True → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232181221348322444900465849806 : (((False → False) → p1) → (((p1 → (p5 ∨ False)) ∧ ((((p4 ∨ ((p1 → (p1 ∨ p4)) ∧ (p3 → p5))) ∨ p2) ∨ (True ∧ True)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54215905632191948946487304594 : ((((((p3 → p5) ∨ (p5 → p4)) ∧ p5) → False) ∧ (p2 ∨ (True ∧ ((p1 ∧ (p4 ∨ ((False ∨ ((True → p1) ∧ p2)) ∨ p2))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51174530211378594337402192888 : ((((p1 → ((((p1 ∨ p3) ∨ p3) ∧ (p3 ∨ (True → True))) ∧ (p2 ∧ p5))) ∨ (p1 ∧ p5)) ∨ (True → ((False ∨ False) ∨ (p3 ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247736160462506569852046623230 : ((p1 ∨ False) ∨ (((p4 ∧ p4) ∧ ((p1 → (True ∧ True)) ∧ p2)) ∨ ((True ∨ ((p1 ∨ p2) → p5)) ∨ (False ∧ (p4 → (p3 → (p5 ∧ p4))))))) := by
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
theorem thm_5_vars_167479757404882317908998722876 : (((((p5 ∨ (((p5 ∨ p1) → p3) → p1)) ∧ (p2 → (p5 → True))) ∧ p4) ∧ (p3 → p1)) → ((p3 ∧ (((p2 ∨ p4) ∨ True) ∨ p2)) → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h15 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h16 := h9 h15
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h18 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h19 := h9 h18
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h28 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h29 := h22 h28
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h31 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h32 := h22 h31
          -- One of the premise coincides with the conclusion.
          exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h36.left
      let h39 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h41 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h42 := h35 h41
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h43 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h44 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h45 := h35 h44
        -- One of the premise coincides with the conclusion.
        exact h45
  case inr h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h47.left
    let h50 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h49.left
    let h52 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h53 =>
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h54 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h55 := h48 h54
      -- One of the premise coincides with the conclusion.
      exact h55
    case inr h56 =>
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h57 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h58 := h48 h57
      -- One of the premise coincides with the conclusion.
      exact h58



