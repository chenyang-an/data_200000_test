variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313317581632265143378663201141 : (p3 ∨ ((p2 ∨ (True ∧ (((p3 ∨ ((p5 → (((p1 → ((True ∨ p3) ∧ p2)) ∧ False) → (True → p2))) → p3)) ∧ p1) ∨ (p5 → p5)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258981971153404104746117054984 : ((True → p3) → ((p3 ∨ p5) → (((p2 → (((p2 → (True ∨ ((p1 ∧ p3) ∧ (p1 ∧ p4)))) ∧ (p3 ∧ p5)) ∨ p4)) → p4) ∨ (p3 → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133977263336714075371191600698 : (((((((p4 ∧ True) ∧ (((((p3 ∧ True) ∨ p5) ∧ p2) ∧ p5) ∨ (True ∨ (p4 ∧ False)))) ∧ p5) ∨ p4) ∧ True) ∨ False) ∨ ((p1 → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10334786835946163188597279945 : (((p5 ∨ ((((((p4 ∧ True) ∧ p4) → ((p1 ∧ p3) ∧ p2)) ∨ p3) ∨ (True → ((p4 → (p3 → p3)) ∨ p5))) → (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137456280364488668597975831074 : ((p4 ∧ ((p2 ∨ p2) ∨ (((p3 ∨ p3) → (p5 ∨ False)) → ((((p2 ∨ p1) ∧ False) → (p5 → False)) → (p2 ∧ False))))) ∨ (True ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16882699565297521900459514153 : ((((True → p1) → (True ∧ (((p5 ∨ p1) ∨ ((p5 ∨ False) ∧ (False → True))) ∧ ((p4 ∧ p4) ∨ (p3 ∧ p4))))) ∨ ((p1 ∧ False) → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_156937067255496498096642967931 : ((((((p3 ∧ ((False ∧ ((p2 ∨ p1) → (p3 ∧ True))) ∧ True)) ∧ p3) ∨ p3) ∨ (p5 ∧ True)) ∨ p5) ∨ (((p3 ∧ p2) ∧ True) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249697960890405626693787823930 : ((p5 ∨ p4) ∨ (False ∨ ((False ∨ True) ∧ (((False → (p5 → True)) ∨ False) → (p4 → ((p2 ∨ (True ∨ p5)) ∨ (p5 → ((False → False) → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350974179140831275069217825786 : (p4 → (((True ∧ (False ∨ True)) ∧ ((p5 ∨ (p3 → (p2 ∨ ((p5 → (p4 ∨ (p3 ∨ p1))) → ((p5 ∨ p1) ∧ True))))) → p1)) ∨ (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125644816381395709503906678899 : (((p2 ∧ p1) ∨ (((p1 → p5) ∨ (p4 ∧ p5)) → (p5 → ((((False ∧ p2) → (p2 → p3)) ∨ p2) ∧ ((True ∨ p5) → p3))))) → (p5 ∨ True)) := by
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
theorem thm_5_vars_350637840967095570562738525960 : (p4 → (((True ∨ p5) ∧ ((((((((p4 → p4) ∨ p2) → (False ∨ p2)) ∨ p4) → p5) ∨ p3) ∨ ((True ∨ (True ∨ p3)) ∨ p5)) → p1)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (((((((p4 → p4) ∨ p2) → (False ∨ p2)) ∨ p4) → p5) ∨ p3) ∨ ((True ∨ (True ∨ p3)) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (((((((p4 → p4) ∨ p2) → (False ∨ p2)) ∨ p4) → p5) ∨ p3) ∨ ((True ∨ (True ∨ p3)) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346898165306835667029659922439 : (p3 → (((True ∧ ((p3 ∨ False) ∧ (p1 ∧ ((p5 ∧ (p1 ∨ p5)) ∧ ((p5 ∨ False) ∧ p5))))) ∨ p1) ∨ (True ∨ (p2 → (p4 → (p5 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167236037474394346318863723347 : (((p1 → (True ∧ ((((p5 ∨ ((p1 ∧ p1) → False)) → p1) ∨ (False ∧ p4)) → p1))) ∨ p1) → (p3 → (((p5 ∧ p4) ∨ (True ∧ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659433673796116536582664629832 : (((((((p1 → p3) ∨ (((((p4 ∨ True) ∧ True) → (False ∧ (p2 → p1))) ∨ (p2 → (p1 ∨ p3))) ∧ False)) ∨ p3) ∧ True) → (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158164748724207783482504490041 : (((((p1 ∧ p1) ∨ p5) ∨ p3) → (((p1 ∨ p2) → (True → p2)) ∨ ((p3 ∧ p2) ∧ (p2 ∨ p3)))) ∨ (((p3 ∧ False) → (p5 → p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302907576341189026262636297339 : (False ∨ (True → (p4 ∨ ((False ∧ ((((p2 ∨ (p5 ∧ p5)) ∨ p5) ∨ p3) → ((((False → False) ∧ (True ∨ p1)) ∧ True) → (p1 ∧ p1)))) ∨ True)))) := by
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
theorem thm_5_vars_662955470686851137798009184842 : (((((True → (False ∨ p4)) ∨ (((p4 → (p2 ∨ (p3 → ((False ∨ (True ∧ p5)) → False)))) → (False → p5)) ∧ (True ∨ p2))) → (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37954347438507617748725358901 : ((((((p1 ∨ False) ∧ ((True → ((p5 → (True ∧ False)) ∧ p5)) ∧ (p1 → ((p4 ∧ p2) → (p4 → p1))))) ∧ p3) ∨ (p3 → p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913034426451729143565633399910 : ((((((p4 → p5) ∧ True) → ((p5 ∨ (p2 ∧ p4)) → (((True ∧ (p2 ∨ p3)) ∨ True) ∨ p4))) → (p5 ∧ ((False ∨ p5) ∧ (False ∧ p1)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → p5) ∧ True) → ((p5 ∨ (p2 ∧ p4)) → (((True ∧ (p2 ∨ p3)) ∨ True) ∨ p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39036380332686633367743305271 : ((((p4 → p4) ∧ ((p4 ∨ (True → p1)) ∨ ((((p3 → p4) ∨ (p3 ∨ False)) ∧ (((p5 → False) ∧ p1) ∨ (p2 → p2))) ∧ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54221105178737513215594398150 : ((((((p2 → (p5 → False)) ∨ p4) → p4) → p3) ∧ (((True ∧ p2) ∨ (p2 → (p1 → p1))) → ((p1 ∨ p4) ∨ ((True → p5) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260829491496196445154200872192 : ((p4 → True) → (((p3 → (((True ∨ ((True → p3) ∧ ((p2 ∨ p3) ∨ p2))) ∨ (p5 ∧ False)) ∨ p4)) → ((True ∧ (p2 → p1)) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321329412687948746779921121255 : (p4 ∨ (p5 ∨ (True ∧ ((p3 → ((((p4 → (p2 ∨ True)) → (p1 → (((p1 ∧ ((False → p1) → False)) → p5) ∧ True))) ∧ p1) ∨ p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_345402337820381120190651645558 : (p3 → ((((p3 → (True ∧ (p3 ∧ ((p3 ∨ ((False ∨ ((False ∧ (True ∨ p5)) ∨ p1)) ∧ False)) ∧ (True ∧ p2))))) ∧ (p1 → p1)) → p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179148403328174853213883039415 : ((p2 ∧ ((p4 ∨ (False ∧ (p3 → ((True ∨ (p5 → p3)) → p4)))) ∧ False)) ∨ ((p5 → ((p1 → p1) ∨ (p4 ∨ ((p3 → p2) ∨ p4)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147476412626777948417626285562 : (((p2 ∧ (((((True → p5) → (((p5 → (p4 → False)) ∨ p1) ∨ False)) ∧ p1) ∨ False) → (False ∧ False))) ∨ True) ∨ ((True → (p4 ∨ False)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606080113894935134874697755799 : ((((p5 → (p3 ∨ ((((False → (p1 → (False → (p1 ∧ p4)))) → (p4 ∨ p1)) ∧ p5) ∧ (p2 → ((p1 ∨ (p2 ∨ False)) ∧ p4))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212194652704994308326583681726 : ((True ∨ (p4 ∨ (p3 ∨ p1))) ∧ ((((p4 ∨ p5) → (p4 ∧ ((p1 → True) ∧ ((p4 → True) ∧ (False ∨ p2))))) ∨ (p3 → (True ∨ p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337957860453385940767985674682 : (p1 → ((True ∧ (p4 ∧ (((p3 ∧ p5) → (p3 → (True ∧ p3))) → p5))) ∨ ((((p4 → ((p4 → True) ∨ p3)) ∨ (p2 ∨ p3)) ∧ p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135161952982780041269836736544 : (((((((p1 → ((((p2 → p3) ∧ p4) ∧ True) ∧ p3)) ∨ p3) ∧ ((p3 ∨ p1) ∧ p1)) ∨ True) ∧ p3) → (p5 ∧ p2)) ∨ (p1 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621103508212621729608780214454 : (((((p3 → p4) → (p5 ∧ (p2 → (((p3 → (((p2 ∧ (p2 ∧ True)) ∧ p4) ∧ p4)) → ((False ∧ (False ∨ True)) ∨ p3)) ∧ p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_263425746656464311323568689609 : (True ∧ ((p4 ∨ ((((p4 ∧ (p1 ∧ False)) ∧ p4) ∧ (p2 ∨ (p5 → (((p4 → False) → p4) → False)))) ∨ (p4 ∧ True))) ∨ (p5 ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137825239580975189575597244714 : ((p3 ∨ ((True ∧ ((p1 ∨ p3) ∧ (((False ∨ (p1 → p3)) ∨ (False → (p3 → p4))) ∨ (p3 ∧ (p4 ∨ False))))) → False)) ∨ (True ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305411836986556444882434534943 : (p1 ∨ (((True ∧ p2) ∧ ((True → (((p2 ∧ True) ∧ (False → p1)) ∧ (p1 → True))) ∨ p1)) ∨ (p3 ∨ ((p5 ∨ p5) → (p1 → (True ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50227611924004738242980854437 : ((((p5 ∨ ((p3 → ((((p1 ∧ (p5 ∧ p2)) → False) → False) ∨ ((p1 → False) ∨ True))) ∧ True)) ∨ p1) ∨ (p2 ∨ ((p1 → p1) ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60324882760349226914649053312 : (((p2 → True) → ((((((True → p3) → (p1 ∧ (p1 ∧ p1))) ∨ ((p1 → p3) → p5)) ∧ p3) ∨ p2) ∨ (False → ((True ∧ p4) → p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50663559614219236061854752395 : ((((False ∨ (p1 → (((p4 ∨ True) ∨ p2) → p1))) → (False ∨ (p3 → ((p5 → p1) ∧ (True ∧ p1))))) → (((p1 → p1) → p5) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711830330071520500220790321702 : ((((((False ∧ False) → (p2 → p2)) ∧ p4) ∨ (p1 ∨ (((False ∧ p3) ∨ p1) ∨ (False ∨ (p4 ∨ (p1 → ((p1 ∨ p3) ∧ (True → p1)))))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315013948214293182312788704521 : (p3 ∨ ((((p3 ∧ (p5 → True)) ∧ p1) ∧ (p3 ∧ False)) ∨ (((False → True) → (p2 ∧ True)) ∨ (p4 ∨ (True ∨ (p1 → (p4 ∨ (p5 → True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_59242440796082527694287575180 : (((p2 ∨ p2) ∨ (True → (p1 ∨ (((p5 → ((p5 → (p3 ∨ p3)) ∨ ((p1 → p5) → p5))) ∨ (((p3 → p5) ∨ p2) ∨ p3)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59867315396420295323421607375 : (((p4 ∧ p2) → ((((p4 ∧ True) ∨ ((p4 → (((p4 ∨ True) ∧ p4) → True)) ∨ p2)) → ((False ∧ (True ∧ (p3 → p5))) ∧ p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622694325486541973518956940166 : ((((p4 ∧ ((True ∨ (p2 ∨ (False ∧ False))) ∧ (((p5 ∧ (((p2 ∨ p1) ∨ (p5 ∨ ((p2 ∧ True) ∧ p5))) ∨ p1)) → p3) → p4))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_692657323136774180460160910164 : ((((((p5 ∨ (p3 ∧ (p4 ∧ p3))) ∨ p1) ∧ (p5 ∧ (True ∧ (False → p2)))) ∧ ((p3 ∧ p2) → ((False → True) ∨ (p5 ∧ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262497227190441573504271859469 : (True ∧ ((p1 → ((p2 ∨ (p3 → False)) ∨ (((False ∨ p2) → (p2 ∧ ((((p4 ∧ (p4 ∨ p3)) → p5) → False) ∨ p1))) ∨ (True ∨ p2)))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47888756154264499829232171651 : (((((((p5 ∨ (p4 → (p4 ∧ (p2 → (True ∨ p2))))) ∧ p4) ∨ p5) ∧ (p4 ∨ ((True → p1) → True))) ∨ (True ∧ p4)) → (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148273704094554771068372721125 : (((((p5 ∧ (p1 ∨ p5)) → (True ∧ (p5 ∨ (((p5 ∨ True) ∨ p1) → p1)))) ∧ p2) → ((p4 ∨ False) ∨ p4)) ∨ (((p2 ∧ p2) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184098634001917943121864269304 : ((((p4 → (p3 ∨ p4)) → ((p4 → (True ∨ p4)) → False)) ∨ p4) ∨ (False → ((p5 → (p3 ∧ (p1 → (((False ∨ p2) → p1) → p2)))) ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147898591571581251871009892159 : ((((p1 ∨ ((p3 ∧ p1) ∧ (((p2 → True) ∨ (p4 → (p4 ∧ p2))) ∨ (p2 ∧ p3)))) ∨ True) ∧ (p1 ∨ p1)) ∨ ((p4 → (True ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637726978150418687268310682466 : ((((((p2 ∧ (p2 → (False ∨ p3))) → ((p1 → True) ∧ p3)) → (p3 ∨ (((p2 ∨ (False ∨ p4)) ∧ p4) ∧ (p1 ∧ (p2 ∨ True))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137326940319677533565344856346 : ((p2 ∧ (True ∧ ((True → ((p5 → (p4 → True)) ∨ ((((p3 ∧ (p4 ∨ (p4 ∨ p3))) ∨ p5) → True) ∨ p1))) → p2))) ∨ ((False → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86669219621690987687645636105 : ((((p2 ∧ p4) → ((p3 ∨ (True ∧ p2)) ∧ False)) ∧ ((p3 → ((p3 ∨ p4) ∧ p1)) ∧ (p3 ∧ ((((p1 ∧ p5) ∧ True) ∧ True) → True)))) → p1) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710624525892329985178613025277 : ((((((p1 ∧ False) ∧ False) ∨ (p1 ∨ p4)) ∧ (p1 → (True ∧ ((p5 ∧ (((p5 ∨ (p3 ∨ p1)) → p3) → ((False ∨ p2) ∧ False))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111451275949752423477241151903 : (((True → ((True ∧ (p4 ∧ (p5 ∨ (p1 → True)))) ∨ ((((p2 ∧ p2) ∧ (((p4 ∨ p3) ∨ p4) ∧ p1)) → p5) → p3))) ∧ p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136608538960932619701430170714 : (((p3 → (p1 ∧ p2)) ∨ (p1 ∨ ((p2 → ((False ∧ p3) ∧ (False → ((p4 ∨ (p1 ∧ False)) → (p3 ∨ p1))))) → p4))) ∨ ((True ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42527833625225107382358808218 : (((p1 ∨ ((p1 ∧ ((((p4 → (p3 ∨ (True ∨ ((((p5 → p1) ∨ p2) ∧ True) → (p5 → p5))))) ∧ p1) → p4) → p3)) ∧ p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147262672999950558890945384257 : (((((((p3 ∨ (((False ∧ p4) ∧ (p2 ∧ (p4 → (p4 ∧ p1)))) → p1)) ∧ p1) → False) ∨ p4) ∨ p4) ∨ False) ∨ (((p3 ∧ False) ∨ False) → p5)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301421993459857016675262185516 : (False ∨ (((p5 ∨ (p2 → p1)) → True) → ((p1 ∨ ((p2 ∧ ((p3 → ((p2 ∧ (p3 ∧ p2)) ∧ p4)) → p4)) ∨ (p2 ∨ p3))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_219209818468352838262270020082 : ((False ∨ (p1 → (p1 ∧ True))) → (p3 → (((p3 ∨ p3) → (((True → p4) → ((p1 ∨ p1) → p5)) ∨ (p2 → (p3 ∧ p4)))) ∨ (p1 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563395190100508744129529351806 : (((p5 ∨ ((p4 → (p5 ∨ p1)) → (((p1 ∨ (False ∨ (p3 ∧ (((p1 ∧ ((p3 → p4) → p5)) ∨ False) ∧ p1)))) ∧ p4) ∨ (True ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137757721318687929668105014728 : ((p2 ∨ ((((p4 ∨ (True ∨ False)) ∧ (p3 → (False → p3))) ∨ (True ∨ (p3 ∧ ((p3 → False) ∧ (p4 → p5))))) → p4)) ∨ (p1 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187473697914002419822431916403 : ((False ∨ (((((p3 → (p2 → p3)) ∨ p4) ∧ False) ∨ p4) ∧ p1)) → (p3 → ((p2 ∧ (((p5 ∧ p3) ∧ False) ∧ p5)) ∨ (p2 ∨ (p2 → p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134532263679288173322322466712 : (((((((((p2 → p5) ∧ (p3 ∧ p2)) → (p4 ∨ p2)) → (p1 ∨ (p4 ∧ (False → p1)))) → True) → False) → p2) → p1) ∨ ((p3 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180469582233950019500525923057 : (((True → ((p2 ∧ False) ∨ (((True ∨ p4) ∨ p3) ∧ p5))) → (p1 ∧ p3)) → ((((p4 ∧ (p5 ∧ p5)) ∨ p3) ∧ ((p4 ∨ True) → False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662397777694949549101185852270 : (((((True → (((p1 ∨ False) ∨ p3) ∨ (p1 → p4))) ∨ (((False ∨ p3) ∨ (p1 ∧ (((p4 ∧ p4) ∨ p5) → p4))) ∨ p2)) → (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193432687323515591052598184142 : (((True → False) ∧ ((p2 → p5) → (p5 ∨ (p4 ∨ p3)))) → (p2 ∧ (p4 ∨ (False ∧ ((False ∧ p5) → (p5 ∧ (True → ((p3 ∨ p2) → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199380809337910253753464171051 : (((((p3 ∨ p4) ∧ p1) → (p1 ∨ True)) ∨ p3) → (((p3 ∨ (p2 → p4)) ∧ p4) ∨ (((p4 ∨ p5) → (False → ((p2 → False) → p1))) ∨ False))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151351164896357202052240126148 : (((p5 → ((((p5 ∧ p4) ∨ ((p3 ∨ p2) → (p1 → p2))) ∨ False) ∧ ((p1 → (p2 ∧ p2)) ∨ p4))) → p3) → ((True → (p1 → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196788712846151471759614261368 : ((((True ∧ p5) ∨ ((p5 ∧ p2) ∧ False)) ∧ p3) ∨ (p4 → (((p2 → p2) ∧ (p1 ∧ ((((p1 ∧ True) → p5) ∨ (p5 ∧ p1)) → p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256276449601634382321194821251 : ((False ∨ p1) → ((False ∧ (((p5 ∨ (((False → ((p1 → (p4 → p3)) ∧ (False → ((p1 → p1) ∧ True)))) → p5) ∧ p2)) → p2) → p4)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171373370559320408622632032527 : ((((True ∨ ((False ∨ False) ∨ (p1 ∨ ((p5 → True) → p3)))) → (p1 → p5)) ∧ p5) ∨ (((p3 ∧ p1) → p4) ∨ (p2 ∨ ((True ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264814256509349902274405363462 : (True ∧ ((p4 ∧ p2) ∨ ((p5 ∨ p1) ∨ ((((p4 ∨ (False ∧ (((False → False) → (True → (p1 ∨ (p3 ∧ p1)))) → False))) ∧ p1) ∨ True) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_135709538070942870820141386594 : (((False ∧ ((p5 ∨ ((False → False) ∧ (p1 ∧ (p1 → (False ∨ p3))))) ∧ p4)) ∧ ((p1 ∧ (p5 ∨ p2)) → (p1 ∨ True))) ∨ (p3 → (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811642265784031321522406700645 : (((p5 → (p1 → (((p4 → p5) ∨ True) → ((p3 ∧ (((((p5 ∨ p4) → p5) ∧ ((p3 → (p1 → p5)) ∨ p5)) → False) ∨ p3)) ∨ p5)))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57381489394542886136349415231 : (((p5 ∧ (p3 → True)) ∨ (p2 ∨ (((p1 ∧ ((p2 ∧ (((((False ∧ p3) ∨ p2) ∧ False) ∨ p3) → (False ∨ False))) ∨ p4)) ∧ p1) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41509353690277205095400100616 : ((((p5 → ((False → (p2 → (p5 → (p4 ∨ False)))) ∧ (p1 → True))) → (True → (p2 ∨ (((p1 → p1) → p4) ∧ (p3 ∧ p3))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75746141427130582559914214551 : (((((((p5 ∧ (p4 ∧ ((False ∧ True) → p2))) ∨ (p4 → ((True ∧ False) ∨ False))) ∨ p5) ∧ (False ∧ (p3 → (p5 → p4)))) ∨ True) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ (p4 ∧ ((False ∧ True) → p2))) ∨ (p4 → ((True ∧ False) ∨ False))) ∨ p5) ∧ (False ∧ (p3 → (p5 → p4)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184230144186662195832512142192 : ((((True → (((p3 ∨ True) → p1) ∨ (p3 ∧ p5))) ∨ p1) → p5) ∨ (p3 ∨ ((False ∧ p2) → ((((False ∧ False) → p4) → p3) ∨ (p2 ∧ p1))))) := by
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
theorem thm_5_vars_78154246657517580380548940716 : (((p1 → (((((True ∧ (False ∨ (p1 ∨ p3))) → False) ∨ p3) ∨ (False ∨ ((p2 ∧ p5) ∧ False))) ∨ (True ∧ ((False ∧ p2) → p5)))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((((True ∧ (False ∨ (p1 ∨ p3))) → False) ∨ p3) ∨ (False ∨ ((p2 ∧ p5) ∧ False))) ∨ (True ∧ ((False ∧ p2) → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713171536816228710219373925887 : ((((p1 ∨ (((p5 → p2) ∧ p1) ∧ False)) ∨ (((p5 → p4) ∨ (False → ((((p1 ∨ (p1 ∨ p5)) ∧ (p4 ∨ p1)) ∧ p3) ∨ p3))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599309133800201396053715387294 : (((((p1 ∧ p1) ∨ (((((p2 ∨ (p1 → p5)) ∨ (p5 ∧ p1)) ∧ (p3 ∧ p2)) ∧ (False → (p5 ∨ p4))) ∨ (False ∧ (p1 ∨ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707806020735618356822018807758 : ((((False ∧ (False ∨ (((p2 ∨ p4) → p1) ∧ False))) ∨ ((((p5 ∨ (((True → True) ∧ p1) ∨ (p5 → p4))) ∨ (p5 ∧ p3)) → False) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_216476288802675973664391710113 : ((p5 → ((p4 ∧ p4) ∧ p5)) ∨ ((p1 → ((((p5 ∨ (p1 → ((p4 ∨ (False ∨ p5)) ∧ p5))) ∨ p2) ∧ ((p4 ∨ p2) ∧ p2)) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339168768030655498877334424848 : (p1 → (p1 ∧ (p4 → (((((((p3 → ((p2 ∧ ((p3 ∨ p2) ∧ p2)) → p2)) ∨ p5) → (p5 ∧ p5)) ∧ p4) ∨ (p3 ∨ p3)) ∧ p5) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198079483294380263765570100843 : (((p3 ∨ p3) ∨ ((p3 ∧ (p3 → p2)) ∨ False)) ∨ (p3 ∨ (((p2 ∨ (p5 ∨ ((False ∨ (p3 ∨ p4)) ∨ True))) → (p3 ∨ (True ∨ p2))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41434526770668542750154521811 : ((((((p4 ∨ p2) ∨ (p3 ∧ (True ∨ p1))) ∧ (((False → p4) ∨ p5) → True)) → ((((p3 → p5) ∧ p1) ∧ p2) ∧ (p1 → p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49680209212564501377788814189 : ((((p3 ∨ p1) ∧ ((True ∨ (((p4 → False) ∧ (p3 → p1)) → False)) → ((False ∨ (False ∧ (True → p2))) → False))) → (p3 ∨ (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67543321330068770568756394603 : ((p1 → (((p1 ∧ False) ∧ p1) ∨ (((((((p4 ∨ p3) ∧ p4) ∨ p4) ∧ p2) ∧ p3) ∨ (True ∧ False)) ∨ ((p1 ∨ True) ∨ (p3 → False))))) ∨ p1) := by
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
theorem thm_5_vars_198956185364208281584051197791 : ((p4 → (p3 ∨ ((p5 ∧ p5) ∧ (p2 ∧ p3)))) ∨ ((p4 ∨ (p5 ∧ ((((p3 → p3) ∧ (False ∨ p5)) ∧ ((True → p5) → True)) ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712650036245781880350219425380 : (((((p4 ∧ True) ∧ (p4 ∧ (p3 ∧ p4))) ∨ (p2 ∨ (((p3 → p1) ∧ ((p2 → p3) ∧ (p5 → True))) → (p4 ∨ (p4 → (True ∨ p4)))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206550392704697149852291848130 : ((True → (True ∧ (p2 ∨ (p5 ∧ p3)))) ∨ (p3 → ((p2 ∨ ((((True ∧ (p3 ∧ p1)) → p1) → True) ∧ p1)) ∨ (True ∧ (p5 ∨ (True ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197304725154938919942044584411 : ((((p1 ∨ p3) ∧ ((p5 ∧ p3) → p4)) → False) ∨ (((p2 → p5) → (((True → p1) → (p4 ∨ ((p4 → (True ∧ p3)) ∨ p1))) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695338332892493194900726289580 : (((((p5 ∧ (((p3 ∧ (p3 ∧ (True ∨ False))) → (True ∨ True)) ∨ False)) → p3) → (p3 ∧ ((((p5 ∧ (p3 → p1)) ∨ p2) ∨ p2) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807611675627912650110289341409 : (((p4 → ((p1 ∨ (False ∧ (True ∧ False))) ∨ (p1 ∨ ((((p4 ∨ p2) ∧ p2) ∨ ((p4 → p2) ∨ p5)) ∧ ((p4 ∨ (True ∨ p3)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588181016787502401547401606972 : ((((((False ∧ ((True ∧ (False ∨ ((p5 ∨ p5) ∨ p2))) ∧ p2)) ∨ (True ∨ ((p3 ∧ True) ∨ (p4 ∧ ((p4 → p2) ∧ p3))))) ∨ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165222551789616139718067424667 : (((((p5 ∨ (p5 ∧ p4)) ∧ False) ∧ (p4 ∧ (p3 ∨ ((p2 → p4) ∨ p3)))) ∨ (p1 → p1)) ∨ ((p4 ∧ (p3 ∨ p2)) ∨ ((p5 ∧ p1) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325812173232813590288380073192 : (p5 ∨ (p3 ∨ ((((True → (p5 ∨ ((p2 ∧ False) ∧ False))) ∧ (True ∧ p1)) ∨ (((False ∧ p5) ∨ True) → p2)) ∨ ((p4 ∧ False) → (p1 ∧ p1))))) := by
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
theorem thm_5_vars_666116083176455476953969046865 : (((((p2 ∧ ((((True ∨ p4) ∨ ((p3 ∧ True) ∨ (p5 ∧ (p5 ∧ p1)))) → p3) → (p3 ∧ p3))) ∧ (True → False)) ∧ (p4 → (p1 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190265435581415105956001818190 : ((((((p3 ∨ p4) ∧ (False → p2)) → p1) ∨ p4) ∨ True) ∨ ((((p2 ∨ (p2 ∧ ((p4 ∨ p1) → p4))) ∨ False) → False) ∨ (p1 ∧ (False → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316471266889587089659096138704 : (p3 ∨ (p1 ∨ (p1 ∨ (True → (p2 ∨ ((p1 ∨ (((((p3 ∧ p2) → p5) ∧ ((p4 ∨ p5) ∨ (p4 → p3))) ∨ p1) ∨ (p2 → True))) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259522228531831194618350281580 : ((False → p5) → (((True → p4) → p4) ∧ (((p1 → p3) ∨ ((True ∧ (p3 ∨ (p3 → (p4 ∨ (False ∨ True))))) → ((p4 → False) ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



