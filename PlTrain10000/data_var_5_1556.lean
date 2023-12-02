variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133661637924661401317469792306 : (((((True → p5) ∨ (((p3 ∨ (p3 ∨ p4)) → ((p4 ∨ p4) ∧ (p2 ∨ (p2 ∧ False)))) → p4)) ∨ (p2 → p2)) ∧ p5) ∨ (p4 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755023029141177429220425622316 : (((False ∧ (True → (((True ∧ p5) → p4) ∧ ((p3 ∨ (p2 → (((p2 → p2) → (p5 ∨ p3)) ∧ ((p4 ∨ False) ∧ p1)))) → (p1 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231487993724042693584746619715 : (((p3 → p3) ∨ True) → ((p5 ∨ (p4 → (((((p5 → p4) ∧ (True ∧ (p4 ∧ True))) ∧ p1) → ((p1 → True) ∧ (p4 → p2))) ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_52263411819484695320557481709 : (((p4 ∨ (p2 ∨ (((p5 ∧ False) ∧ p5) → (p2 → ((True ∨ (p5 ∧ p3)) ∧ p2))))) → (p2 ∧ (p4 ∧ (((False ∨ p5) ∧ p2) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115642083010701031965456241055 : ((((p2 → ((p5 ∨ p1) ∧ p2)) ∨ p3) ∨ ((((p3 → p3) ∨ (True ∧ p4)) ∧ (((False ∨ p5) ∨ (p3 ∧ p4)) ∧ p4)) → p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39598412554389259474605792832 : (((p2 ∨ (((p5 ∧ p1) ∧ (((p3 ∨ p5) → False) ∧ ((((p2 ∨ p3) ∨ False) ∧ p2) ∨ ((True ∨ p3) ∨ (p3 → p4))))) → p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159071232124393278945041092941 : ((p5 ∨ (p1 ∨ (p3 ∧ (p1 → (True ∨ (p5 → (((((p2 ∧ p5) ∨ True) → p1) → True) → p1))))))) ∨ (p4 ∨ (p1 ∨ (False ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739004464458476562126890883921 : ((((p3 ∧ p2) ∨ (p1 ∨ (((p2 → False) ∨ (((p3 → ((p4 → (p3 ∧ (p2 → p4))) → (p1 ∧ p1))) ∨ p5) ∨ True)) ∧ (p4 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57031379562083489563269639020 : (((p2 → (p1 ∧ True)) ∧ ((True ∧ ((False ∨ (p3 → (((((p4 ∧ (p4 → p5)) → p2) → p4) ∧ p2) → False))) ∨ (p1 → p5))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190368376365426911310704898219 : ((((p3 ∧ p4) ∨ (False ∨ (p2 ∨ (p2 ∨ p3)))) ∨ True) ∨ (p4 ∨ (((True ∧ (p2 → (p5 ∧ (p2 ∨ p5)))) → (p4 → (p3 ∨ True))) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153615915655780215102742254313 : ((p1 → (((False ∨ (((p2 ∧ (True → (p4 ∨ (p5 ∧ (p1 ∨ p2))))) → p2) ∧ (p1 ∧ p5))) ∨ p3) ∨ True)) → (((p3 → p5) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_992239752609188113830584633961 : (((p4 ∧ ((p4 → (((True ∨ (p3 ∨ p2)) → (True ∧ False)) ∧ p3)) ∧ ((p2 ∨ ((False ∧ False) ∨ True)) ∧ (((p2 → p3) → p3) → p5)))) → p3) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186103667013147966990571989854 : (((((p2 ∧ True) ∧ (p1 ∨ (False → p2))) ∨ (p4 ∨ p3)) ∨ p5) → (((((p4 ∧ p2) ∨ (p3 → (p5 ∨ (True → p3)))) ∨ p3) ∨ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225315414791774564681737393871 : (((False ∨ p4) ∧ p1) ∨ ((p5 ∨ (((((p5 ∨ (True ∧ (p4 ∨ (p5 → p5)))) ∧ p5) → False) ∨ ((p4 ∨ p5) ∧ (p4 ∧ p4))) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184983041777387040772009924708 : (((p4 → (False ∧ p5)) → (p3 ∧ (p1 → ((p5 ∨ p2) → p3)))) ∨ (((p4 → True) ∨ ((p3 → (p3 ∨ p1)) → (p5 ∨ p2))) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656384811853503440477303560985 : (((((p2 → (((p3 ∧ p2) ∧ True) ∧ ((p5 ∧ False) ∨ (True ∧ False)))) → ((True → p2) ∧ ((p3 ∧ p2) ∧ (p4 ∨ True)))) ∨ (p4 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_203969514026119147688120854866 : ((p3 → (((p2 → False) ∨ False) ∨ True)) ∧ (p1 → ((p2 ∨ False) ∨ (p3 ∨ (((True ∨ p4) ∨ (p2 ∨ True)) ∨ ((p3 ∨ (p1 → p1)) → p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184558094525559963704461535507 : (((((p3 → p1) → (p4 → True)) ∨ (False → p1)) → (p4 ∨ p4)) ∨ (True ∨ (p4 → ((((p3 ∧ (False ∧ True)) → p2) ∧ p5) ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299481318354344152131113357083 : (False ∨ ((p1 → ((False ∨ ((p4 → False) ∧ p1)) ∧ ((True ∨ False) → (((p3 ∨ p1) → (p2 ∨ (((p5 ∧ p3) ∨ p5) → p4))) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354748227213848166351252673976 : (p5 → ((((((p2 → (p4 → ((True ∧ p2) ∨ p3))) ∧ p4) ∨ ((p2 ∨ p5) → p4)) ∧ p4) → (((p1 ∧ p2) ∨ (p3 ∧ False)) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243999283462073261019219222066 : ((True ∧ p1) ∨ (p5 → (p5 → (((((False ∧ False) ∨ ((((True ∧ p2) ∨ (False ∨ p5)) ∧ p5) ∧ (p4 ∧ p5))) ∨ p3) → p4) → (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((False ∧ False) ∨ ((((True ∧ p2) ∨ (False ∨ p5)) ∧ p5) ∧ (p4 ∧ p5))) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165672019634466450210502490228 : (((p4 → (((p5 → p1) ∧ p5) ∨ p1)) ∨ ((p1 ∨ p4) ∧ (((False ∧ True) ∨ p2) ∨ p3))) ∨ (p5 → (True ∨ (((p5 → p5) ∧ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64429181817442990513473003286 : ((p1 ∨ (((((p5 ∧ ((p4 ∧ p3) ∨ p5)) ∧ ((p5 ∨ p2) ∧ False)) → p2) → (p4 ∧ (p5 → ((p2 ∧ True) ∨ p5)))) ∧ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4474254953686449621790723046 : (p2 → ((((p3 → (p1 ∧ p1)) ∨ (p2 ∧ True)) ∧ p1) → ((((p4 → (((p3 ∧ p2) → False) → (p4 → p1))) ∨ p4) → p3) → p3))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 → (((p3 ∧ p2) → False) → (p4 → p1))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : ((p4 → (((p3 ∧ p2) → False) → (p4 → p1))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h15
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599194228797162277034971816818 : (((((p3 → p5) ∧ ((((p1 → ((p1 ∨ True) ∧ (p2 ∨ p2))) ∨ ((((p1 ∨ False) ∧ True) ∨ (p1 → False)) ∨ False)) ∨ p5) ∨ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231431700787255796895905687409 : (((p2 → False) ∨ True) → (((p3 ∨ ((p4 → (((p1 ∨ ((p1 → p3) ∨ p3)) → (p2 ∨ p3)) → (p5 → p4))) → (False ∧ True))) ∧ False) ∨ True)) := by
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
theorem thm_5_vars_609092816398588757259022993358 : ((((((p5 ∨ ((p1 ∧ True) ∨ (p4 ∧ p5))) ∧ (p4 → (((p3 ∧ (p4 ∨ (p5 ∨ (True ∧ True)))) ∧ (False ∨ True)) → p2))) ∨ False) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_149120346318856065091750199751 : (((p1 ∧ True) ∧ (((True → (p1 ∨ (p1 ∨ True))) ∨ p5) → ((p2 → ((False ∧ (False ∧ p4)) → p3)) → False))) ∨ (False → (p2 ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198980563524005683629844776020 : ((p5 → ((p3 ∨ (p4 ∨ p2)) → (False ∨ p2))) ∨ (False → (True ∧ ((p5 → (p3 ∧ False)) → (((False ∨ ((p3 → p1) → p3)) ∧ p4) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709583330142849002616180512709 : ((((p1 ∨ (((False → p4) ∨ (p4 ∨ p2)) ∨ False)) → ((p5 → (((False ∨ (True ∧ (p4 ∧ (p5 → p5)))) ∧ p5) → (p4 → p1))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245676365847865258469086977591 : ((p3 ∧ p1) ∨ (((p1 ∧ p1) ∧ p3) ∨ ((p1 ∨ ((True ∧ (p2 ∧ ((False ∧ p3) ∧ p2))) → p3)) ∧ (((True ∨ p5) → (p5 → p5)) ∨ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172896198084620941400895299132 : ((p2 ∧ (((True → (p4 ∨ False)) ∨ ((p4 → (False ∧ False)) ∨ (p1 ∧ p3))) ∧ True)) ∨ ((True ∧ p2) ∨ (p4 → (p2 → (p2 ∨ (p3 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264540757087389456174371687532 : (True ∧ (((False → True) ∧ p3) ∨ (((p2 ∨ ((p3 ∨ (p4 → p3)) ∨ p5)) ∨ (((False ∧ (p3 ∧ p5)) ∧ False) ∨ ((True → True) ∨ False))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238078926507563363477604237598 : ((True ∨ p2) ∧ ((p1 ∨ ((((p1 ∨ (True → False)) → p2) → p2) ∨ p2)) ∨ (p2 → ((((p3 ∨ p1) → (True ∨ (p3 → p2))) ∧ True) → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178365841383052614411787144727 : ((((((False → ((p4 → p3) ∨ True)) ∨ True) ∨ True) ∧ True) → (p3 → p4)) ∨ ((True ∨ (True ∧ (p5 → p4))) ∨ ((p2 → (p1 ∨ True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350188179971548830032195400289 : (p4 → (((True ∧ (p5 ∧ (p5 ∨ True))) → ((((p4 ∧ ((p4 ∧ (p3 ∨ p2)) → (p5 ∧ (p4 ∧ p3)))) → p3) ∨ p3) ∧ (p4 → p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708345963158272532694557871369 : ((((((True ∧ ((p5 ∧ True) ∧ p2)) → p4) ∧ p2) → (p3 ∧ (p1 → (((((p3 → p1) ∨ p5) → False) ∨ ((p1 → p2) ∨ False)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171787840974430356309856033858 : ((((p1 → ((p5 → p4) ∧ (((p2 → p1) ∨ p1) ∨ True))) ∨ (p4 ∨ p3)) → p3) ∨ ((p1 ∨ (p1 ∨ False)) ∨ (((True ∨ p5) ∧ False) → p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74895252400450504900831771141 : (((p1 ∨ ((((True ∨ p4) ∧ ((((True ∧ p1) → (p1 ∧ (False ∨ (p4 ∧ True)))) ∧ p2) ∧ p2)) → (p5 ∨ (p5 ∨ True))) → False)) ∨ p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (((True ∨ p4) ∧ ((((True ∧ p1) → (p1 ∧ (False ∨ (p4 ∧ True)))) ∧ p2) ∧ p2)) → (p5 ∨ (p5 ∨ True))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h8.left
          let h11 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h8.left
          let h16 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h5
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216077694753416631554356769160 : ((True → ((p1 ∧ p1) ∧ p2)) ∨ (((p3 → p3) ∨ p4) → (((p5 ∨ False) ∧ (p5 → p2)) ∨ ((((p3 ∧ p3) → (False → p4)) ∧ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233302962441996970872642481926 : ((True ∨ (p3 ∨ p4)) → ((p1 ∨ (((True ∧ p3) ∨ p4) → p5)) → (((p1 → p5) ∧ ((True ∧ False) ∧ p1)) ∨ (p5 → ((p5 ∨ False) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260342108042813968666588487845 : ((p2 → p5) → (((False ∧ ((((False ∧ ((((True → False) ∨ False) → (p4 → True)) ∨ p3)) ∧ (True ∨ p3)) ∧ (p4 → p1)) ∨ p5)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209303763656633230993125642031 : ((True → (True ∨ (False ∨ (False ∨ p2)))) → (((p4 ∨ p5) → ((((p2 → p4) ∧ p1) → (p1 → False)) → p3)) ∨ (p5 → (True ∨ (p2 ∨ p1))))) := by
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
theorem thm_5_vars_357290260795564780826248417675 : (p5 → ((False ∨ False) ∨ ((((((p5 → True) → p2) ∧ (p2 → p1)) → p1) ∧ (True → (True ∧ (p3 ∨ p1)))) → (((p3 ∧ p5) ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_177239141946341903298881088833 : ((True ∨ (False ∨ (p5 → ((p1 ∨ ((p1 → (p3 ∧ p5)) ∧ p5)) → p2)))) ∧ ((p2 ∨ (p5 ∧ (p5 → True))) → ((True → False) → (False ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32634562272191639081839510497 : ((p2 ∨ ((False ∧ (p1 ∨ True)) ∨ ((((p3 ∧ True) ∧ False) ∨ (((((False ∨ (False → p1)) ∧ p3) → False) → True) ∨ (p4 → p1))) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50196645598239228610599200123 : ((((p5 ∨ ((False ∧ ((p5 ∧ False) ∨ (p4 ∧ p2))) → (p1 → (p5 ∨ ((True ∨ p1) → False))))) ∧ p3) ∨ (p4 ∨ (p2 ∧ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319167496933776286880983964576 : (p4 ∨ (((True ∨ ((p2 ∨ p1) ∧ (p3 → (p2 → (True ∨ ((p5 ∨ p2) ∧ True)))))) → (p4 ∧ p3)) ∨ ((p5 ∨ True) → (False → (False ∧ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164864629932037673043559912458 : (((p3 ∨ ((False ∧ (((True → p3) → p3) ∧ p1)) ∧ (p5 ∨ ((p3 ∨ p1) → p2)))) ∨ p5) ∨ (p2 ∨ (((p3 ∧ (p3 ∨ p2)) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133568608547926705090535802498 : (((((((p5 ∧ (((p1 ∨ False) → p3) ∨ p3)) ∨ ((True ∨ (False → p3)) ∧ p4)) ∨ p5) → (p4 ∨ p3)) ∨ p3) ∧ True) ∨ (p3 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339501513266671254377556942866 : (p1 → (False ∨ ((True ∧ (((p4 → p2) ∧ (False → p1)) ∨ (p5 → ((p3 ∧ p1) → (p4 ∨ p5))))) → ((p5 ∨ (p3 ∧ p4)) ∨ (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719772596742954683233372352229 : ((((p1 → (p5 ∨ (p4 ∨ False))) ∨ (p2 → (((p4 ∧ (False ∧ False)) ∨ True) ∧ ((((True → False) → (False ∧ (p2 ∧ p3))) ∨ p2) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117785849166793629372941357289 : ((p4 ∧ (((p3 → (True ∧ ((False → False) → p1))) ∧ (False ∧ (p1 ∨ (False ∨ False)))) ∧ ((p5 ∨ False) ∨ ((p3 → p1) → p1)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357523786207365644463387949612 : (p5 → (True ∧ ((p1 → True) → (((p4 → (((p4 ∧ (p3 ∨ (p4 → ((p1 → True) ∧ p5)))) → p3) ∨ False)) ∨ (p1 ∨ p3)) ∨ (p3 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135741236078619200790459418713 : ((((p5 ∧ (True → (p4 ∧ (p1 ∧ (p5 ∨ p5))))) ∨ ((False → p4) ∧ False)) ∨ ((p2 ∨ p3) ∨ (True ∨ (p2 → p1)))) ∨ (p5 ∧ (p1 ∧ True))) := by
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
theorem thm_5_vars_614383058256602928837961426359 : (((((True ∨ (p2 → ((((False ∨ p2) → True) ∧ (False ∨ (((p2 → (False ∧ p3)) → False) → p4))) ∨ True))) → (p4 ∧ (p4 ∧ True))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714075702449393276081391866179 : ((((((p3 ∨ False) ∧ (p3 → p4)) → p5) → ((((p5 ∨ p5) ∧ (True ∨ (p2 ∨ (True → p4)))) → False) ∨ ((True ∨ (p5 → p5)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147089533683843234357752417395 : (((((p3 ∨ p5) ∨ (p5 ∨ p2)) → (p2 ∨ (p3 → ((p3 ∨ ((p4 ∨ (p1 → True)) ∧ p1)) ∨ p5)))) ∧ p1) ∨ (p5 → ((p1 ∨ p5) ∨ p2))) := by
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
theorem thm_5_vars_686242806409761721634363783479 : ((((((((True ∧ p3) → (p1 ∨ p1)) ∨ p2) → p2) ∧ (p2 ∧ (((p5 → p3) ∨ p4) ∨ True))) → (p3 → (((p3 ∧ True) ∧ p1) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186561243652579510318056009420 : (((p2 ∧ (p1 → ((False ∧ p3) → (p1 → True)))) ∨ (p5 ∨ p2)) → ((((((p3 ∧ p1) ∧ p3) → p1) → False) → (p3 ∧ (p3 ∨ True))) ∨ p2)) := by
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
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (((p3 ∧ p1) ∧ p3) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h8
      -- False on the left can always be used.
      apply False.elim h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183909791257338922426820511200 : ((((p2 → p1) → (False ∨ ((p1 → p2) ∨ (p3 ∨ p5)))) ∧ True) ∨ ((p2 ∧ (p3 ∧ (False ∧ (p5 → (p5 → False))))) → ((False → p1) ∨ p4))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777343297477281842971929165397 : (((p1 ∨ ((((p5 ∧ True) → p5) ∧ ((True ∧ (p3 ∨ ((p1 → (p2 ∧ p1)) ∧ p3))) ∨ (p2 → p4))) ∨ (((p4 ∨ False) → p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37462486950987258780445818230 : (((((((((p1 ∧ p3) → True) ∨ False) ∨ False) ∧ p4) ∧ ((p5 ∨ (((p2 ∧ p2) ∨ (p2 → True)) ∨ p1)) ∨ (False → p1))) ∨ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54422904709586022159959530543 : ((((((True ∧ (p5 ∨ False)) ∨ p2) → False) ∨ p5) ∨ (((((True ∨ (p5 ∧ p3)) ∨ (p5 ∧ p4)) ∨ p4) ∨ p2) → ((False ∨ True) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
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
theorem thm_5_vars_308525176944390396884411568914 : (p2 ∨ (((((((p3 → p1) ∧ (p5 ∨ True)) ∧ p4) → ((p2 → p3) ∧ p1)) → p5) ∨ (((p2 ∨ (p5 ∧ p2)) → (p4 → p4)) ∨ p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41390567748141307659140325827 : ((((((p5 ∧ ((p3 ∧ p3) → p1)) ∨ p5) → ((True → p5) ∨ (False ∨ False))) ∧ (((p3 ∧ p3) ∨ p4) ∨ ((p2 ∨ p5) ∨ p3))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137687756133483584626255498029 : ((p1 ∨ ((p4 ∨ (((((p3 ∨ False) → p2) ∨ False) ∨ (p3 → (True → p4))) → ((p2 → p4) → (p1 ∧ p2)))) ∨ p4)) ∨ (False ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256119913492049899271836288154 : ((True ∨ p5) → (((p2 ∧ (p5 → p3)) → False) ∨ (((p2 ∧ ((p3 → (((p2 → (p4 → p2)) ∧ (p2 → p3)) ∧ p1)) → p5)) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685189309947722357772049395123 : ((((p5 ∨ (((((True ∧ p3) ∧ (p2 ∨ ((p4 ∨ (True → p2)) ∧ True))) → p2) ∨ False) → p3)) ∨ ((p4 ∨ True) ∨ ((p3 ∨ p3) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731481098725124762423392063780 : ((((True → (False → p1)) → (((((p5 ∧ (p5 ∧ p4)) → False) ∨ ((True → True) ∨ ((p2 ∧ (False ∨ p5)) ∧ False))) ∨ False) ∧ (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319115388656293519348931571363 : (p4 ∨ ((p4 → ((False ∨ (False ∨ (True → (p1 → True)))) → (((False ∨ ((p2 → p3) → p2)) ∧ True) → True))) → (p3 ∨ ((p2 → True) → True)))) := by
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
theorem thm_5_vars_46952903790097443779615223304 : ((((p4 → (p3 ∨ ((p3 ∧ (((p1 ∧ (p5 ∧ (False ∨ (p5 ∨ p2)))) → (p5 ∨ (True ∨ p3))) ∧ False)) ∧ p1))) ∨ p1) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178233588449632102557210557327 : (((p4 → (((((False ∧ p3) ∧ (True → p5)) ∧ p2) ∨ p5) → p4)) → p5) ∨ ((p1 ∨ True) ∨ (p2 → ((p1 ∨ (False → (False ∧ p5))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199765528138669954338782465763 : (((p1 → (p5 ∧ ((True → p5) → False))) → p2) → ((((p1 ∧ p3) ∨ p1) → p5) → (p4 ∨ ((False ∨ ((p4 → p4) → (p5 → p5))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160767269151550205358039966567 : ((((p2 ∧ (False ∧ p4)) → (p1 → True)) ∧ (((True → (False ∧ ((False → p2) ∨ True))) → p1) → False)) → ((p3 ∨ p1) → (False ∧ (p1 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True → (False ∧ ((False → p2) ∨ True))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h6
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : ((True → (False ∧ ((False → p2) ∨ True))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h15
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : ((True → (False ∧ ((False → p2) ∨ True))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h26 := h20 h21
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h1.left
    let h29 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587974154940443477489604303948 : (((((((((p2 ∨ (True ∧ False)) ∨ p1) → (True ∧ ((p5 ∧ (p1 → p3)) ∧ p3))) ∨ (p2 → p3)) → ((p4 ∨ p4) ∨ p4)) ∨ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783764581369586713652736475243 : (((p3 ∨ (((p4 → p5) ∧ (False ∨ p2)) ∧ ((((p5 ∧ p2) ∧ ((((True → p1) ∨ p5) ∨ p5) ∧ p4)) ∨ True) ∨ ((p1 ∨ p3) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114317181029409253326783908227 : ((((True ∨ (p1 ∨ p1)) ∧ (p4 → (((p1 → p3) ∨ p2) → (False ∧ ((p3 → p5) ∧ p1))))) ∧ ((False ∧ p2) → (p2 ∨ p4))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346319552874493655744478388204 : (p3 → ((((((False ∧ p1) ∧ (p5 ∨ (p4 → ((True ∨ p1) → (((True → p3) ∧ p5) → p3))))) → p3) ∨ False) → (p1 ∨ p1)) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686206698381315021749486529217 : (((((False ∧ (False → (p4 ∨ (False ∨ (p4 → (False → False)))))) ∨ (((p1 ∨ p1) ∨ p3) → p5)) → ((p3 → (p3 ∨ (p1 ∨ p3))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46989076362629893794113392490 : (((((p2 → (((((p1 ∨ True) ∧ p4) ∧ False) ∨ False) → (False ∨ p4))) ∧ (p3 → ((False → (False → True)) ∧ p4))) → p1) ∨ (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305350954449390593303044591951 : (p1 ∨ ((p3 ∧ (p4 ∧ (((p3 → (False ∧ p5)) → p3) ∨ ((p2 ∧ (p1 → (True ∧ True))) ∨ p4)))) → (False ∨ ((p2 ∧ False) ∨ (p4 → p4))))) := by
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215612764609108095973676029991 : ((p5 ∧ (p5 → (p2 ∨ p1))) ∨ ((p1 ∧ (False ∨ p4)) → ((p2 ∨ (((p1 ∧ p1) → p5) → False)) ∨ (False ∨ ((p3 ∧ (False ∧ p3)) ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51477808526401967811493240667 : ((((((False → p4) ∨ (True → True)) → p4) ∧ ((((p1 ∧ p2) ∨ True) → (p2 ∧ p3)) → p2)) → (((True ∧ p4) ∧ (p4 ∨ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53229197622276638293856904918 : ((((((True ∧ p3) ∨ p4) ∨ p3) → ((False ∨ p3) ∧ (p4 ∨ p5))) ∨ (p1 ∨ (((((p3 ∨ False) ∧ p4) → p3) ∨ True) → (p4 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171589033027323237888511751789 : (((((((False ∨ True) ∨ p3) → (False ∨ True)) ∧ p4) ∨ (p3 → (p4 ∨ p5))) ∨ True) ∨ (p4 ∨ (p5 ∨ ((False ∨ (p1 → True)) ∨ (p4 ∨ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254996192557008185913149648413 : ((p4 ∧ p1) → ((p2 ∨ ((p5 → (True → ((((p4 ∨ p1) ∧ p2) ∨ (p5 → p5)) ∧ (p4 ∧ (p4 ∨ True))))) → ((p3 → False) ∨ True))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693463566870182546509904002415 : (((((((False ∨ (p5 → ((p3 → (True → p3)) ∨ p4))) → p2) ∧ False) ∧ p5) ∨ (p5 ∨ (False → ((((p1 → False) ∨ False) → p5) → p2)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39063389137053469897668025317 : ((((p5 ∧ False) ∨ ((p2 ∨ (((p5 ∨ ((p2 ∨ (False ∨ False)) → (p3 → p3))) → ((p5 ∧ p2) → p4)) ∨ (p5 → p5))) ∧ True)) ∧ True) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52339651769044349896977738794 : (((((False ∧ (((p4 ∧ True) ∨ (p5 ∧ p1)) ∨ p3)) → (p1 → True)) → p4) ∧ (p3 ∧ (((p1 → (p2 ∨ p1)) → p5) → (False ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340012757618374488859020230344 : (p1 → (p1 → (p3 ∨ ((((True ∨ (True ∧ (p2 ∧ (p1 ∧ p5)))) ∨ p1) ∧ (((p3 ∨ ((False ∨ True) ∨ False)) ∨ p1) ∧ True)) → (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- False on the left can always be used.
              apply False.elim h14
            case inr h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h5.left
      let h26 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h31 =>
              -- False on the left can always be used.
              apply False.elim h31
            case inr h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h5.left
    let h37 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- False on the left can always be used.
            apply False.elim h42
          case inr h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h44 =>
          -- False on the left can always be used.
          apply False.elim h44
    case inr h45 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54696698488243794182664440760 : ((((((p3 ∨ True) ∨ False) → p2) ∧ (p5 ∧ p5)) → (((p4 ∧ (p1 ∧ ((p1 → ((p3 ∨ p2) ∨ False)) ∧ (p4 ∧ p3)))) ∨ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322496791377164051121889406929 : (p5 ∨ (((False ∨ p2) → ((((True ∨ p4) ∨ (True ∨ (False ∨ ((True ∧ (False ∧ (p5 ∧ True))) ∨ (True ∨ False))))) ∧ (p1 → False)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265695110723546987719309061572 : (True ∧ (p3 ∨ ((((((p5 ∨ True) ∧ (p3 ∨ p5)) ∧ ((p4 ∧ (p3 ∧ ((False ∧ p3) → p4))) ∧ False)) ∧ p4) ∨ (False ∨ (p1 ∨ True))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201040236399290475376204119880 : ((p4 ∨ ((True ∧ True) → ((False ∧ p1) ∧ p2))) → (p5 → ((((p2 ∧ p2) → p1) ∧ p1) → (((p2 ∧ ((p5 ∧ p3) → p1)) ∨ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888496019647307496742553926375 : (((((False ∧ ((p1 ∧ True) ∨ (False ∧ (((p4 ∨ p1) ∧ (False → p5)) → p4)))) ∨ ((True ∧ False) ∨ (True ∧ (True ∨ p2)))) → (False ∧ True)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p1 ∧ True) ∨ (False ∧ (((p4 ∨ p1) ∧ (False → p5)) → p4)))) ∨ ((True ∧ False) ∨ (True ∧ (True ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48827383805136806736034605458 : (((p5 ∧ (p4 ∧ (p5 ∨ (((p5 ∧ (p2 → p5)) ∨ True) ∧ (p4 ∨ ((((True ∨ p4) ∧ False) ∧ p1) → p1)))))) ∧ ((False ∨ p3) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133772605207200908301416322843 : ((((((p4 ∨ False) ∨ p3) ∧ False) ∨ (p5 ∨ (((p3 → (p1 → ((p2 ∧ True) → True))) → (p2 → True)) → p4))) ∧ p4) ∨ (p1 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67685113027285716060022975913 : ((p1 → (p2 → (((((p3 ∨ (p1 ∧ (p4 ∨ p1))) ∨ p3) ∨ (p4 ∨ p4)) → ((p1 ∨ ((p4 ∧ p5) → (False → p4))) → False)) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149401313855178031746549987541 : ((True ∧ ((((False ∨ (((((p4 ∧ ((p3 ∧ p1) → p4)) → p2) → p4) ∧ p5) ∧ p5)) → p3) → p2) → p3)) ∨ (((p4 ∧ p2) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



